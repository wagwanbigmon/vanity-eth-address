/*
    Copyright (C) 2023 MrSpike63

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as published by
    the Free Software Foundation, version 3.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

#if defined(_WIN64)
#define WIN32_NO_STATUS
#include <windows.h>
#undef WIN32_NO_STATUS
#endif

#include <thread>
#include <cinttypes>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <queue>
#include <chrono>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>

#include "secure_rand.h"
#include "structures.h"

#include "cpu_curve_math.h"
#include "cpu_keccak.h"
#include "cpu_math.h"


#define OUTPUT_BUFFER_SIZE 10000

#define BLOCK_SIZE 256U
#define THREAD_WORK (1U << 8)

// Maximum prefix/suffix length
#define MAX_PREFIX_LENGTH 20
#define MAX_SUFFIX_LENGTH 20

__constant__ CurvePoint thread_offsets[BLOCK_SIZE];
__constant__ CurvePoint addends[THREAD_WORK - 1];
__device__ uint64_t device_memory[2 + OUTPUT_BUFFER_SIZE * 3];

// Add constant memory for prefix/suffix patterns
__constant__ uint32_t target_prefix[MAX_PREFIX_LENGTH];
__constant__ uint32_t target_suffix[MAX_SUFFIX_LENGTH];
__constant__ int prefix_length;
__constant__ int suffix_length;

__device__ int count_zero_bytes(uint32_t x) {
    int n = 0;
    n += ((x & 0xFF) == 0);
    n += ((x & 0xFF00) == 0);
    n += ((x & 0xFF0000) == 0);
    n += ((x & 0xFF000000) == 0);
    return n;
}

__device__ int score_zero_bytes(Address a) {
    int n = 0;
    n += count_zero_bytes(a.a);
    n += count_zero_bytes(a.b);
    n += count_zero_bytes(a.c);
    n += count_zero_bytes(a.d);
    n += count_zero_bytes(a.e);
    return n;
}

__device__ int score_leading_zeros(Address a) {
    int n = __clz(a.a);
    if (n == 32) {
        n += __clz(a.b);

        if (n == 64) {
            n += __clz(a.c);

            if (n == 96) {
                n += __clz(a.d);

                if (n == 128) {
                    n += __clz(a.e);
                }
            }
        }
    }

    return n >> 3;
}

// Convert hex character to nibble value
__device__ uint8_t hex_to_nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 0;
}

// Convert address to hex string for pattern matching
__device__ void address_to_hex_string(Address a, char* hex_str) {
    uint32_t words[5] = { a.a, a.b, a.c, a.d, a.e };

    for (int i = 0; i < 5; i++) {
        for (int j = 0; j < 8; j++) {
            uint8_t nibble = (words[i] >> (28 - j * 4)) & 0xF;
            hex_str[i * 8 + j] = (nibble < 10) ? ('0' + nibble) : ('a' + nibble - 10);
        }
    }
    hex_str[40] = '\0';
}

// Check if address has target prefix
__device__ bool has_prefix(Address a) {
    if (prefix_length == 0) return true;

    char hex_str[41];
    address_to_hex_string(a, hex_str);

    for (int i = 0; i < prefix_length; i++) {
        uint8_t addr_nibble = hex_to_nibble(hex_str[i]);
        uint8_t target_nibble = target_prefix[i];
        if (addr_nibble != target_nibble) {
            return false;
        }
    }
    return true;
}

// Check if address has target suffix
__device__ bool has_suffix(Address a) {
    if (suffix_length == 0) return true;

    char hex_str[41];
    address_to_hex_string(a, hex_str);

    for (int i = 0; i < suffix_length; i++) {
        uint8_t addr_nibble = hex_to_nibble(hex_str[40 - suffix_length + i]);
        uint8_t target_nibble = target_suffix[i];
        if (addr_nibble != target_nibble) {
            return false;
        }
    }
    return true;
}

// Score prefix match (how many characters match from the beginning)
__device__ int score_prefix(Address a) {
    if (prefix_length == 0) return 0;

    char hex_str[41];
    address_to_hex_string(a, hex_str);

    int score = 0;
    for (int i = 0; i < prefix_length; i++) {
        uint8_t addr_nibble = hex_to_nibble(hex_str[i]);
        uint8_t target_nibble = target_prefix[i];
        if (addr_nibble == target_nibble) {
            score++;
        }
        else {
            break;
        }
    }
    return score;
}

// Score suffix match (how many characters match from the end)
__device__ int score_suffix(Address a) {
    if (suffix_length == 0) return 0;

    char hex_str[41];
    address_to_hex_string(a, hex_str);

    int score = 0;
    for (int i = suffix_length - 1; i >= 0; i--) {
        uint8_t addr_nibble = hex_to_nibble(hex_str[40 - suffix_length + i]);
        uint8_t target_nibble = target_suffix[i];
        if (addr_nibble == target_nibble) {
            score++;
        }
        else {
            break;
        }
    }
    return score;
}

#ifdef __linux__
#define atomicMax_ul(a, b) atomicMax((unsigned long long*)(a), (unsigned long long)(b))
#define atomicAdd_ul(a, b) atomicAdd((unsigned long long*)(a), (unsigned long long)(b))
#else
#define atomicMax_ul(a, b) atomicMax(a, b)
#define atomicAdd_ul(a, b) atomicAdd(a, b)
#endif

__device__ void handle_output(int score_method, Address a, uint64_t key, bool inv) {
    int score = 0;
    bool is_match = false;

    switch (score_method) {
    case 0: // leading zeros
        score = score_leading_zeros(a);
        break;
    case 1: // zeros anywhere
        score = score_zero_bytes(a);
        break;
    case 2: // prefix match (exact)
        is_match = has_prefix(a);
        score = is_match ? prefix_length : 0;
        break;
    case 3: // suffix match (exact)
        is_match = has_suffix(a);
        score = is_match ? suffix_length : 0;
        break;
    case 4: // prefix and suffix match (exact)
        is_match = has_prefix(a) && has_suffix(a);
        score = is_match ? (prefix_length + suffix_length) : 0;
        break;
    case 5: // partial prefix match
        score = score_prefix(a);
        break;
    case 6: // partial suffix match
        score = score_suffix(a);
        break;
    case 7: // partial prefix + suffix match
        score = score_prefix(a) + score_suffix(a);
        break;
    }

    if ((score_method >= 2 && score_method <= 4 && is_match) ||
        (score_method >= 5 && score >= device_memory[1]) ||
        (score_method <= 1 && score >= device_memory[1])) {

        atomicMax_ul(&device_memory[1], score);
        if (score >= device_memory[1]) {
            uint32_t idx = atomicAdd_ul(&device_memory[0], 1);
            if (idx < OUTPUT_BUFFER_SIZE) {
                device_memory[2 + idx] = key;
                device_memory[OUTPUT_BUFFER_SIZE + 2 + idx] = score;
                device_memory[OUTPUT_BUFFER_SIZE * 2 + 2 + idx] = inv;
            }
        }
    }
}

__device__ void handle_output2(int score_method, Address a, uint64_t key) {
    int score = 0;
    bool is_match = false;

    switch (score_method) {
    case 0: // leading zeros
        score = score_leading_zeros(a);
        break;
    case 1: // zeros anywhere
        score = score_zero_bytes(a);
        break;
    case 2: // prefix match (exact)
        is_match = has_prefix(a);
        score = is_match ? prefix_length : 0;
        break;
    case 3: // suffix match (exact)
        is_match = has_suffix(a);
        score = is_match ? suffix_length : 0;
        break;
    case 4: // prefix and suffix match (exact)
        is_match = has_prefix(a) && has_suffix(a);
        score = is_match ? (prefix_length + suffix_length) : 0;
        break;
    case 5: // partial prefix match
        score = score_prefix(a);
        break;
    case 6: // partial suffix match
        score = score_suffix(a);
        break;
    case 7: // partial prefix + suffix match
        score = score_prefix(a) + score_suffix(a);
        break;
    }

    if ((score_method >= 2 && score_method <= 4 && is_match) ||
        (score_method >= 5 && score >= device_memory[1]) ||
        (score_method <= 1 && score >= device_memory[1])) {

        atomicMax_ul(&device_memory[1], score);
        if (score >= device_memory[1]) {
            uint32_t idx = atomicAdd_ul(&device_memory[0], 1);
            if (idx < OUTPUT_BUFFER_SIZE) {
                device_memory[2 + idx] = key;
                device_memory[OUTPUT_BUFFER_SIZE + 2 + idx] = score;
            }
        }
    }
}

#include "address.h"
#include "contract_address.h"
#include "contract_address2.h"
#include "contract_address3.h"


int global_max_score = 0;
std::mutex global_max_score_mutex;
uint32_t GRID_SIZE = 1U << 15;

struct Message {
    uint64_t time;

    int status;
    int device_index;
    cudaError_t error;

    double speed;
    int results_count;
    _uint256* results;
    int* scores;
};

std::queue<Message> message_queue;
std::mutex message_queue_mutex;

// Helper function to convert hex string to nibbles
std::vector<uint32_t> hex_string_to_nibbles(const std::string& hex_str) {
    std::vector<uint32_t> nibbles;
    for (char c : hex_str) {
        if (c >= '0' && c <= '9') {
            nibbles.push_back(c - '0');
        }
        else if (c >= 'a' && c <= 'f') {
            nibbles.push_back(c - 'a' + 10);
        }
        else if (c >= 'A' && c <= 'F') {
            nibbles.push_back(c - 'A' + 10);
        }
        else {
            throw std::invalid_argument("Invalid hex character in pattern");
        }
    }
    return nibbles;
}

#define gpu_assert(call) { \
    cudaError_t e = call; \
    if (e != cudaSuccess) { \
        message_queue_mutex.lock(); \
        message_queue.push(Message{milliseconds(), 1, device_index, e}); \
        message_queue_mutex.unlock(); \
        if (thread_offsets_host != 0) { cudaFreeHost(thread_offsets_host); } \
        if (device_memory_host != 0) { cudaFreeHost(device_memory_host); } \
        cudaDeviceReset(); \
        return; \
    } \
}

uint64_t milliseconds() {
    return (std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch())).count();
}


void host_thread(int device, int device_index, int score_method, int mode, Address origin_address, Address deployer_address, _uint256 bytecode) {
    uint64_t GRID_WORK = ((uint64_t)BLOCK_SIZE * (uint64_t)GRID_SIZE * (uint64_t)THREAD_WORK);

    CurvePoint* block_offsets = 0;
    CurvePoint* offsets = 0;
    CurvePoint* thread_offsets_host = 0;

    uint64_t* device_memory_host = 0;
    uint64_t* max_score_host;
    uint64_t* output_counter_host;
    uint64_t* output_buffer_host;
    uint64_t* output_buffer2_host;
    uint64_t* output_buffer3_host;

    gpu_assert(cudaSetDevice(device));

    gpu_assert(cudaHostAlloc(&device_memory_host, (2 + OUTPUT_BUFFER_SIZE * 3) * sizeof(uint64_t), cudaHostAllocDefault))
        output_counter_host = device_memory_host;
    max_score_host = device_memory_host + 1;
    output_buffer_host = max_score_host + 1;
    output_buffer2_host = output_buffer_host + OUTPUT_BUFFER_SIZE;
    output_buffer3_host = output_buffer2_host + OUTPUT_BUFFER_SIZE;

    output_counter_host[0] = 0;
    max_score_host[0] = (score_method >= 2 && score_method <= 4) ? 1 : 2; // For exact matches, we want score >= 1
    gpu_assert(cudaMemcpyToSymbol(device_memory, device_memory_host, 2 * sizeof(uint64_t)));
    gpu_assert(cudaDeviceSynchronize())


        if (mode == 0 || mode == 1) {
            gpu_assert(cudaMalloc(&block_offsets, GRID_SIZE * sizeof(CurvePoint)))
                gpu_assert(cudaMalloc(&offsets, (uint64_t)GRID_SIZE * BLOCK_SIZE * sizeof(CurvePoint)))
                thread_offsets_host = new CurvePoint[BLOCK_SIZE];
            gpu_assert(cudaHostAlloc(&thread_offsets_host, BLOCK_SIZE * sizeof(CurvePoint), cudaHostAllocWriteCombined))
        }

    _uint256 max_key;
    if (mode == 0 || mode == 1) {
        _uint256 GRID_WORK = cpu_mul_256_mod_p(cpu_mul_256_mod_p(_uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK }, _uint256{ 0, 0, 0, 0, 0, 0, 0, BLOCK_SIZE }), _uint256{ 0, 0, 0, 0, 0, 0, 0, GRID_SIZE });
        max_key = _uint256{ 0x7FFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x5D576E73, 0x57A4501D, 0xDFE92F46, 0x681B20A0 };
        max_key = cpu_sub_256(max_key, GRID_WORK);
        max_key = cpu_sub_256(max_key, _uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK });
        max_key = cpu_add_256(max_key, _uint256{ 0, 0, 0, 0, 0, 0, 0, 2 });
    }
    else if (mode == 2 || mode == 3) {
        max_key = _uint256{ 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF };
    }

    _uint256 base_random_key{ 0, 0, 0, 0, 0, 0, 0, 0 };
    _uint256 random_key_increment{ 0, 0, 0, 0, 0, 0, 0, 0 };
    int status;
    if (mode == 0 || mode == 1) {
        status = generate_secure_random_key(base_random_key, max_key, 255);
        random_key_increment = cpu_mul_256_mod_p(cpu_mul_256_mod_p(uint32_to_uint256(BLOCK_SIZE), uint32_to_uint256(GRID_SIZE)), uint32_to_uint256(THREAD_WORK));
    }
    else if (mode == 2 || mode == 3) {
        status = generate_secure_random_key(base_random_key, max_key, 256);
        random_key_increment = cpu_mul_256_mod_p(cpu_mul_256_mod_p(uint32_to_uint256(BLOCK_SIZE), uint32_to_uint256(GRID_SIZE)), uint32_to_uint256(THREAD_WORK));
        base_random_key.h &= ~(THREAD_WORK - 1);
    }

    if (status) {
        message_queue_mutex.lock();
        message_queue.push(Message{ milliseconds(), 10 + status });
        message_queue_mutex.unlock();
        return;
    }
    _uint256 random_key = base_random_key;

    if (mode == 0 || mode == 1) {
        CurvePoint* addends_host = new CurvePoint[THREAD_WORK - 1];
        CurvePoint p = G;
        for (int i = 0; i < THREAD_WORK - 1; i++) {
            addends_host[i] = p;
            p = cpu_point_add(p, G);
        }
        gpu_assert(cudaMemcpyToSymbol(addends, addends_host, (THREAD_WORK - 1) * sizeof(CurvePoint)))
            delete[] addends_host;

        CurvePoint* block_offsets_host = new CurvePoint[GRID_SIZE];
        CurvePoint block_offset = cpu_point_multiply(G, _uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK * BLOCK_SIZE });
        p = G;
        for (int i = 0; i < GRID_SIZE; i++) {
            block_offsets_host[i] = p;
            p = cpu_point_add(p, block_offset);
        }
        gpu_assert(cudaMemcpy(block_offsets, block_offsets_host, GRID_SIZE * sizeof(CurvePoint), cudaMemcpyHostToDevice))
            delete[] block_offsets_host;
    }

    if (mode == 0 || mode == 1) {
        cudaStream_t streams[2];
        gpu_assert(cudaStreamCreate(&streams[0]))
            gpu_assert(cudaStreamCreate(&streams[1]))

            _uint256 previous_random_key = random_key;
        bool first_iteration = true;
        uint64_t start_time;
        uint64_t end_time;
        double elapsed;

        while (true) {
            if (!first_iteration) {
                if (mode == 0) {
                    gpu_address_work << <GRID_SIZE, BLOCK_SIZE, 0, streams[0] >> > (score_method, offsets);
                }
                else {
                    gpu_contract_address_work << <GRID_SIZE, BLOCK_SIZE, 0, streams[0] >> > (score_method, offsets);
                }
            }

            if (!first_iteration) {
                previous_random_key = random_key;
                random_key = cpu_add_256(random_key, random_key_increment);
                if (gte_256(random_key, max_key)) {
                    random_key = cpu_sub_256(random_key, max_key);
                }
            }
            CurvePoint thread_offset = cpu_point_multiply(G, _uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK });
            CurvePoint p = cpu_point_multiply(G, cpu_add_256(_uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK - 1 }, random_key));
            for (int i = 0; i < BLOCK_SIZE; i++) {
                thread_offsets_host[i] = p;
                p = cpu_point_add(p, thread_offset);
            }
            gpu_assert(cudaMemcpyToSymbolAsync(thread_offsets, thread_offsets_host, BLOCK_SIZE * sizeof(CurvePoint), 0, cudaMemcpyHostToDevice, streams[1]));
            gpu_assert(cudaStreamSynchronize(streams[1]))
                gpu_assert(cudaStreamSynchronize(streams[0]))

                if (!first_iteration) {
                    end_time = milliseconds();
                    elapsed = (end_time - start_time) / 1000.0;
                }
            start_time = milliseconds();

            gpu_address_init << <GRID_SIZE / BLOCK_SIZE, BLOCK_SIZE, 0, streams[0] >> > (block_offsets, offsets);
            if (!first_iteration) {
                gpu_assert(cudaMemcpyFromSymbolAsync(device_memory_host, device_memory, (2 + OUTPUT_BUFFER_SIZE * 3) * sizeof(uint64_t), 0, cudaMemcpyDeviceToHost, streams[1]))
                    gpu_assert(cudaStreamSynchronize(streams[1]))
            }
            if (!first_iteration) {
                global_max_score_mutex.lock();
                if (output_counter_host[0] != 0) {
                    if (max_score_host[0] > global_max_score) {
                        global_max_score = max_score_host[0];
                    }
                    else {
                        max_score_host[0] = global_max_score;
                    }
                }
                global_max_score_mutex.unlock();

                double speed = GRID_WORK / elapsed / 1000000.0 * 2;
                if (output_counter_host[0] != 0) {
                    int valid_results = 0;

                    for (int i = 0; i < output_counter_host[0]; i++) {
                        if (output_buffer2_host[i] < max_score_host[0]) { continue; }
                        valid_results++;
                    }

                    if (valid_results > 0) {
                        _uint256* results = new _uint256[valid_results];
                        int* scores = new int[valid_results];
                        valid_results = 0;

                        for (int i = 0; i < output_counter_host[0]; i++) {
                            if (output_buffer2_host[i] < max_score_host[0]) { continue; }

                            uint64_t k_offset = output_buffer_host[i];
                            _uint256 k = cpu_add_256(previous_random_key, cpu_add_256(_uint256{ 0, 0, 0, 0, 0, 0, 0, THREAD_WORK }, _uint256{ 0, 0, 0, 0, 0, 0, (uint32_t)(k_offset >> 32), (uint32_t)(k_offset & 0xFFFFFFFF) }));

                            if (output_buffer3_host[i]) {
                                k = cpu_sub_256(N, k);
                            }

                            int idx = valid_results++;
                            results[idx] = k;
                            scores[idx] = output_buffer2_host[i];
                        }

                        message_queue_mutex.lock();
                        message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, valid_results, results, scores });
                        message_queue_mutex.unlock();
                    }
                    else {
                        message_queue_mutex.lock();
                        message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                        message_queue_mutex.unlock();
                    }
                }
                else {
                    message_queue_mutex.lock();
                    message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                    message_queue_mutex.unlock();
                }
            }

            if (!first_iteration) {
                output_counter_host[0] = 0;
                gpu_assert(cudaMemcpyToSymbolAsync(device_memory, device_memory_host, sizeof(uint64_t), 0, cudaMemcpyHostToDevice, streams[1]));
                gpu_assert(cudaStreamSynchronize(streams[1]))
            }
            gpu_assert(cudaStreamSynchronize(streams[0]))
                first_iteration = false;
        }
    }

    if (mode == 2) {
        while (true) {
            uint64_t start_time = milliseconds();
            gpu_contract2_address_work << <GRID_SIZE, BLOCK_SIZE >> > (score_method, origin_address, random_key, bytecode);

            gpu_assert(cudaDeviceSynchronize())
                gpu_assert(cudaMemcpyFromSymbol(device_memory_host, device_memory, (2 + OUTPUT_BUFFER_SIZE * 3) * sizeof(uint64_t)))

                uint64_t end_time = milliseconds();
            double elapsed = (end_time - start_time) / 1000.0;

            global_max_score_mutex.lock();
            if (output_counter_host[0] != 0) {
                if (max_score_host[0] > global_max_score) {
                    global_max_score = max_score_host[0];
                }
                else {
                    max_score_host[0] = global_max_score;
                }
            }
            global_max_score_mutex.unlock();

            double speed = GRID_WORK / elapsed / 1000000.0;
            if (output_counter_host[0] != 0) {
                int valid_results = 0;

                for (int i = 0; i < output_counter_host[0]; i++) {
                    if (output_buffer2_host[i] < max_score_host[0]) { continue; }
                    valid_results++;
                }

                if (valid_results > 0) {
                    _uint256* results = new _uint256[valid_results];
                    int* scores = new int[valid_results];
                    valid_results = 0;

                    for (int i = 0; i < output_counter_host[0]; i++) {
                        if (output_buffer2_host[i] < max_score_host[0]) { continue; }

                        uint64_t k_offset = output_buffer_host[i];
                        _uint256 k = cpu_add_256(random_key, _uint256{ 0, 0, 0, 0, 0, 0, (uint32_t)(k_offset >> 32), (uint32_t)(k_offset & 0xFFFFFFFF) });

                        int idx = valid_results++;
                        results[idx] = k;
                        scores[idx] = output_buffer2_host[i];
                    }

                    message_queue_mutex.lock();
                    message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, valid_results, results, scores });
                    message_queue_mutex.unlock();
                }
                else {
                    message_queue_mutex.lock();
                    message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                    message_queue_mutex.unlock();
                }
            }
            else {
                message_queue_mutex.lock();
                message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                message_queue_mutex.unlock();
            }

            random_key = cpu_add_256(random_key, random_key_increment);

            output_counter_host[0] = 0;
            gpu_assert(cudaMemcpyToSymbol(device_memory, device_memory_host, sizeof(uint64_t)));
        }
    }

    if (mode == 3) {
        while (true) {
            uint64_t start_time = milliseconds();
            gpu_contract3_address_work << <GRID_SIZE, BLOCK_SIZE >> > (score_method, origin_address, deployer_address, random_key, bytecode);

            gpu_assert(cudaDeviceSynchronize())
                gpu_assert(cudaMemcpyFromSymbol(device_memory_host, device_memory, (2 + OUTPUT_BUFFER_SIZE * 3) * sizeof(uint64_t)))

                uint64_t end_time = milliseconds();
            double elapsed = (end_time - start_time) / 1000.0;

            global_max_score_mutex.lock();
            if (output_counter_host[0] != 0) {
                if (max_score_host[0] > global_max_score) {
                    global_max_score = max_score_host[0];
                }
                else {
                    max_score_host[0] = global_max_score;
                }
            }
            global_max_score_mutex.unlock();

            double speed = GRID_WORK / elapsed / 1000000.0;
            if (output_counter_host[0] != 0) {
                int valid_results = 0;

                for (int i = 0; i < output_counter_host[0]; i++) {
                    if (output_buffer2_host[i] < max_score_host[0]) { continue; }
                    valid_results++;
                }

                if (valid_results > 0) {
                    _uint256* results = new _uint256[valid_results];
                    int* scores = new int[valid_results];
                    valid_results = 0;

                    for (int i = 0; i < output_counter_host[0]; i++) {
                        if (output_buffer2_host[i] < max_score_host[0]) { continue; }

                        uint64_t k_offset = output_buffer_host[i];
                        _uint256 k = cpu_add_256(random_key, _uint256{ 0, 0, 0, 0, 0, 0, (uint32_t)(k_offset >> 32), (uint32_t)(k_offset & 0xFFFFFFFF) });

                        int idx = valid_results++;
                        results[idx] = k;
                        scores[idx] = output_buffer2_host[i];
                    }

                    message_queue_mutex.lock();
                    message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, valid_results, results, scores });
                    message_queue_mutex.unlock();
                }
                else {
                    message_queue_mutex.lock();
                    message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                    message_queue_mutex.unlock();
                }
            }
            else {
                message_queue_mutex.lock();
                message_queue.push(Message{ end_time, 0, device_index, cudaSuccess, speed, 0 });
                message_queue_mutex.unlock();
            }

            random_key = cpu_add_256(random_key, random_key_increment);

            output_counter_host[0] = 0;
            gpu_assert(cudaMemcpyToSymbol(device_memory, device_memory_host, sizeof(uint64_t)));
        }
    }
}


void print_speeds(int num_devices, int* device_ids, double* speeds) {
    double total = 0.0;
    for (int i = 0; i < num_devices; i++) {
        total += speeds[i];
    }

    printf("Total: %.2fM/s", total);
    for (int i = 0; i < num_devices; i++) {
        printf("  DEVICE %d: %.2fM/s", device_ids[i], speeds[i]);
    }
}

void print_usage() {
    printf("Usage: ./vanity-eth-address [PARAMETERS]\n");
    printf("Scoring methods:\n");
    printf("  (-lz) --leading-zeros          Count zero bytes at the start of the address\n");
    printf("   (-z) --zeros                  Count zero bytes anywhere in the address\n");
    printf("   (-p) --prefix <pattern>       Search for exact prefix match (e.g., \"dead\")\n");
    printf("   (-s) --suffix <pattern>       Search for exact suffix match (e.g., \"beef\")\n");
    printf("  (-ps) --prefix-suffix <prefix> <suffix>  Search for both prefix and suffix\n");
    printf("  (-pp) --partial-prefix <pattern>  Search for best partial prefix match\n");
    printf("  (-ss) --partial-suffix <pattern>  Search for best partial suffix match\n");
    printf("  (-bb) --best-both <prefix> <suffix>  Search for best partial prefix+suffix\n");
    printf("Modes (normal addresses by default):\n");
    printf("   (-c) --contract               Search for addresses and score the contract address generated using nonce=0\n");
    printf("  (-c2) --contract2              Search for contract addresses using the CREATE2 opcode\n");
    printf("  (-c3) --contract3              Search for contract addresses using a CREATE3 proxy deployer\n");
    printf("Other:\n");
    printf("   (-d) --device <device_number> Use device <device_number> (Add one for each device for multi-gpu)\n");
    printf("   (-b) --bytecode <filename>    File containing contract bytecode (only needed when using --contract2 or --contract3)\n");
    printf("   (-a) --address <address>      Sender contract address (only needed when using --contract2 or --contract3)\n");
    printf("  (-ad) --deployer-address <address>  Deployer contract address (only needed when using --contract3)\n");
    printf("   (-w) --work-scale <num>       Defaults to 15. Scales the work done in each kernel.\n");
    printf("\nExamples:\n");
    printf("  ./vanity-eth-address --zeros --device 0 --device 2 --work-scale 17\n");
    printf("  ./vanity-eth-address --prefix \"dead\" --device 0\n");
    printf("  ./vanity-eth-address --suffix \"beef\" --device 0\n");
    printf("  ./vanity-eth-address --prefix-suffix \"dead\" \"beef\" --device 0\n");
    printf("  ./vanity-eth-address --partial-prefix \"deadbeef\" --device 0\n");
}


int main(int argc, char* argv[]) {
    int score_method = -1; // 0 = leading zeroes, 1 = zeros, 2 = prefix, 3 = suffix, 4 = prefix+suffix, 5 = partial prefix, 6 = partial suffix, 7 = partial both
    int mode = 0; // 0 = address, 1 = contract, 2 = create2 contract, 3 = create3 proxy contract
    char* input_file = 0;
    char* input_address = 0;
    char* input_deployer_address = 0;
    std::string target_prefix_str;
    std::string target_suffix_str;

    int num_devices = 0;
    int device_ids[10];

    for (int i = 1; i < argc;) {
        if (strcmp(argv[i], "--device") == 0 || strcmp(argv[i], "-d") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --device requires a device number\n");
                return 1;
            }
            device_ids[num_devices++] = atoi(argv[i + 1]);
            i += 2;
        }
        else if (strcmp(argv[i], "--leading-zeros") == 0 || strcmp(argv[i], "-lz") == 0) {
            score_method = 0;
            i++;
        }
        else if (strcmp(argv[i], "--zeros") == 0 || strcmp(argv[i], "-z") == 0) {
            score_method = 1;
            i++;
        }
        else if (strcmp(argv[i], "--prefix") == 0 || strcmp(argv[i], "-p") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --prefix requires a pattern\n");
                return 1;
            }
            score_method = 2;
            target_prefix_str = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--suffix") == 0 || strcmp(argv[i], "-s") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --suffix requires a pattern\n");
                return 1;
            }
            score_method = 3;
            target_suffix_str = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--prefix-suffix") == 0 || strcmp(argv[i], "-ps") == 0) {
            if (i + 2 >= argc) {
                printf("Error: --prefix-suffix requires two patterns\n");
                return 1;
            }
            score_method = 4;
            target_prefix_str = argv[i + 1];
            target_suffix_str = argv[i + 2];
            i += 3;
        }
        else if (strcmp(argv[i], "--partial-prefix") == 0 || strcmp(argv[i], "-pp") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --partial-prefix requires a pattern\n");
                return 1;
            }
            score_method = 5;
            target_prefix_str = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--partial-suffix") == 0 || strcmp(argv[i], "-ss") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --partial-suffix requires a pattern\n");
                return 1;
            }
            score_method = 6;
            target_suffix_str = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--best-both") == 0 || strcmp(argv[i], "-bb") == 0) {
            if (i + 2 >= argc) {
                printf("Error: --best-both requires two patterns\n");
                return 1;
            }
            score_method = 7;
            target_prefix_str = argv[i + 1];
            target_suffix_str = argv[i + 2];
            i += 3;
        }
        else if (strcmp(argv[i], "--contract") == 0 || strcmp(argv[i], "-c") == 0) {
            mode = 1;
            i++;
        }
        else if (strcmp(argv[i], "--contract2") == 0 || strcmp(argv[i], "-c2") == 0) {
            mode = 2;
            i++;
        }
        else if (strcmp(argv[i], "--contract3") == 0 || strcmp(argv[i], "-c3") == 0) {
            mode = 3;
            i++;
        }
        else if (strcmp(argv[i], "--bytecode") == 0 || strcmp(argv[i], "-b") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --bytecode requires a filename\n");
                return 1;
            }
            input_file = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--address") == 0 || strcmp(argv[i], "-a") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --address requires an address\n");
                return 1;
            }
            input_address = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--deployer-address") == 0 || strcmp(argv[i], "-da") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --deployer-address requires an address\n");
                return 1;
            }
            input_deployer_address = argv[i + 1];
            i += 2;
        }
        else if (strcmp(argv[i], "--work-scale") == 0 || strcmp(argv[i], "-w") == 0) {
            if (i + 1 >= argc) {
                printf("Error: --work-scale requires a number\n");
                return 1;
            }
            GRID_SIZE = 1U << atoi(argv[i + 1]);
            i += 2;
        }
        else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage();
            return 0;
        }
        else {
            printf("Unknown argument: %s\n", argv[i]);
            print_usage();
            return 1;
        }
    }

    if (num_devices == 0) {
        printf("No devices were specified\n");
        return 1;
    }

    if (score_method == -1) {
        printf("No scoring method was specified\n");
        print_usage();
        return 1;
    }

    // Validate patterns
    if (score_method >= 2 && score_method <= 7) {
        try {
            if (score_method == 2 || score_method == 4 || score_method == 5 || score_method == 7) {
                if (target_prefix_str.empty()) {
                    printf("Error: Prefix pattern cannot be empty\n");
                    return 1;
                }
                if (target_prefix_str.length() > MAX_PREFIX_LENGTH) {
                    printf("Error: Prefix pattern too long (max %d characters)\n", MAX_PREFIX_LENGTH);
                    return 1;
                }
                // Convert to lowercase for consistency
                std::transform(target_prefix_str.begin(), target_prefix_str.end(), target_prefix_str.begin(), ::tolower);
            }

            if (score_method == 3 || score_method == 4 || score_method == 6 || score_method == 7) {
                if (target_suffix_str.empty()) {
                    printf("Error: Suffix pattern cannot be empty\n");
                    return 1;
                }
                if (target_suffix_str.length() > MAX_SUFFIX_LENGTH) {
                    printf("Error: Suffix pattern too long (max %d characters)\n", MAX_SUFFIX_LENGTH);
                    return 1;
                }
                // Convert to lowercase for consistency
                std::transform(target_suffix_str.begin(), target_suffix_str.end(), target_suffix_str.begin(), ::tolower);
            }
        }
        catch (const std::exception& e) {
            printf("Error processing patterns: %s\n", e.what());
            return 1;
        }
    }

    if (mode == 2 && !input_file) {
        printf("You must specify contract bytecode when using --contract2\n");
        return 1;
    }

    if ((mode == 2 || mode == 3) && !input_address) {
        printf("You must specify an origin address when using --contract2\n");
        return 1;
    }
    else if ((mode == 2 || mode == 3) && strlen(input_address) != 40 && strlen(input_address) != 42) {
        printf("The origin address must be 40 characters long\n");
        return 1;
    }

    if (mode == 3 && !input_deployer_address) {
        printf("You must specify a deployer address when using --contract3\n");
        return 1;
    }

    for (int i = 0; i < num_devices; i++) {
        cudaError_t e = cudaSetDevice(device_ids[i]);
        if (e != cudaSuccess) {
            printf("Could not detect device %d\n", device_ids[i]);
            return 1;
        }
    }

    // Copy patterns to GPU constant memory
    if (score_method >= 2 && score_method <= 7) {
        try {
            // Set up prefix
            if (score_method == 2 || score_method == 4 || score_method == 5 || score_method == 7) {
                std::vector<uint32_t> prefix_nibbles = hex_string_to_nibbles(target_prefix_str);
                int prefix_len = prefix_nibbles.size();

                uint32_t prefix_array[MAX_PREFIX_LENGTH] = { 0 };
                for (int i = 0; i < prefix_len && i < MAX_PREFIX_LENGTH; i++) {
                    prefix_array[i] = prefix_nibbles[i];
                }

                for (int i = 0; i < num_devices; i++) {
                    cudaSetDevice(device_ids[i]);
                    cudaMemcpyToSymbol(target_prefix, prefix_array, MAX_PREFIX_LENGTH * sizeof(uint32_t));
                    cudaMemcpyToSymbol(prefix_length, &prefix_len, sizeof(int));
                }

                printf("Searching for prefix: %s (%d characters)\n", target_prefix_str.c_str(), prefix_len);
            }
            else {
                int zero_len = 0;
                for (int i = 0; i < num_devices; i++) {
                    cudaSetDevice(device_ids[i]);
                    cudaMemcpyToSymbol(prefix_length, &zero_len, sizeof(int));
                }
            }

            // Set up suffix
            if (score_method == 3 || score_method == 4 || score_method == 6 || score_method == 7) {
                std::vector<uint32_t> suffix_nibbles = hex_string_to_nibbles(target_suffix_str);
                int suffix_len = suffix_nibbles.size();

                uint32_t suffix_array[MAX_SUFFIX_LENGTH] = { 0 };
                for (int i = 0; i < suffix_len && i < MAX_SUFFIX_LENGTH; i++) {
                    suffix_array[i] = suffix_nibbles[i];
                }

                for (int i = 0; i < num_devices; i++) {
                    cudaSetDevice(device_ids[i]);
                    cudaMemcpyToSymbol(target_suffix, suffix_array, MAX_SUFFIX_LENGTH * sizeof(uint32_t));
                    cudaMemcpyToSymbol(suffix_length, &suffix_len, sizeof(int));
                }

                printf("Searching for suffix: %s (%d characters)\n", target_suffix_str.c_str(), suffix_len);
            }
            else {
                int zero_len = 0;
                for (int i = 0; i < num_devices; i++) {
                    cudaSetDevice(device_ids[i]);
                    cudaMemcpyToSymbol(suffix_length, &zero_len, sizeof(int));
                }
            }
        }
        catch (const std::exception& e) {
            printf("Error setting up GPU patterns: %s\n", e.what());
            return 1;
        }
    }

#define nothex(n) ((n < 48 || n > 57) && (n < 65 || n > 70) && (n < 97 || n > 102))
    _uint256 bytecode_hash;
    if (mode == 2 || mode == 3) {
        std::ifstream infile(input_file, std::ios::binary);
        if (!infile.is_open()) {
            printf("Failed to open the bytecode file.\n");
            return 1;
        }

        int file_size = 0;
        {
            infile.seekg(0, std::ios::end);
            std::streampos file_size_ = infile.tellg();
            infile.seekg(0, std::ios::beg);
            file_size = file_size_ - infile.tellg();
        }

        if (file_size & 1) {
            printf("Invalid bytecode in file.\n");
            return 1;
        }

        uint8_t* bytecode = new uint8_t[24576];
        if (bytecode == 0) {
            printf("Error while allocating memory. Perhaps you are out of memory?");
            return 1;
        }

        char byte[2];
        bool prefix = false;
        for (int i = 0; i < (file_size >> 1); i++) {
            infile.read((char*)&byte, 2);
            if (i == 0) {
                prefix = byte[0] == '0' && byte[1] == 'x';
                if ((file_size >> 1) > (prefix ? 24577 : 24576)) {
                    printf("Invalid bytecode in file.\n");
                    delete[] bytecode;
                    return 1;
                }
                if (prefix) { continue; }
            }

            if (nothex(byte[0]) || nothex(byte[1])) {
                printf("Invalid bytecode in file.\n");
                delete[] bytecode;
                return 1;
            }

            bytecode[i - prefix] = (uint8_t)strtol(byte, 0, 16);
        }
        bytecode_hash = cpu_full_keccak(bytecode, (file_size >> 1) - prefix);
        delete[] bytecode;
    }

    Address origin_address;
    if (mode == 2 || mode == 3) {
        if (strlen(input_address) == 42) {
            input_address += 2;
        }
        char substr[9];

#define round(i, offset) \
        strncpy(substr, input_address + offset * 8, 8); \
        if (nothex(substr[0]) || nothex(substr[1]) || nothex(substr[2]) || nothex(substr[3]) || nothex(substr[4]) || nothex(substr[5]) || nothex(substr[6]) || nothex(substr[7])) { \
            printf("Invalid origin address.\n"); \
            return 1; \
        } \
        origin_address.i = strtoull(substr, 0, 16);

        round(a, 0)
            round(b, 1)
            round(c, 2)
            round(d, 3)
            round(e, 4)

#undef round
    }

    Address deployer_address;
    if (mode == 3) {
        if (strlen(input_deployer_address) == 42) {
            input_deployer_address += 2;
        }
        char substr[9];

#define round(i, offset) \
        strncpy(substr, input_deployer_address + offset * 8, 8); \
        if (nothex(substr[0]) || nothex(substr[1]) || nothex(substr[2]) || nothex(substr[3]) || nothex(substr[4]) || nothex(substr[5]) || nothex(substr[6]) || nothex(substr[7])) { \
            printf("Invalid deployer address.\n"); \
            return 1; \
        } \
        deployer_address.i = strtoull(substr, 0, 16);

        round(a, 0)
            round(b, 1)
            round(c, 2)
            round(d, 3)
            round(e, 4)

#undef round
    }
#undef nothex


    std::vector<std::thread> threads;
    uint64_t global_start_time = milliseconds();
    for (int i = 0; i < num_devices; i++) {
        std::thread th(host_thread, device_ids[i], i, score_method, mode, origin_address, deployer_address, bytecode_hash);
        threads.push_back(move(th));
    }

    double speeds[100];
    while (true) {
        message_queue_mutex.lock();
        if (message_queue.size() == 0) {
            message_queue_mutex.unlock();
            std::this_thread::sleep_for(std::chrono::milliseconds(500));
        }
        else {
            while (!message_queue.empty()) {
                Message m = message_queue.front();
                message_queue.pop();

                int device_index = m.device_index;

                if (m.status == 0) {
                    speeds[device_index] = m.speed;

                    printf("\r");
                    if (m.results_count != 0) {
                        Address* addresses = new Address[m.results_count];
                        for (int i = 0; i < m.results_count; i++) {
                            if (mode == 0) {
                                CurvePoint p = cpu_point_multiply(G, m.results[i]);
                                addresses[i] = cpu_calculate_address(p.x, p.y);
                            }
                            else if (mode == 1) {
                                CurvePoint p = cpu_point_multiply(G, m.results[i]);
                                addresses[i] = cpu_calculate_contract_address(cpu_calculate_address(p.x, p.y));
                            }
                            else if (mode == 2) {
                                addresses[i] = cpu_calculate_contract_address2(origin_address, m.results[i], bytecode_hash);
                            }
                            else if (mode == 3) {
                                _uint256 salt = cpu_calculate_create3_salt(origin_address, m.results[i]);
                                Address proxy = cpu_calculate_contract_address2(deployer_address, salt, bytecode_hash);
                                addresses[i] = cpu_calculate_contract_address(proxy, 1);
                            }
                        }

                        for (int i = 0; i < m.results_count; i++) {
                            _uint256 k = m.results[i];
                            int score = m.scores[i];
                            Address a = addresses[i];
                            uint64_t time = (m.time - global_start_time) / 1000;

                            if (mode == 0 || mode == 1) {
                                printf("Elapsed: %06u Score: %02u Private Key: 0x%08x%08x%08x%08x%08x%08x%08x%08x Address: 0x%08x%08x%08x%08x%08x\n", (uint32_t)time, score, k.a, k.b, k.c, k.d, k.e, k.f, k.g, k.h, a.a, a.b, a.c, a.d, a.e);
                            }
                            else if (mode == 2 || mode == 3) {
                                printf("Elapsed: %06u Score: %02u Salt: 0x%08x%08x%08x%08x%08x%08x%08x%08x Address: 0x%08x%08x%08x%08x%08x\n", (uint32_t)time, score, k.a, k.b, k.c, k.d, k.e, k.f, k.g, k.h, a.a, a.b, a.c, a.d, a.e);
                            }
                        }

                        delete[] addresses;
                        delete[] m.results;
                        delete[] m.scores;
                    }
                    print_speeds(num_devices, device_ids, speeds);
                    fflush(stdout);
                }
                else if (m.status == 1) {
                    printf("\rCuda error %d on device %d. Device will halt work.\n", m.error, device_ids[device_index]);
                    print_speeds(num_devices, device_ids, speeds);
                    fflush(stdout);
                }
                else if (m.status == 11) {
                    printf("\rError from BCryptGenRandom. Device %d will halt work.", device_ids[device_index]);
                    print_speeds(num_devices, device_ids, speeds);
                    fflush(stdout);
                }
                else if (m.status == 12) {
                    printf("\rError while reading from /dev/urandom. Device %d will halt work.", device_ids[device_index]);
                    print_speeds(num_devices, device_ids, speeds);
                    fflush(stdout);
                }
                else if (m.status == 13) {
                    printf("\rError while opening /dev/urandom. Device %d will halt work.", device_ids[device_index]);
                    print_speeds(num_devices, device_ids, speeds);
                    fflush(stdout);
                }
                else if (m.status == 100) {
                    printf("\rError while allocating memory. Perhaps you are out of memory? Device %d will halt work.", device_ids[device_index]);
                }
            }
            message_queue_mutex.unlock();
        }
    }
}
