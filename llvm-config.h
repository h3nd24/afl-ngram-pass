#ifndef LLVM_CONFIG_H
#define LLVM_CONFIG_H

#include "../config.h"

#if (MAP_SIZE_POW2 <= 16)
typedef u16 PREV_LOC_T;
#elif (MAP_SIZE_POW2 <= 32)
typedef u32 PREV_LOC_T;
#else
typedef u64 PREV_LOC_T;
#endif

/* Maximum ngram size */
#define MAX_NGRAM_SIZE 128

#endif
