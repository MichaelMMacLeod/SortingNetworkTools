#include <stdint.h>
#include <assert.h>

uint64_t uShr64x8(uint64_t lhs, uint8_t rhs) {
    assert(rhs <= 63 && "uShr64x8 attempt to right shift with overflow");
    return lhs >> rhs;
}

uint64_t uShl64x8(uint64_t lhs, uint8_t rhs) {
    assert(rhs <= 63 && "uShl64x8 attempt to left shift with overflow");
    return lhs << rhs;
}