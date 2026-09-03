#include <stdio.h>
#include <stdint.h>

struct TestStruct {
    uint8_t a;
    uint16_t b;
    uint32_t c;
    uint64_t d;
};

void printStruct(
    struct TestStruct c
) {
    printf("%hhd\n", c.a);
    printf("%hd\n", c.b);
    printf("%d\n", c.c);
    printf("%lld\n", c.d);
}
