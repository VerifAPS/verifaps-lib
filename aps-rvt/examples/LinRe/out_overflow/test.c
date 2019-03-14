#include <stdint.h>
#include <stdio.h>


int main() {
    int16_t m = 802, x1=2927, y1=1362, ICONST=1000;
    printf("%d\n", (int16_t) (((int16_t)( (int16_t) (m * x1) / ICONST)) - y1));
    printf("%d\n", - (int16_t) (((int16_t)( (int16_t) (m * x1) / ICONST)) - y1));
    printf("%d\n", (int16_t) (y1 - (int16_t)((int16_t)(m * x1) / ICONST)));
    return 0;
}

