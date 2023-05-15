/* { dg-do run } */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    unsigned char blue;
    unsigned char green;
} Pixel;

typedef struct {
    unsigned short colormaplength;
    Pixel         *colormapdata;
} TargaImage;

TargaImage *img;

int main() {
    img = (TargaImage *) malloc( sizeof(TargaImage) );
    if (img->colormaplength > 0) {
        img->colormapdata = (Pixel *) malloc(sizeof(Pixel) * img->colormaplength);
        memset(img->colormapdata, 0, (sizeof(Pixel) * img->colormaplength) );
    }
}
