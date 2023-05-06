/*
 * TLSH is provided for use under two licenses: Apache OR BSD.
 * Users may opt to use either license depending on the license
 * restictions of the systems with which they plan to integrate
 * the TLSH code.
 */

/* ==============
 * Apache License
 * ==============
 * Copyright 2013 Trend Micro Incorporated
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/* ===========
 * BSD License
 * ===========
 * Copyright (c) 2013, Trend Micro Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.

 * 3. Neither the name of the copyright holder nor the names of its contributors
 *    may be used to endorse or promote products derived from this software without
 *    specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE
 * OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

//#include "tlsh.h"
//#include "tlsh_impl.h"
//#include "tlsh_util.h"

#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <math.h>
// #include <algorithm>
#include <string.h>
#include <errno.h>
#include <malloc.h>

#define RANGE_LVALUE 256
#define RANGE_QRATIO 16
#define BUCKETS 256
#define SLIDING_WND_SIZE 5
#define CODE_SIZE           32   // 128 * 2 bits = 32 bytes
#define INTERNAL_TLSH_STRING_LEN 70
#define TLSH_CHECKSUM_LEN 1
#define TLSH_STRING_LEN_REQ 72
// changed the minimum data length to 256 for version 3.3
#define MIN_DATA_LENGTH		50
// added the -force option for version 3.5
// added the -conservatibe option for version 3.17
#define MIN_CONSERVATIVE_DATA_LENGTH	256
#define EFF_BUCKETS         128

typedef struct lsh_bin_struct {
  unsigned char checksum[1];
  unsigned char Lvalue;
  union {
    unsigned char QB;
    struct{
      unsigned char Q1ratio : 4;
      unsigned char Q2ratio : 4;
    } QR;
  } Q;
  unsigned char tmp_code[32];
} lsh_bin_t;

typedef struct {
  unsigned int *a_bucket;
  unsigned char slide_window[5];
  unsigned int data_len;

  lsh_bin_t lsh_bin;
  char *lsh_code;
  int lsh_code_valid;
} TlshImpl;

static void find_quartile(unsigned int *q1, unsigned int *q2, unsigned int *q3, const unsigned int * a_bucket);
static unsigned int partition(unsigned int * buf, unsigned int left, unsigned int right);

////////////////////////////////////////////////////////////////////////////////////////////////

void tlshImpl_reset(TlshImpl * this) {
  if (this->a_bucket) free(this->a_bucket); this->a_bucket = NULL;
  if (this->lsh_code) free(this->lsh_code); this->lsh_code = NULL;
  memset(this->slide_window, 0, sizeof this->slide_window);
  memset(&this->lsh_bin, 0, sizeof this->lsh_bin);
  this->data_len = 0;
  this->lsh_code_valid = 0;
}

TlshImpl * tlshImpl_new() {
  //: a_bucket(NULL), data_len(0), lsh_code(NULL), lsh_code_valid(false)
  TlshImpl * this = (TlshImpl *) malloc(sizeof(TlshImpl));
  memset(this, 0, sizeof(TlshImpl));
  tlshImpl_reset(this);
  assert (sizeof (this->lsh_bin.Q.QR) == sizeof (this->lsh_bin.Q.QB));
}

void tlshImpl_done(TlshImpl * this) {
  if (this->a_bucket) free(this->a_bucket);
  if (this->lsh_code) free(this->lsh_code);
  free(this);
}

////////////////////////////////////////////////////////////////////////////////////////////

// Pearson's sample random table
static unsigned char v_table[256] = {
    1, 87, 49, 12, 176, 178, 102, 166, 121, 193, 6, 84, 249, 230, 44, 163,
    14, 197, 213, 181, 161, 85, 218, 80, 64, 239, 24, 226, 236, 142, 38, 200,
    110, 177, 104, 103, 141, 253, 255, 50, 77, 101, 81, 18, 45, 96, 31, 222,
    25, 107, 190, 70, 86, 237, 240, 34, 72, 242, 20, 214, 244, 227, 149, 235,
    97, 234, 57, 22, 60, 250, 82, 175, 208, 5, 127, 199, 111, 62, 135, 248,
    174, 169, 211, 58, 66, 154, 106, 195, 245, 171, 17, 187, 182, 179, 0, 243,
    132, 56, 148, 75, 128, 133, 158, 100, 130, 126, 91, 13, 153, 246, 216, 219,
    119, 68, 223, 78, 83, 88, 201, 99, 122, 11, 92, 32, 136, 114, 52, 10,
    138, 30, 48, 183, 156, 35, 61, 26, 143, 74, 251, 94, 129, 162, 63, 152,
    170, 7, 115, 167, 241, 206, 3, 150, 55, 59, 151, 220, 90, 53, 23, 131,
    125, 173, 15, 238, 79, 95, 89, 16, 105, 137, 225, 224, 217, 160, 37, 123,
    118, 73, 2, 157, 46, 116, 9, 145, 134, 228, 207, 212, 202, 215, 69, 229,
    27, 188, 67, 124, 168, 252, 42, 4, 29, 108, 21, 247, 19, 205, 39, 203,
    233, 40, 186, 147, 198, 192, 155, 33, 164, 191, 98, 204, 165, 180, 117, 76,
    140, 36, 210, 172, 41, 54, 159, 8, 185, 232, 113, 196, 231, 47, 146, 120,
    51, 65, 28, 144, 254, 221, 93, 189, 194, 139, 112, 43, 71, 109, 184, 209
};

static unsigned char v_table48[256] = {
	1, 39, 1, 12, 32, 34, 6, 22, 25, 1, 6, 36, 48, 38, 44, 19,
	14, 5, 21, 37, 17, 37, 26, 32, 16, 47, 24, 34, 44, 46, 38, 8,
	14, 33, 8, 7, 45, 48, 48, 2, 29, 5, 33, 18, 45, 0, 31, 30,
	25, 11, 46, 22, 38, 45, 48, 34, 24, 48, 20, 22, 48, 35, 5, 43,
	1, 42, 9, 22, 12, 48, 34, 31, 16, 5, 31, 7, 15, 14, 39, 48,
	30, 25, 19, 10, 18, 10, 10, 3, 48, 27, 17, 43, 38, 35, 0, 48,
	36, 8, 4, 27, 32, 37, 14, 4, 34, 30, 43, 13, 9, 48, 24, 27,
	23, 20, 31, 30, 35, 40, 9, 3, 26, 11, 44, 32, 40, 18, 4, 10,
	42, 30, 0, 39, 12, 35, 13, 26, 47, 26, 48, 46, 33, 18, 15, 8,
	26, 7, 19, 23, 48, 14, 3, 6, 7, 11, 7, 28, 42, 5, 23, 35,
	29, 29, 15, 46, 31, 47, 41, 16, 9, 41, 33, 32, 25, 16, 37, 27,
	22, 25, 2, 13, 46, 20, 9, 1, 38, 36, 15, 20, 10, 23, 21, 37,
	27, 44, 19, 28, 24, 48, 42, 4, 29, 12, 21, 48, 19, 13, 39, 11,
	41, 40, 42, 3, 6, 0, 11, 33, 20, 47, 2, 12, 21, 36, 21, 28,
	44, 36, 18, 28, 41, 6, 15, 8, 41, 40, 17, 4, 39, 47, 2, 24,
	3, 17, 28, 0, 48, 29, 45, 45, 2, 43, 16, 43, 23, 13, 40, 17,
};

// Pearson's algorithm
unsigned char b_mapping(unsigned char salt, unsigned char i, unsigned char j, unsigned char k) {
    unsigned char h = 0;

    h = v_table[h ^ salt];
    h = v_table[h ^ i];
    h = v_table[h ^ j];
    h = v_table[h ^ k];
    return h;
}

#if defined BUCKETS_48
#define fast_b_mapping(ms,i,j,k) (v_table48[ v_table[ v_table[ms^i] ^ j] ^ k ])
#else
#define fast_b_mapping(ms,i,j,k) (v_table  [ v_table[ v_table[ms^i] ^ j] ^ k ])
#endif

////////////////////////////////////////////////////////////////////////////////////////////

#define SLIDING_WND_SIZE_M1	4


#define RNG_SIZE    	SLIDING_WND_SIZE
#define RNG_IDX(i)	((i+RNG_SIZE)%RNG_SIZE)

void tlshImpl_fast_update5(TlshImpl * this,
                           const unsigned char* data, unsigned int len, int tlsh_option);


void tlshImpl_update(TlshImpl * this, const unsigned char* data,
                     unsigned int len, int tlsh_option)
{
    if (this->lsh_code_valid) {
      fprintf(stderr, "call to update() on a tlsh that is already valid\n");
      return;
    }

    unsigned int fed_len = this->data_len;

    if (this->a_bucket == NULL) {
      this->a_bucket = malloc(sizeof(int)*BUCKETS);
      memset(this->a_bucket, 0, sizeof(int)*BUCKETS);
    }

    if (TLSH_CHECKSUM_LEN == 1) {
      tlshImpl_fast_update5(this, data, len, tlsh_option);
	/* if ((tlsh_option & TLSH_OPTION_THREADED) || (tlsh_option & TLSH_OPTION_PRIVATE)) {
	* 	this->lsh_bin.checksum[0] = 0;
	}*/
	return;
    }
    int j = (int)(this->data_len % RNG_SIZE);

    for( unsigned int i=0; i<len; i++, fed_len++, j=RNG_IDX(j+1) ) {
        this->slide_window[j] = data[i];

        if ( fed_len >= SLIDING_WND_SIZE_M1 ) {
            //only calculate when input >= 5 bytes
            int j_1 = RNG_IDX(j-1);
            int j_2 = RNG_IDX(j-2);
            int j_3 = RNG_IDX(j-3);


            for (int k = 0; k < TLSH_CHECKSUM_LEN; k++) {
		if (k == 0) {
			//				 b_mapping(0, ... )
		 	this->lsh_bin.checksum[k] = fast_b_mapping(1, this->slide_window[j], this->slide_window[j_1], this->lsh_bin.checksum[k]);
		} else {
			// use calculated 1 byte checksums to expand the total checksum to 3 bytes
			this->lsh_bin.checksum[k] = b_mapping(this->lsh_bin.checksum[k-1], this->slide_window[j], this->slide_window[j_1], this->lsh_bin.checksum[k]);
		}
            }

            unsigned char r;
	    //	     b_mapping(2, ... )
	    r = fast_b_mapping(49, this->slide_window[j], this->slide_window[j_1], this->slide_window[j_2]);
            this->a_bucket[r]++;
	    //	     b_mapping(3, ... )
	    r = fast_b_mapping(12, this->slide_window[j], this->slide_window[j_1], this->slide_window[j_3]);
            this->a_bucket[r]++;
	    //	     b_mapping(5, ... )
	    r = fast_b_mapping(178, this->slide_window[j], this->slide_window[j_2], this->slide_window[j_3]);
            this->a_bucket[r]++;
        }
    }
    this->data_len += len;
}

static void raw_fast_update5(
	// inputs
	const unsigned char* data,
	unsigned int len,
	unsigned int fed_len,
	// outputs
	unsigned int *a_bucket,
	unsigned char *ret_checksum,
	unsigned char *slide_window
	)
{
	int j = (int)(fed_len % RNG_SIZE);
	unsigned char checksum = *ret_checksum;

	unsigned int start_i=0;
	if ( fed_len < SLIDING_WND_SIZE_M1 ) {
		int extra = SLIDING_WND_SIZE_M1 - fed_len;
		start_i	= extra;
		j	= (j + extra) % RNG_SIZE;
	}
	for( unsigned int i=start_i; i<len;  ) {
		//only calculate when input >= 5 bytes
		if ((i >= 4) && (i+5 < len)) {
			unsigned char a0 = data[i-4];
			unsigned char a1 = data[i-3];
			unsigned char a2 = data[i-2];
			unsigned char a3 = data[i-1];
			unsigned char a4 = data[i];
			unsigned char a5 = data[i+1];
			unsigned char a6 = data[i+2];
			unsigned char a7 = data[i+3];
			unsigned char a8 = data[i+4];

			checksum = fast_b_mapping(1, a4, a3, checksum );
			a_bucket[ fast_b_mapping(49,  a4, a3, a2 ) ]++;
			a_bucket[ fast_b_mapping(12,  a4, a3, a1 ) ]++;
			a_bucket[ fast_b_mapping(178, a4, a2, a1 ) ]++;
			a_bucket[ fast_b_mapping(166, a4, a2, a0 ) ]++;
			a_bucket[ fast_b_mapping(84,  a4, a3, a0 ) ]++;
			a_bucket[ fast_b_mapping(230, a4, a1, a0 ) ]++;

			checksum = fast_b_mapping(1, a5, a4, checksum );
			a_bucket[ fast_b_mapping(49,  a5, a4, a3 ) ]++;
			a_bucket[ fast_b_mapping(12,  a5, a4, a2 ) ]++;
			a_bucket[ fast_b_mapping(178, a5, a3, a2 ) ]++;
			a_bucket[ fast_b_mapping(166, a5, a3, a1 ) ]++;
			a_bucket[ fast_b_mapping(84,  a5, a4, a1 ) ]++;
			a_bucket[ fast_b_mapping(230, a5, a2, a1 ) ]++;

			checksum = fast_b_mapping(1, a6, a5, checksum );
			a_bucket[ fast_b_mapping(49,  a6, a5, a4 ) ]++;
			a_bucket[ fast_b_mapping(12,  a6, a5, a3 ) ]++;
			a_bucket[ fast_b_mapping(178, a6, a4, a3 ) ]++;
			a_bucket[ fast_b_mapping(166, a6, a4, a2 ) ]++;
			a_bucket[ fast_b_mapping(84,  a6, a5, a2 ) ]++;
			a_bucket[ fast_b_mapping(230, a6, a3, a2 ) ]++;

			checksum = fast_b_mapping(1, a7, a6, checksum );
			a_bucket[ fast_b_mapping(49,  a7, a6, a5 ) ]++;
			a_bucket[ fast_b_mapping(12,  a7, a6, a4 ) ]++;
			a_bucket[ fast_b_mapping(178, a7, a5, a4 ) ]++;
			a_bucket[ fast_b_mapping(166, a7, a5, a3 ) ]++;
			a_bucket[ fast_b_mapping(84,  a7, a6, a3 ) ]++;
			a_bucket[ fast_b_mapping(230, a7, a4, a3 ) ]++;

			checksum = fast_b_mapping(1, a8, a7, checksum );
			a_bucket[ fast_b_mapping(49,  a8, a7, a6 ) ]++;
			a_bucket[ fast_b_mapping(12,  a8, a7, a5 ) ]++;
			a_bucket[ fast_b_mapping(178, a8, a6, a5 ) ]++;
			a_bucket[ fast_b_mapping(166, a8, a6, a4 ) ]++;
			a_bucket[ fast_b_mapping(84,  a8, a7, a4 ) ]++;
			a_bucket[ fast_b_mapping(230, a8, a5, a4 ) ]++;

			i=i+5;
			j=RNG_IDX(j+5);
		} else {
			slide_window[j] = data[i];
			int j_1 = RNG_IDX(j-1); if (i >= 1) { slide_window[j_1] = data[i-1]; }
			int j_2 = RNG_IDX(j-2); if (i >= 2) { slide_window[j_2] = data[i-2]; }
			int j_3 = RNG_IDX(j-3); if (i >= 3) { slide_window[j_3] = data[i-3]; }
			int j_4 = RNG_IDX(j-4); if (i >= 4) { slide_window[j_4] = data[i-4]; }

			checksum = fast_b_mapping(1, slide_window[j], slide_window[j_1], checksum );
			a_bucket[ fast_b_mapping(49,  slide_window[j], slide_window[j_1], slide_window[j_2] ) ]++;
			a_bucket[ fast_b_mapping(12,  slide_window[j], slide_window[j_1], slide_window[j_3] ) ]++;
			a_bucket[ fast_b_mapping(178, slide_window[j], slide_window[j_2], slide_window[j_3] ) ]++;
			a_bucket[ fast_b_mapping(166, slide_window[j], slide_window[j_2], slide_window[j_4] ) ]++;
			a_bucket[ fast_b_mapping(84,  slide_window[j], slide_window[j_1], slide_window[j_4] ) ]++;
			a_bucket[ fast_b_mapping(230, slide_window[j], slide_window[j_3], slide_window[j_4] ) ]++;
			i++;
			j=RNG_IDX(j+1);
		}
	}
	*ret_checksum = checksum;
}

void tlshImpl_fast_update5(TlshImpl * this,
                           const unsigned char* data, unsigned int len, int tlsh_option)
{

  raw_fast_update5 (data, len, this->data_len, this->a_bucket, &(this->lsh_bin.checksum[0]), this->slide_window);
  this->data_len += len;
}

unsigned int topval[170] = {
1,
2,
3,
5,
7,
11,
17,
25,
38,
57,
86,
129,
194,
291,
437,
656,
854,
1110,
1443,
1876,
2439,
3171,
3475,
3823,
4205,
4626,
5088,
5597,
6157,
6772,
7450,
8195,
9014,
9916,
10907,
11998,
13198,
14518,
15970,
17567,
19323,
21256,
23382,
25720,
28292,
31121,
34233,
37656,
41422,
45564,
50121,
55133,
60646,
66711,
73382,
80721,
88793,
97672,
107439,
118183,
130002,
143002,
157302,
173032,
190335,
209369,
230306,
253337,
278670,
306538,
337191,
370911,
408002,
448802,
493682,
543050,
597356,
657091,
722800,
795081,
874589,
962048,
1058252,
1164078,
1280486,
1408534,
1549388,
1704327,
1874759,
2062236,
2268459,
2495305,
2744836,
3019320,
3321252,
3653374,
4018711,
4420582,
4862641,
5348905,
5883796,
6472176,
7119394,
7831333,
8614467,
9475909,
10423501,
11465851,
12612437,
13873681,
15261050,
16787154,
18465870,
20312458,
22343706,
24578077,
27035886,
29739474,
32713425,
35984770,
39583245,
43541573,
47895730,
52685306,
57953837,
63749221,
70124148,
77136564,
84850228,
93335252,
102668779,
112935659,
124229227,
136652151,
150317384,
165349128,
181884040,
200072456,
220079703,
242087671,
266296456,
292926096,
322218735,
354440623,
389884688,
428873168,
471760495,
518936559,
570830240,
627913311,
690704607,
759775136,
835752671,
919327967,
1011260767,
1112386880,
1223623232,
1345985727,
1480584256,
1628642751,
1791507135,
1970657856,
2167723648,
2384496256,
2622945920,
2885240448,
3173764736,
3491141248,
3840255616,
4224281216
};

unsigned char l_capturing(unsigned int len)
{
	int bottom = 0;
	int top    = 170;
	unsigned char idx = 85;

	while (1) {
		if (idx == 0) {
			return(idx);
		}
		if ((len <= topval[idx]) && (len > topval[idx-1])) {
// printf("len=%u	idx=%u\n", len, idx);
			return(idx);
		}
		if (len < topval[idx]) {
			top = idx - 1;
		} else {
			bottom = idx + 1;
		}
		idx = (bottom + top) / 2;
	}
}


/////////////////////////////////////////////////////////////////////////////
// fc_cons_option - a bitfield
//	0	default
//	1	force (now the default)
//	2	conservative
//	4	do not delete a_bucket
/////////////////////////////////////////////////////////////////////////////

/* to signal the class there is no more data to be added */
void tlshImpl_final(TlshImpl * this, int fc_cons_option)
{
    if (this->lsh_code_valid) {
      fprintf(stderr, "call to final() on a tlsh that is already valid\n");
      return;
    }
    // incoming data must more than or equal to MIN_DATA_LENGTH bytes

    unsigned int q1, q2, q3;
    find_quartile(&q1, &q2, &q3, this->a_bucket);

    // buckets must be more than 50% non-zero
    int nonzero = 0;
    for(unsigned int i=0; i<CODE_SIZE; i++) {
      for(unsigned int j=0; j<4; j++) {
        if (this->a_bucket[4*i + j] > 0) {
          nonzero++;
        }
      }
    }

    for(unsigned int i=0; i<CODE_SIZE; i++) {
        unsigned char h=0;
        for(unsigned int j=0; j<4; j++) {
            unsigned int k = this->a_bucket[4*i + j];
            if( q3 < k ) {
                h += 3 << (j*2);  // leave the optimization j*2 = j<<1 or j*2 = j+j for compiler
            } else if( q2 < k ) {
                h += 2 << (j*2);
            } else if( q1 < k ) {
                h += 1 << (j*2);
	    }
        }
        this->lsh_bin.tmp_code[i] = h;
    }

    this->lsh_bin.Lvalue = l_capturing(this->data_len);
    this->lsh_bin.Q.QR.Q1ratio = (unsigned int) ((float)(q1*100)/(float) q3) % 16;
    this->lsh_bin.Q.QR.Q2ratio = (unsigned int) ((float)(q2*100)/(float) q3) % 16;
    this->lsh_code_valid = 1;
}

void to_hex( unsigned char * psrc, int len, char* pdest )
{
    static unsigned char HexLookup[513]= {
	"000102030405060708090A0B0C0D0E0F"
	"101112131415161718191A1B1C1D1E1F"
	"202122232425262728292A2B2C2D2E2F"
	"303132333435363738393A3B3C3D3E3F"
	"404142434445464748494A4B4C4D4E4F"
	"505152535455565758595A5B5C5D5E5F"
	"606162636465666768696A6B6C6D6E6F"
	"707172737475767778797A7B7C7D7E7F"
	"808182838485868788898A8B8C8D8E8F"
	"909192939495969798999A9B9C9D9E9F"
	"A0A1A2A3A4A5A6A7A8A9AAABACADAEAF"
	"B0B1B2B3B4B5B6B7B8B9BABBBCBDBEBF"
	"C0C1C2C3C4C5C6C7C8C9CACBCCCDCECF"
	"D0D1D2D3D4D5D6D7D8D9DADBDCDDDEDF"
	"E0E1E2E3E4E5E6E7E8E9EAEBECEDEEEF"
	"F0F1F2F3F4F5F6F7F8F9FAFBFCFDFEFF"
    };
    unsigned short* pwHex = (unsigned short*)HexLookup;
	unsigned short* pwDest= (unsigned short*)pdest;

	for (int i=0; i<len; i++ ) {
		*pwDest= pwHex[*psrc];
		pwDest++; psrc++;
	}
	*((unsigned char*)pwDest)= 0;  // terminate the string
}

void from_hex( const char* psrc, int len, unsigned char* pdest )
{
    static unsigned char DecLookup[] = {
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, // gap before first hex digit
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
	0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
	0,1,2,3,4,5,6,7,8,9,       // 0123456789
	0,0,0,0,0,0,0,             // :;<=>?@ (gap)
	10,11,12,13,14,15,         // ABCDEF
	0,0,0,0,0,0,0,0,0,0,0,0,0, // GHIJKLMNOPQRS (gap)
	0,0,0,0,0,0,0,0,0,0,0,0,0, // TUVWXYZ[/]^_` (gap)
	10,11,12,13,14,15          // abcdef
    };

    for (int i=0; i<len; i += 2 ) {
	unsigned d =  DecLookup[*(unsigned char *)(psrc + i)] << 4;
	d |= DecLookup[*(unsigned char *)(psrc + i + 1)];
	*pdest++ = d;
    }
}

unsigned char swap_byte( const unsigned char in )
{
	unsigned char byte = 0;
	byte = ((in & 0xF0) >> 4) & 0x0F;
	byte |= ((in & 0x0F) << 4) & 0xF0;
	return byte;
}

int tlshImpl_fromTlshStr(TlshImpl * this, const char* str)
{
	// Assume that we have 128 Buckets
	int start = 0;
        if (strncmp(str, "T1", 2) == 0) {
		start = 2;
	} else {
		start = 0;
	}
	// Validate input string
	for( int ii=0; ii < INTERNAL_TLSH_STRING_LEN; ii++ ) {
		int i = ii + start;
		if (!(	(str[i] >= '0' && str[i] <= '9') ||
			(str[i] >= 'A' && str[i] <= 'F') ||
			(str[i] >= 'a' && str[i] <= 'f') ))
        	{
			// printf("warning ii=%d str[%d]='%c'\n", ii, i, str[i]);
			return 1;
		}
	}
	int xi = INTERNAL_TLSH_STRING_LEN + start;
	if ((	(str[xi] >= '0' && str[xi] <= '9') ||
		(str[xi] >= 'A' && str[xi] <= 'F') ||
		(str[xi] >= 'a' && str[xi] <= 'f') ))
        {
		// printf("warning xi=%d\n", xi);
		return 1;
	}

	tlshImpl_reset(this);

	lsh_bin_t tmp;
	from_hex( &str[start], INTERNAL_TLSH_STRING_LEN, (unsigned char*)&tmp );

	// Reconstruct checksum, Qrations & lvalue
	for (int k = 0; k < TLSH_CHECKSUM_LEN; k++) {
		this->lsh_bin.checksum[k] = swap_byte(tmp.checksum[k]);
	}
	this->lsh_bin.Lvalue = swap_byte( tmp.Lvalue );
	this->lsh_bin.Q.QB = swap_byte(tmp.Q.QB);
	for( int i=0; i < CODE_SIZE; i++ ){
		this->lsh_bin.tmp_code[i] = (tmp.tmp_code[CODE_SIZE-1-i]);
	}
	this->lsh_code_valid = 1;

	return 0;
}

const char* tlshImpl_hash(TlshImpl * this, char *buffer, unsigned int bufSize, int showvers)
{
    if (bufSize < TLSH_STRING_LEN_REQ + 1) {
        strncpy(buffer, "", bufSize);
        return buffer;
    }
    if (this->lsh_code_valid == 0) {
        strncpy(buffer, "", bufSize);
        return buffer;
    }

    lsh_bin_t tmp;
    for (int k = 0; k < TLSH_CHECKSUM_LEN; k++) {
      tmp.checksum[k] = swap_byte( this->lsh_bin.checksum[k] );
    }
    tmp.Lvalue = swap_byte( this->lsh_bin.Lvalue );
    tmp.Q.QB = swap_byte( this->lsh_bin.Q.QB );
    for( int i=0; i < CODE_SIZE; i++ ){
        tmp.tmp_code[i] = (this->lsh_bin.tmp_code[CODE_SIZE-1-i]);
    }

	if (showvers) {
		buffer[0] = 'T';
		buffer[1] = '0' + showvers;
		to_hex( (unsigned char*)&tmp, sizeof(tmp), &buffer[2]);
	} else {
		to_hex( (unsigned char*)&tmp, sizeof(tmp), buffer);
	}
	return buffer;
}

/* to get the hex-encoded hash code */
const char* tlshImpl_hash_vers(TlshImpl * this, int showvers)
{
    if (this->lsh_code != NULL) {
        // lsh_code has been previously calculated, so just return it
        return this->lsh_code;
    }

    this->lsh_code = malloc(TLSH_STRING_LEN_REQ+1);
    memset(this->lsh_code, 0, TLSH_STRING_LEN_REQ+1);

    return tlshImpl_hash(this, this->lsh_code, TLSH_STRING_LEN_REQ+1, showvers);
}


// compare
int tlshImpl_compare(TlshImpl * this, TlshImpl * other)
{
    return (memcmp( &(this->lsh_bin), &(other->lsh_bin), sizeof(this->lsh_bin)));
}

////////////////////////////////////////////
// the default for these parameters is 12
////////////////////////////////////////////

static int length_mult = 12;
static int qratio_mult = 12;



int tlshImpl_Lvalue(TlshImpl * this)
{
	return(this->lsh_bin.Lvalue);
}
int tlshImpl_Q1ratio(TlshImpl * this)
{
	return(this->lsh_bin.Q.QR.Q1ratio);
}
int tlshImpl_Q2ratio(TlshImpl * this)
{
	return(this->lsh_bin.Q.QR.Q2ratio);
}
int tlshImpl_Checksum(TlshImpl * this, int k)
{
	if ((k >= TLSH_CHECKSUM_LEN) || (k < 0)) {
		return(0);
	}
	return(this->lsh_bin.checksum[k]);
}
int tlshImpl_BucketValue(TlshImpl * this, int bucket)
{
int idx;
int elem;
unsigned char bv;
//  default TLSH
//  #define EFF_BUCKETS         128
//  #define CODE_SIZE           32   // 128 * 2 bits = 32 bytes

	idx	= (CODE_SIZE - (bucket / 4)) - 1;
//	if ((idx < 0) || (idx >= CODE_SIZE)) {
//		printf("error in BucketValue: idx=%d\n", idx);
//		exit(1);
//	}
	elem	= bucket % 4;
	bv = this->lsh_bin.tmp_code[idx];
	int h1	= bv  / 16;
	int h2	= bv  % 16;
	int p1	= h1 / 4;
	int p2	= h1 % 4;
	int p3	= h2 / 4;
	int p4	= h2 % 4;
	if (elem == 0) {
		return(p1);
	}
	if (elem == 1) {
		return(p2);
	}
	if (elem == 2) {
		return(p3);
	}
	return(p4);
}

int tlshImpl_HistogramCount(TlshImpl * this, int bucket)
{
	if (this->a_bucket == NULL)
		return(-1);
	return(this->a_bucket[EFF_BUCKETS - 1 - bucket]);
}

int mod_diff(unsigned int x, unsigned int y, unsigned int R)
{
    int dl = 0;
    int dr = 0;
    if ( y > x ){
        dl = (int)(y - x);
        dr = (int)(x + R - y);
    }else{
        dl = (int)(x - y);
        dr = (int)(y + R - x);
    }
    return (dl > dr ? dr : dl);
}

// Compile and run gen_arr2.cpp to generate bit_pairs_diff_table
static unsigned char bit_pairs_diff_table[][256] = {
{
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20, 18, 19, 20, 24
},
{
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16, 19, 18, 19, 20
},
{
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15, 20, 19, 18, 19
},
{
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14, 24, 20, 19, 18
},
{
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20
},
{
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16
},
{
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15
},
{
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14
},
{
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19
},
{
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15
},
{
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14
},
{
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13
},
{
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
18, 19, 20, 24, 14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18
},
{
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
19, 18, 19, 20, 15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14
},
{
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
20, 19, 18, 19, 16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13
},
{
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
24, 20, 19, 18, 20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12
},
{
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20
},
{
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16
},
{
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15
},
{
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14
},
{
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16
},
{
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12
},
{
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11
},
{
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10
},
{
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15
},
{
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11
},
{
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10
},
{
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9
},
{
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14
},
{
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10
},
{
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9
},
{
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8
},
{
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19
},
{
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15
},
{
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14
},
{
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13
},
{
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15
},
{
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11
},
{
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10
},
{
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9
},
{
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14
},
{
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10
},
{
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9
},
{
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8
},
{
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13
},
{
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9
},
{
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8
},
{
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7
},
{
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20, 18, 19, 20, 24,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18
},
{
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16, 19, 18, 19, 20,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14
},
{
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15, 20, 19, 18, 19,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13
},
{
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14, 24, 20, 19, 18,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12
},
{
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14
},
{
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10
},
{
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9
},
{
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8
},
{
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13
},
{
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9
},
{
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8
},
{
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7
},
{
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
18, 19, 20, 24, 14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12
},
{
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
19, 18, 19, 20, 15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8
},
{
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
20, 19, 18, 19, 16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7
},
{
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
24, 20, 19, 18, 20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6
},
{
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20
},
{
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16
},
{
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15
},
{
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14
},
{
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16
},
{
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12
},
{
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11
},
{
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10
},
{
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15
},
{
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11
},
{
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10
},
{
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9
},
{
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14
},
{
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10
},
{
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9
},
{
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8
},
{
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16
},
{
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12
},
{
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11
},
{
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10
},
{
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12
},
{
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8
},
{
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7
},
{
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6
},
{
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11
},
{
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7
},
{
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6
},
{
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5
},
{
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10
},
{
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6
},
{
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5
},
{
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4
},
{
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15
},
{
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11
},
{
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10
},
{
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9
},
{
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11
},
{
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7
},
{
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6
},
{
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5
},
{
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10
},
{
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6
},
{
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5
},
{
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4
},
{
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9
},
{
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5
},
{
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4
},
{
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3
},
{
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14
},
{
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10
},
{
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9
},
{
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8
},
{
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10
},
{
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6
},
{
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5
},
{
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4
},
{
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9
},
{
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5
},
{
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4
},
{
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3
},
{
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8
},
{
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4
},
{
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3
},
{
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2
},
{
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19
},
{
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15
},
{
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14
},
{
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13
},
{
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15
},
{
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11
},
{
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10
},
{
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9
},
{
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14
},
{
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10
},
{
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9
},
{
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8
},
{
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13
},
{
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9
},
{
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8
},
{
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7
},
{
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15
},
{
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11
},
{
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10
},
{
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9
},
{
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11
},
{
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7
},
{
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6
},
{
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5
},
{
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10
},
{
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6
},
{
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5
},
{
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4
},
{
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9
},
{
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5
},
{
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4
},
{
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3
},
{
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14
},
{
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10
},
{
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9
},
{
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8
},
{
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10
},
{
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6
},
{
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5
},
{
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4
},
{
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9
},
{
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5
},
{
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4
},
{
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3
},
{
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8
},
{
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4
},
{
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3
},
{
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2
},
{
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13
},
{
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9
},
{
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8
},
{
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7
},
{
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9
},
{
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5
},
{
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4
},
{
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3
},
{
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8
},
{
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4
},
{
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3
},
{
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2
},
{
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7
},
{
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3
},
{
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2
},
{
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1
},
{
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20, 18, 19, 20, 24,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18
},
{
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16, 19, 18, 19, 20,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14
},
{
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15, 20, 19, 18, 19,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13
},
{
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14, 24, 20, 19, 18,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12
},
{
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14
},
{
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10
},
{
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9
},
{
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8
},
{
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13
},
{
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9
},
{
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8
},
{
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7
},
{
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
18, 19, 20, 24, 14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12
},
{
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
19, 18, 19, 20, 15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8
},
{
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
20, 19, 18, 19, 16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7
},
{
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
24, 20, 19, 18, 20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6
},
{
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14
},
{
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10
},
{
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9
},
{
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8
},
{
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10
},
{
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6
},
{
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5
},
{
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4
},
{
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9
},
{
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5
},
{
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4
},
{
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3
},
{
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8
},
{
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4
},
{
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3
},
{
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2
},
{
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13
},
{
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9
},
{
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8
},
{
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7
},
{
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9
},
{
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5
},
{
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4
},
{
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3
},
{
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8
},
{
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4
},
{
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3
},
{
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2
},
{
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7
},
{
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3
},
{
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2
},
{
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1
},
{
12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20, 18, 19, 20, 24,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16, 14, 15, 16, 20,
4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12, 10, 11, 12, 16,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15, 13, 14, 15, 19,
3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11, 9, 10, 11, 15,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14, 12, 13, 14, 18,
2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10, 8, 9, 10, 14,
1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9, 7, 8, 9, 13,
0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8, 6, 7, 8, 12
},
{
13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16, 19, 18, 19, 20,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12, 15, 14, 15, 16,
5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8, 11, 10, 11, 12,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11, 14, 13, 14, 15,
4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7, 10, 9, 10, 11,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10, 13, 12, 13, 14,
3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6, 9, 8, 9, 10,
2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5, 8, 7, 8, 9,
1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4, 7, 6, 7, 8
},
{
14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15, 20, 19, 18, 19,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11, 16, 15, 14, 15,
6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7, 12, 11, 10, 11,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10, 15, 14, 13, 14,
5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6, 11, 10, 9, 10,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9, 14, 13, 12, 13,
4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5, 10, 9, 8, 9,
3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4, 9, 8, 7, 8,
2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3, 8, 7, 6, 7
},
{
18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14, 24, 20, 19, 18,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10, 20, 16, 15, 14,
10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6, 16, 12, 11, 10,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9, 19, 15, 14, 13,
9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5, 15, 11, 10, 9,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8, 18, 14, 13, 12,
8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4, 14, 10, 9, 8,
7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3, 13, 9, 8, 7,
6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2, 12, 8, 7, 6
},
{
13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19, 14, 15, 16, 20,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15, 10, 11, 12, 16,
5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11, 6, 7, 8, 12,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14, 9, 10, 11, 15,
4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10, 5, 6, 7, 11,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13, 8, 9, 10, 14,
3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9, 4, 5, 6, 10,
2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8, 3, 4, 5, 9,
1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7, 2, 3, 4, 8
},
{
14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15, 15, 14, 15, 16,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11, 11, 10, 11, 12,
6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7, 7, 6, 7, 8,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10, 10, 9, 10, 11,
5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6, 6, 5, 6, 7,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9, 9, 8, 9, 10,
4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5, 5, 4, 5, 6,
3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4, 4, 3, 4, 5,
2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3, 3, 2, 3, 4
},
{
15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14, 16, 15, 14, 15,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10, 12, 11, 10, 11,
7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6, 8, 7, 6, 7,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9, 11, 10, 9, 10,
6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5, 7, 6, 5, 6,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8, 10, 9, 8, 9,
5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4, 6, 5, 4, 5,
4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3, 5, 4, 3, 4,
3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2, 4, 3, 2, 3
},
{
19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13, 20, 16, 15, 14,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9, 16, 12, 11, 10,
11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5, 12, 8, 7, 6,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8, 15, 11, 10, 9,
10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4, 11, 7, 6, 5,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7, 14, 10, 9, 8,
9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3, 10, 6, 5, 4,
8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2, 9, 5, 4, 3,
7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1, 8, 4, 3, 2
},
{
14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18, 13, 14, 15, 19,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14, 9, 10, 11, 15,
6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10, 5, 6, 7, 11,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13, 8, 9, 10, 14,
5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9, 4, 5, 6, 10,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12, 7, 8, 9, 13,
4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8, 3, 4, 5, 9,
3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7, 2, 3, 4, 8,
2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6, 1, 2, 3, 7
},
{
15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14, 14, 13, 14, 15,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10, 10, 9, 10, 11,
7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6, 6, 5, 6, 7,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9, 9, 8, 9, 10,
6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5, 5, 4, 5, 6,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8, 8, 7, 8, 9,
5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4, 4, 3, 4, 5,
4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3, 3, 2, 3, 4,
3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2, 2, 1, 2, 3
},
{
16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13, 15, 14, 13, 14,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9, 11, 10, 9, 10,
8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5, 7, 6, 5, 6,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8, 10, 9, 8, 9,
7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4, 6, 5, 4, 5,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7, 9, 8, 7, 8,
6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3, 5, 4, 3, 4,
5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2, 4, 3, 2, 3,
4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1, 3, 2, 1, 2
},
{
20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12, 19, 15, 14, 13,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8, 15, 11, 10, 9,
12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4, 11, 7, 6, 5,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7, 14, 10, 9, 8,
11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3, 10, 6, 5, 4,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6, 13, 9, 8, 7,
10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2, 9, 5, 4, 3,
9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1, 8, 4, 3, 2,
8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0, 7, 3, 2, 1
},
{
18, 19, 20, 24, 14, 15, 16, 20, 13, 14, 15, 19, 12, 13, 14, 18,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
14, 15, 16, 20, 10, 11, 12, 16, 9, 10, 11, 15, 8, 9, 10, 14,
10, 11, 12, 16, 6, 7, 8, 12, 5, 6, 7, 11, 4, 5, 6, 10,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
13, 14, 15, 19, 9, 10, 11, 15, 8, 9, 10, 14, 7, 8, 9, 13,
9, 10, 11, 15, 5, 6, 7, 11, 4, 5, 6, 10, 3, 4, 5, 9,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
12, 13, 14, 18, 8, 9, 10, 14, 7, 8, 9, 13, 6, 7, 8, 12,
8, 9, 10, 14, 4, 5, 6, 10, 3, 4, 5, 9, 2, 3, 4, 8,
7, 8, 9, 13, 3, 4, 5, 9, 2, 3, 4, 8, 1, 2, 3, 7,
6, 7, 8, 12, 2, 3, 4, 8, 1, 2, 3, 7, 0, 1, 2, 6
},
{
19, 18, 19, 20, 15, 14, 15, 16, 14, 13, 14, 15, 13, 12, 13, 14,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
15, 14, 15, 16, 11, 10, 11, 12, 10, 9, 10, 11, 9, 8, 9, 10,
11, 10, 11, 12, 7, 6, 7, 8, 6, 5, 6, 7, 5, 4, 5, 6,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
14, 13, 14, 15, 10, 9, 10, 11, 9, 8, 9, 10, 8, 7, 8, 9,
10, 9, 10, 11, 6, 5, 6, 7, 5, 4, 5, 6, 4, 3, 4, 5,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
13, 12, 13, 14, 9, 8, 9, 10, 8, 7, 8, 9, 7, 6, 7, 8,
9, 8, 9, 10, 5, 4, 5, 6, 4, 3, 4, 5, 3, 2, 3, 4,
8, 7, 8, 9, 4, 3, 4, 5, 3, 2, 3, 4, 2, 1, 2, 3,
7, 6, 7, 8, 3, 2, 3, 4, 2, 1, 2, 3, 1, 0, 1, 2
},
{
20, 19, 18, 19, 16, 15, 14, 15, 15, 14, 13, 14, 14, 13, 12, 13,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
16, 15, 14, 15, 12, 11, 10, 11, 11, 10, 9, 10, 10, 9, 8, 9,
12, 11, 10, 11, 8, 7, 6, 7, 7, 6, 5, 6, 6, 5, 4, 5,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
15, 14, 13, 14, 11, 10, 9, 10, 10, 9, 8, 9, 9, 8, 7, 8,
11, 10, 9, 10, 7, 6, 5, 6, 6, 5, 4, 5, 5, 4, 3, 4,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
14, 13, 12, 13, 10, 9, 8, 9, 9, 8, 7, 8, 8, 7, 6, 7,
10, 9, 8, 9, 6, 5, 4, 5, 5, 4, 3, 4, 4, 3, 2, 3,
9, 8, 7, 8, 5, 4, 3, 4, 4, 3, 2, 3, 3, 2, 1, 2,
8, 7, 6, 7, 4, 3, 2, 3, 3, 2, 1, 2, 2, 1, 0, 1
},
{
24, 20, 19, 18, 20, 16, 15, 14, 19, 15, 14, 13, 18, 14, 13, 12,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
20, 16, 15, 14, 16, 12, 11, 10, 15, 11, 10, 9, 14, 10, 9, 8,
16, 12, 11, 10, 12, 8, 7, 6, 11, 7, 6, 5, 10, 6, 5, 4,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
19, 15, 14, 13, 15, 11, 10, 9, 14, 10, 9, 8, 13, 9, 8, 7,
15, 11, 10, 9, 11, 7, 6, 5, 10, 6, 5, 4, 9, 5, 4, 3,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
18, 14, 13, 12, 14, 10, 9, 8, 13, 9, 8, 7, 12, 8, 7, 6,
14, 10, 9, 8, 10, 6, 5, 4, 9, 5, 4, 3, 8, 4, 3, 2,
13, 9, 8, 7, 9, 5, 4, 3, 8, 4, 3, 2, 7, 3, 2, 1,
12, 8, 7, 6, 8, 4, 3, 2, 7, 3, 2, 1, 6, 2, 1, 0
}
};


int h_distance( int len, const unsigned char x[], const unsigned char y[])
{
	int diff = 0;

/* #ifdef TLSH_DISTANCE_PARAMETERS */
/* 	if (test_distance) { */
/* 		for (int i=0; i<len; i++) { */
/* 			int dist2 = byte_diff( x[i], y[i] ); */
/* 			// printf("warning x[%d]=%d y[%d]=%d dist2=%d\n", i, x[i], i, y[i], dist2); */
/* 			if ( (hist_diff1_add == 1) && (hist_diff2_add == 2) && (hist_diff3_add == 6) ) { */
/* 				int dist1 = bit_pairs_diff_table[ x[i] ][ y[i] ]; */
/* 				if (dist1 != dist2) { */
/* 					printf("warning x[%d]=%d y[%d]=%d dist1=%d dist2=%d\n", i, x[i], i, y[i], dist1, dist2); */
/* 				} */
/* 			} */
/* 			diff += dist2; */
/* 		} */
/* 		return diff; */
/* 	} */
/* #endif */
	for (int i=0; i<len; i++) {
		diff += bit_pairs_diff_table[ x[i] ][ y[i] ];
	}
	return diff;
}

int tlshImpl_totalDiff(TlshImpl * this, const TlshImpl * other, int len_diff)
{
    int diff = 0;

    if (len_diff) {
        int ldiff = mod_diff( this->lsh_bin.Lvalue, other->lsh_bin.Lvalue, RANGE_LVALUE);
        if ( ldiff == 0 )
            diff = 0;
        else if ( ldiff == 1 )
            diff = 1;
        else
           diff += ldiff*length_mult;
    }

    int q1diff = mod_diff( this->lsh_bin.Q.QR.Q1ratio, other->lsh_bin.Q.QR.Q1ratio, RANGE_QRATIO);
    if ( q1diff <= 1 )
        diff += q1diff;
    else
        diff += (q1diff-1)*qratio_mult;

    int q2diff = mod_diff( this->lsh_bin.Q.QR.Q2ratio, other->lsh_bin.Q.QR.Q2ratio, RANGE_QRATIO);
    if ( q2diff <= 1)
        diff += q2diff;
    else
        diff += (q2diff-1)*qratio_mult;

    for (int k = 0; k < TLSH_CHECKSUM_LEN; k++) {
      if (this->lsh_bin.checksum[k] != other->lsh_bin.checksum[k] ) {
        diff ++;
        break;
      }
    }

    diff += h_distance( CODE_SIZE, this->lsh_bin.tmp_code, other->lsh_bin.tmp_code );

    return (diff);
}



#define SWAP_UINT(x,y) do {\
    unsigned int int_tmp = (x);  \
    (x) = (y); \
    (y) = int_tmp; } while(0)

void find_quartile(unsigned int *q1, unsigned int *q2, unsigned int *q3, const unsigned int * a_bucket)
{
    unsigned int bucket_copy[EFF_BUCKETS], short_cut_left[EFF_BUCKETS], short_cut_right[EFF_BUCKETS], spl=0, spr=0;
    unsigned int p1 = EFF_BUCKETS/4-1;
    unsigned int p2 = EFF_BUCKETS/2-1;
    unsigned int p3 = EFF_BUCKETS-EFF_BUCKETS/4-1;
    unsigned int end = EFF_BUCKETS-1;

    for(unsigned int i=0; i<=end; i++) {
        bucket_copy[i] = a_bucket[i];
    }

    for( unsigned int l=0, r=end; ; ) {
        unsigned int ret = partition( bucket_copy, l, r );
        if( ret > p2 ) {
            r = ret - 1;
            short_cut_right[spr] = ret;
            spr++;
        } else if( ret < p2 ){
            l = ret + 1;
            short_cut_left[spl] = ret;
            spl++;
        } else {
            *q2 = bucket_copy[p2];
            break;
        }
    }

    short_cut_left[spl] = p2-1;
    short_cut_right[spr] = p2+1;

    for( unsigned int i=0, l=0; i<=spl; i++ ) {
        unsigned int r = short_cut_left[i];
        if( r > p1 ) {
            for( ; ; ) {
                unsigned int ret = partition( bucket_copy, l, r );
                if( ret > p1 ) {
                    r = ret-1;
                } else if( ret < p1 ) {
                    l = ret+1;
                } else {
                    *q1 = bucket_copy[p1];
                    break;
                }
            }
            break;
        } else if( r < p1 ) {
            l = r;
        } else {
            *q1 = bucket_copy[p1];
            break;
        }
    }

    for( unsigned int i=0, r=end; i<=spr; i++ ) {
        unsigned int l = short_cut_right[i];
        if( l < p3 ) {
            for( ; ; ) {
                unsigned int ret = partition( bucket_copy, l, r );
                if( ret > p3 ) {
                    r = ret-1;
                } else if( ret < p3 ) {
                    l = ret+1;
                } else {
                    *q3 = bucket_copy[p3];
                    break;
                }
            }
            break;
        } else if( l > p3 ) {
            r = l;
        } else {
            *q3 = bucket_copy[p3];
            break;
        }
    }

}

unsigned int partition(unsigned int * buf, unsigned int left, unsigned int right)
{
    if( left == right ) {
        return left;
    }
    if( left+1 == right ) {
        if( buf[left] > buf[right] ) {
            SWAP_UINT( buf[left], buf[right] );
        }
        return left;
    }

    unsigned int ret = left, pivot = (left + right)>>1;

    unsigned int val = buf[pivot];

    buf[pivot] = buf[right];
    buf[right] = val;

    for( unsigned int i = left; i < right; i++ ) {
        if( buf[i] < val ) {
            SWAP_UINT( buf[ret], buf[i] );
            ret++;
        }
    }
    buf[right] = buf[ret];
    buf[ret] = val;

    return ret;
}
