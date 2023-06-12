#ifndef __RFRAG_H__
#define __RFRAG_H__

#define RRFRAG                                                                 \
  108 // This is just after the "experiemntal" ids and is currently unused

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct RRFrag {
  char *name;
  uint16_t
      type; // Should always be RRFRAG but keeping so it's consistent with RRs
  uint16_t fragsize;
  uint32_t curidx;
  uint32_t rrsize;
  uint16_t rrid;
  unsigned char *fragdata;
} RRFrag;

int rrfrag_create(RRFrag **out, uint16_t fragsize, uint32_t curidx,
                  uint32_t rrsize, uint16_t rrid, unsigned char *fragdata);

int rrfrag_clone(RRFrag *in, RRFrag **out);

int rrfrag_destroy(RRFrag **rrfrag);

int rrfrag_to_bytes(RRFrag *in, unsigned char **out, size_t *out_len);

int rrfrag_from_bytes(unsigned char *in, size_t in_len, size_t *bytes_processed,
                      bool is_dns_message_query, RRFrag **out);

char *rrfrag_to_string(RRFrag *rrfrag);

// TODO dangerous, add length checks
bool is_rrfrag(unsigned char *in);

bool is_rrfrag_equal(RRFrag *lhs, RRFrag *rhs);

#endif