#ifndef __PACKEDRR_H__
#define __PACKEDRR_H__

#include <resource_record.h>
#include <rrfrag.h>
#include <stdbool.h>

typedef union RR {
  ResourceRecord *rr;
  RRFrag *rrfrag;
} RR;

typedef struct PackedRR {
  bool isRRFrag;
  RR data;
} PackedRR;

// PackedRR functions. A PackedRR is used to store a Resource record and RRFRAG
// in the same place since they are shaped slightly differently.

// in should either be a ResourceRecord or an RRFrag
int packedrr_create(void *in, PackedRR **out);

int packedrr_clone(PackedRR *in, PackedRR **out);

int packedrr_destroy(PackedRR **prr);

int packedrr_to_bytes(PackedRR *in, unsigned char **out, size_t *in_len);

int packedrr_from_bytes(unsigned char *in, size_t in_len,
                        size_t *bytes_processed, bool is_dns_message_query,
                        PackedRR **out);

char *packedrr_to_string(PackedRR *prr);

bool is_packedrr_equal(PackedRR *lhs, PackedRR *rhs);

#endif
