#ifndef __RESOURCE_RECORD_H__
#define __RESOURCE_RECORD_H__

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct ResourceRecord {
  char *name;
  uint16_t type;
  uint16_t clas;
  uint32_t ttl;
  uint16_t rdsize;
  unsigned char *rdata;
  // These need to be last so we maintain the byte structure of Resource Records
  // and RRFrags since we cast between them in a few places
  unsigned char *name_bytes;
  size_t name_byte_len;
} ResourceRecord;

int resource_record_create(ResourceRecord **out, char *name,
                           unsigned char *name_bytes, size_t name_byte_len,
                           uint16_t type, uint16_t clas, uint32_t ttl,
                           uint16_t rdsize, unsigned char *rdata);

int resource_record_clone(ResourceRecord *in, ResourceRecord **out);

int resource_record_destroy(ResourceRecord **rr);

int resource_record_to_bytes(ResourceRecord *in, unsigned char **out,
                             size_t *out_len);

int resource_record_from_bytes(unsigned char *in, size_t in_len,
                               size_t *bytes_processed, ResourceRecord **out);

char *resource_record_to_string(ResourceRecord *rr);

bool is_resource_record_equal(ResourceRecord *lhs, ResourceRecord *rhs);

int dns_name_from_bytes(unsigned char *in, char **name, size_t *name_len,
                        size_t *bytes_processed, size_t in_len);

int dns_name_to_bytes(char *name, size_t name_len, unsigned char **out,
                      size_t *out_len);

#endif
