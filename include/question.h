#ifndef __QUESTION_H__
#define __QUESTION_H__

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct Question {
  char *qname;
  uint16_t qtype;
  uint16_t qclass;
} Question;

int question_create(Question **out, char *qname, uint16_t qtype,
                    uint16_t qclass);

int question_clone(Question *in, Question **out);

int question_destroy(Question **question);

int question_to_bytes(Question *in, unsigned char **out, size_t *out_len);

int question_from_bytes(unsigned char *in, size_t in_len,
                        size_t *bytes_processed, Question **out);

char *question_to_string(Question *q);

bool is_question_equal(Question *lhs, Question *rhs);

#endif
