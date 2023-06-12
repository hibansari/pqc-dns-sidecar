#ifndef __DNS_MESSAGE_H__
#define __DNS_MESSAGE_H__

#include <packedrr.h>
#include <question.h>
#include <resource_record.h>
#include <rrfrag.h>
#include <stdbool.h>

#define DNSHEADERSIZE 12

typedef struct DNSMessage {
  uint16_t identification;
  uint16_t flags;
  uint16_t qdcount;
  uint16_t ancount;
  uint16_t nscount;
  uint16_t arcount;
  Question **question_section;
  PackedRR **answers_section;
  PackedRR **authoritative_section;
  PackedRR **additional_section;
} DNSMessage;

int dns_message_create(DNSMessage **out, uint16_t identification,
                       uint16_t flags, uint16_t qdcount, uint16_t ancount,
                       uint16_t nscount, uint16_t arcount, Question **questions,
                       PackedRR **answers_section,
                       PackedRR **authoritative_section,
                       PackedRR **additional_section);

int dns_message_clone(DNSMessage *in, DNSMessage **out);

int dns_message_destroy(DNSMessage **msg);

int dns_message_to_bytes(DNSMessage *in, unsigned char **out, size_t *out_len);

int dns_message_from_bytes(unsigned char *in, size_t in_len, DNSMessage **out);

char *dns_message_to_string(DNSMessage *in);

bool is_dns_message(unsigned char *in, size_t in_len);

bool is_dns_message_query(DNSMessage *in);

bool is_dns_message_contains_rrfrag(DNSMessage *msg);

bool is_dns_message_equal(DNSMessage *lhs, DNSMessage *rhs);

#endif