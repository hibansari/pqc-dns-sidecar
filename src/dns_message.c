#include <arpa/inet.h>
#include <assert.h>
#include <dns_message.h>
#include <packedrr.h>
#include <question.h>
#include <resource_record.h>
#include <rrfrag.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int dns_message_destroy(DNSMessage **msg) {
  if (msg == NULL)
    return 0;
  if (*msg == NULL)
    return 0;
  DNSMessage *m = *msg;
  for (uint16_t i = 0; i < m->qdcount; i++) {
    question_destroy((m->question_section + i));
  }
  for (uint16_t i = 0; i < m->ancount; i++) {
    packedrr_destroy((m->answers_section + i));
  }
  for (uint16_t i = 0; i < m->nscount; i++) {
    packedrr_destroy((m->authoritative_section + i));
  }
  for (uint16_t i = 0; i < m->arcount; i++) {
    packedrr_destroy((m->additional_section + i));
  }
  free(m);
  *msg = NULL;
  return 0;
}

#define DNS_MESSAGE_QR_FLAG 0x8000U
#define DNS_MESSAGE_TC_FLAG 0x0200U
#define DNS_MESSAGE_RCODE_MASK 0x000fU

bool is_dns_message_query(DNSMessage *in) {
  if (in == NULL)
    return false;
  return ((in->flags & DNS_MESSAGE_QR_FLAG) == 0) &&
         ((in->flags & DNS_MESSAGE_RCODE_MASK) == 0);
}

bool is_truncated(DNSMessage *in) {
  if (in == NULL)
    return false;
  return ((in->flags & DNS_MESSAGE_TC_FLAG) != 0);
}

int dns_message_create(DNSMessage **out, uint16_t identification,
                       uint16_t flags, uint16_t qdcount, uint16_t ancount,
                       uint16_t nscount, uint16_t arcount, Question **questions,
                       PackedRR **answers_section,
                       PackedRR **authoritative_section,
                       PackedRR **additional_section) {
  DNSMessage *msg = malloc(sizeof(DNSMessage));
  msg->identification = identification;
  msg->flags = flags;
  msg->qdcount = qdcount;
  msg->ancount = ancount;
  msg->nscount = nscount;
  msg->arcount = arcount;
  if (qdcount > 0) {
    msg->question_section = malloc(sizeof(Question *) * qdcount);
  }
  for (uint16_t i = 0; i < qdcount; i++) {
    question_clone(questions[i], msg->question_section + i);
  }
  if (ancount > 0) {
    msg->answers_section = malloc(sizeof(PackedRR *) * ancount);
  }
  for (uint16_t i = 0; i < ancount; i++) {
    packedrr_clone(answers_section[i], msg->answers_section + i);
  }
  if (nscount > 0) {
    msg->authoritative_section = malloc(sizeof(PackedRR *) * nscount);
  }
  for (uint16_t i = 0; i < nscount; i++) {
    packedrr_clone(authoritative_section[i], msg->authoritative_section + i);
  }
  if (arcount > 0) {
    msg->additional_section = malloc(sizeof(PackedRR *) * arcount);
  }
  for (uint16_t i = 0; i < arcount; i++) {
    packedrr_clone(additional_section[i], msg->additional_section + i);
  }
  *out = msg;
  return 0;
}

int dns_message_from_bytes(unsigned char *in, size_t in_len, DNSMessage **out) {
  int rc;
  unsigned char *cur_pos;
  size_t bytes_processed;
  uint16_t identification;
  uint16_t flags;
  uint16_t qdcount;
  uint16_t qddone = 0;
  uint16_t ancount;
  uint16_t andone = 0;
  uint16_t nscount;
  uint16_t nsdone = 0;
  uint16_t arcount;
  uint16_t ardone = 0;
  Question **questions;
  PackedRR **answer_section;
  PackedRR **authoritative_section;
  PackedRR **additional_section;
  size_t original_len = in_len;
  cur_pos = in;
  identification = *(uint16_t *)cur_pos;
  identification = ntohs(identification);
  cur_pos += 2;
  in_len -= 2;

  flags = *(uint16_t *)cur_pos;
  flags = ntohs(flags);
  cur_pos += 2;
  in_len -= 2;

  qdcount = *(uint16_t *)cur_pos;
  qdcount = ntohs(qdcount);
  cur_pos += 2;
  in_len -= 2;

  ancount = *(uint16_t *)cur_pos;
  ancount = ntohs(ancount);
  cur_pos += 2;
  in_len -= 2;

  nscount = *(uint16_t *)cur_pos;
  nscount = ntohs(nscount);
  cur_pos += 2;
  in_len -= 2;

  arcount = *(uint16_t *)cur_pos;
  arcount = ntohs(arcount);
  cur_pos += 2;
  in_len -= 2;

  bool query = ((flags & DNS_MESSAGE_QR_FLAG) == 0) &&
               ((flags & DNS_MESSAGE_RCODE_MASK) == 0);
  size_t bytes_so_far = 0;
  if (qdcount > 0) {
    questions = malloc(sizeof(Question *) * qdcount);
    memset(questions, 0, sizeof(Question *) * qdcount);
  }
  for (uint16_t i = 0; i < qdcount; i++) {
    rc = question_from_bytes(cur_pos, in_len, &bytes_processed, &questions[i]);
    qddone++;
    if (bytes_processed == 0 || rc != 0) {
      printf("bytes_processed == %lu\n", bytes_processed);
      for (int i = 0; i < original_len; i++) {
        printf("%hhu\n", in[i]);
      }
      fflush(stdout);
      assert(false);
      goto err;
    }
    cur_pos += bytes_processed;
    bytes_so_far += bytes_processed;
    in_len -= bytes_processed;
  }
  if (ancount > 0) {
    answer_section = malloc(sizeof(PackedRR *) * ancount);
  }
  for (uint16_t i = 0; i < ancount; i++) {
    rc = packedrr_from_bytes(cur_pos, in_len, &bytes_processed, query,
                             &answer_section[i]);
    andone++;
    if (bytes_processed == 0 || rc != 0) {
      printf("bytes_processed == %lu\n", bytes_processed);
      for (int i = 0; i < original_len; i++) {
        printf("%hhu\n", in[i]);
      }
      fflush(stdout);
      assert(false);
      goto err;
    }
    cur_pos += bytes_processed;
    bytes_so_far += bytes_processed;
    in_len -= bytes_processed;
  }

  if (nscount > 0) {
    authoritative_section = malloc(sizeof(PackedRR *) * nscount);
  }
  for (uint16_t i = 0; i < nscount; i++) {
    rc = packedrr_from_bytes(cur_pos, in_len, &bytes_processed, query,
                             &authoritative_section[i]);
    nsdone++;
    if (bytes_processed == 0 || rc != 0) {
      printf("bytes_processed: %ld rc: %u\n", bytes_processed, rc);
      for (int i = 0; i < original_len; i++) {
        printf("%hhu\n", in[i]);
      }
      fflush(stdout);
      assert(false);
      goto err;
    }
    cur_pos += bytes_processed;
    bytes_so_far += bytes_processed;
    in_len -= bytes_processed;
  }

  if (arcount > 0) {
    additional_section = malloc(sizeof(PackedRR *) * arcount);
  }
  for (uint16_t i = 0; i < arcount; i++) {
    rc = packedrr_from_bytes(cur_pos, in_len, &bytes_processed, query,
                             &additional_section[i]);
    ardone++;
    if (bytes_processed == 0 || rc != 0) {
      printf("bytes_processed == %lu\n", bytes_processed);
      for (int i = 0; i < original_len; i++) {
        printf("%hhu\n", in[i]);
      }
      fflush(stdout);
      assert(false);
      goto err;
    }
    cur_pos += bytes_processed;
    bytes_so_far += bytes_processed;
    in_len -= bytes_processed;
  }
  rc = dns_message_create(out, identification, flags, qdcount, ancount, nscount,
                          arcount, questions, answer_section,
                          authoritative_section, additional_section);
  if (rc != 0) {
    dns_message_destroy(out);
    assert(false);
    goto end;
  }
err:
  if (rc != 0) {
    for (size_t i = 0; i < qddone; i++) {
      question_destroy(&questions[i]);
    }
    for (size_t i = 0; i < andone; i++) {
      packedrr_destroy(&answer_section[i]);
    }
    for (size_t i = 0; i < nsdone; i++) {
      packedrr_destroy(&authoritative_section[i]);
    }
    for (size_t i = 0; i < ardone; i++) {
      packedrr_destroy(&additional_section[i]);
    }
  }
end:
  return rc;
}

int dns_message_to_bytes(DNSMessage *in, unsigned char **out, size_t *out_len) {
  int rc = 0;
  unsigned char *cur_pos;
  uint16_t identification;
  uint16_t flags;
  uint16_t qdcount;
  uint16_t ancount;
  uint16_t nscount;
  uint16_t arcount;
  uint16_t header_size = DNSHEADERSIZE;
  unsigned char **question_bytes = NULL;
  size_t *question_byte_lens = NULL;
  unsigned char **answer_bytes = NULL;
  size_t *answer_byte_lens = NULL;
  unsigned char **authoritative_bytes = NULL;
  size_t *authoritative_byte_lens = NULL;
  unsigned char **additional_bytes = NULL;
  size_t *additional_byte_lens = NULL;

  size_t total_bytes_needed = header_size;

  identification = htons(in->identification);
  flags = htons(in->flags);
  qdcount = htons(in->qdcount);
  ancount = htons(in->ancount);
  nscount = htons(in->nscount);
  arcount = htons(in->arcount);

  if (in->qdcount > 0) {
    question_bytes = malloc(sizeof(unsigned char *) * in->qdcount);
    if (question_bytes == NULL) {
      rc = -1;
      goto end;
    }
    question_byte_lens = calloc(in->qdcount, sizeof(size_t));
    if (question_byte_lens == NULL) {
      free(question_bytes);
      rc = -1;
      goto end;
    }
  }
  for (size_t i = 0; i < in->qdcount; i++) {
    rc = question_to_bytes(in->question_section[i], question_bytes + i,
                           question_byte_lens + i);
    if (rc != 0) {
      free(question_bytes);
      free(question_byte_lens);
      goto question_free;
    }
  }

  if (in->ancount > 0) {
    answer_bytes = malloc(sizeof(unsigned char *) * in->ancount);
    if (answer_bytes == NULL) {
      rc = -1;
      goto question_free;
    }
    answer_byte_lens = calloc(in->ancount, sizeof(size_t));
    if (answer_byte_lens == NULL) {
      free(answer_bytes);
      rc = -1;
      goto question_free;
    }
  }
  for (size_t i = 0; i < in->ancount; i++) {
    rc = packedrr_to_bytes(in->answers_section[i], answer_bytes + i,
                           answer_byte_lens + i);
    if (rc != 0) {
      goto answer_free;
    }
  }

  if (in->nscount > 0) {
    authoritative_bytes = malloc(sizeof(unsigned char *) * in->nscount);
    if (authoritative_bytes == NULL) {
      rc = -1;
      goto answer_free;
    }
    authoritative_byte_lens = calloc(in->nscount, sizeof(size_t));
    if (authoritative_byte_lens == NULL) {
      free(authoritative_bytes);
      rc = -1;
      goto answer_free;
    }
  }
  for (size_t i = 0; i < in->nscount; i++) {
    rc =
        packedrr_to_bytes(in->authoritative_section[i], authoritative_bytes + i,
                          authoritative_byte_lens + i);
    if (rc != 0) {
      goto authoritative_free;
    }
  }

  if (in->arcount > 0) {
    additional_bytes = malloc(sizeof(unsigned char *) * in->arcount);
    if (additional_bytes == NULL) {
      rc = -1;
      goto authoritative_free;
    }
    additional_byte_lens = calloc(in->arcount, sizeof(size_t));
    if (additional_byte_lens == NULL) {
      free(additional_bytes);
      rc = -1;
      goto authoritative_free;
    }
  }
  for (size_t i = 0; i < in->arcount; i++) {
    rc = packedrr_to_bytes(in->additional_section[i], additional_bytes + i,
                           additional_byte_lens + i);
    if (rc != 0) {
      goto additional_free;
    }
  }

  // figure out how much space we actually need...
  for (size_t i = 0; i < in->qdcount; i++) {
    total_bytes_needed += question_byte_lens[i];
  }
  for (size_t i = 0; i < in->ancount; i++) {
    total_bytes_needed += answer_byte_lens[i];
  }
  for (size_t i = 0; i < in->nscount; i++) {
    total_bytes_needed += authoritative_byte_lens[i];
  }
  for (size_t i = 0; i < in->arcount; i++) {
    total_bytes_needed += additional_byte_lens[i];
    printf("additional add: %lu\n", additional_byte_lens[i]);
  }
  *out = malloc(sizeof(unsigned char) * total_bytes_needed);
  if (*out == NULL) {
    rc = -1;
    goto additional_free;
  }

  // header
  cur_pos = *out;
  memcpy(cur_pos, &identification, 2);
  cur_pos += 2;
  memcpy(cur_pos, &flags, 2);
  cur_pos += 2;
  memcpy(cur_pos, &qdcount, 2);
  cur_pos += 2;
  memcpy(cur_pos, &ancount, 2);
  cur_pos += 2;
  memcpy(cur_pos, &nscount, 2);
  cur_pos += 2;
  memcpy(cur_pos, &arcount, 2);
  cur_pos += 2;

  // Question section
  for (size_t i = 0; i < in->qdcount; i++) {
    memcpy(cur_pos, question_bytes[i], question_byte_lens[i]);
    cur_pos += question_byte_lens[i];
  }

  // Answer section
  for (size_t i = 0; i < in->ancount; i++) {
    memcpy(cur_pos, answer_bytes[i], answer_byte_lens[i]);
    cur_pos += answer_byte_lens[i];
  }

  // Authoritative section
  for (size_t i = 0; i < in->nscount; i++) {
    memcpy(cur_pos, authoritative_bytes[i], authoritative_byte_lens[i]);
    cur_pos += authoritative_byte_lens[i];
  }

  // additional section
  for (size_t i = 0; i < in->arcount; i++) {
    memcpy(cur_pos, additional_bytes[i], additional_byte_lens[i]);
    cur_pos += additional_byte_lens[i];
  }

  *out_len = total_bytes_needed;
additional_free:
  for (size_t i = 0; i < in->arcount; i++) {
    free(additional_bytes[i]);
  }
  if (additional_bytes != NULL) {
    free(additional_bytes);
  }
  if (additional_byte_lens != NULL) {
    free(additional_byte_lens);
  }

authoritative_free:
  for (size_t i = 0; i < in->nscount; i++) {
    free(authoritative_bytes[i]);
  }
  if (authoritative_bytes != NULL) {
    free(authoritative_bytes);
  }
  if (authoritative_byte_lens != NULL) {
    free(authoritative_byte_lens);
  }

answer_free:
  for (size_t i = 0; i < in->ancount; i++) {
    free(answer_bytes[i]);
  }
  if (answer_bytes != NULL) {
    free(answer_bytes);
  }
  if (answer_byte_lens != NULL) {
    free(answer_byte_lens);
  }

question_free:
  for (size_t i = 0; i < in->qdcount; i++) {
    free(question_bytes[i]);
  }
  if (answer_bytes != NULL) {
    free(question_bytes);
  }
  if (answer_byte_lens != NULL) {
    free(question_byte_lens);
  }

end:
  return rc;
}

int dns_message_clone(DNSMessage *in, DNSMessage **out) {
  Question **question_section = malloc(sizeof(Question *) * in->qdcount);
  PackedRR **answers_section = malloc(sizeof(PackedRR *) * in->ancount);
  PackedRR **authoritative_section = malloc(sizeof(PackedRR *) * in->nscount);
  PackedRR **additional_section = malloc(sizeof(PackedRR *) * in->arcount);
  for (uint16_t i = 0; i < in->qdcount; i++) {
    question_clone(in->question_section[i], question_section + i);
  }
  for (uint16_t i = 0; i < in->ancount; i++) {
    packedrr_clone(in->answers_section[i], answers_section + i);
  }
  for (uint16_t i = 0; i < in->nscount; i++) {
    packedrr_clone(in->authoritative_section[i], authoritative_section + i);
  }
  for (uint16_t i = 0; i < in->arcount; i++) {
    packedrr_clone(in->additional_section[i], additional_section + i);
  }
  return dns_message_create(out, in->identification, in->flags, in->qdcount,
                            in->ancount, in->nscount, in->arcount,
                            question_section, answers_section,
                            authoritative_section, additional_section);
}

char *dns_message_to_string(DNSMessage *in) {
  if (in == NULL)
    return "";
  char **substrings =
      malloc(sizeof(char *) *
             (1 + 1 + in->qdcount + in->ancount + in->nscount + in->arcount));
  printf("DNS MESSAGE: id: %hu, flags: ", ntohs(in->identification));
  uint16_t tmp = in->flags;
  uint16_t mask = 1 << 15;
  for (int i = 0; i < 16; i++) {
    printf("%u ", tmp & mask ? 1 : 0);
    tmp = tmp << 1;
  }
  printf("\n");
  printf("flag dump: %hhu, %hhu\n", ((uint8_t)in->flags),
         *(((uint8_t *)&in->flags) + 1));
  fflush(stdout);
  printf("\tqdcount: %hu\n\tancount: %hu\n\tnscount: %hu\n\tarcount: %hu\n",
         in->qdcount, in->ancount, in->nscount, in->arcount);
  size_t question_start = 2; // after header info
  size_t answer_start = question_start + in->qdcount;
  size_t authoritative_start = answer_start + in->ancount;
  size_t additional_start = authoritative_start + in->nscount;
  for (uint16_t i = 0; i < in->qdcount; i++) {
    substrings[question_start + i] =
        question_to_string(in->question_section[i]);
  }
  for (uint16_t i = 0; i < in->ancount; i++) {
    substrings[answer_start + i] = packedrr_to_string(in->answers_section[i]);
  }
  for (uint16_t i = 0; i < in->nscount; i++) {
    substrings[authoritative_start + i] =
        packedrr_to_string(in->authoritative_section[i]);
  }
  for (uint16_t i = 0; i < in->arcount; i++) {
    substrings[additional_start + i] =
        packedrr_to_string(in->additional_section[i]);
  }
  for (uint16_t i = question_start; i < additional_start + in->arcount; i++) {
    if (i == additional_start) {
      printf("Additional:\n");
    } else if (i == authoritative_start) {
      printf("Authoritative:\n");
    } else if (i == answer_start) {
      printf("Answers:\n");
    } else if (i == question_start) {
      printf("Question:\n");
    }
    printf("%s", substrings[i]);
  }
  printf("\n");
  return NULL;
}

bool is_dns_message_contains_rrfrag(DNSMessage *msg) {
  for (uint16_t i = 0; i < msg->ancount; i++) {
    if (msg->answers_section[i]->isRRFrag)
      return true;
  }
  for (uint16_t i = 0; i < msg->nscount; i++) {
    if (msg->authoritative_section[i]->isRRFrag)
      return true;
  }
  for (uint16_t i = 0; i < msg->arcount; i++) {
    if (msg->additional_section[i]->isRRFrag)
      return true;
  }
  return false;
}

bool is_dns_message_equal(DNSMessage *lhs, DNSMessage *rhs) {
  if (lhs == NULL && rhs != NULL)
    return false;
  if (lhs != NULL && rhs == NULL)
    return false;
  if (lhs->identification != rhs->identification)
    return false;
  if (lhs->flags != rhs->flags)
    return false;
  if (lhs->qdcount != rhs->qdcount)
    return false;
  if (lhs->ancount != rhs->ancount)
    return false;
  if (lhs->nscount != rhs->nscount)
    return false;
  if (lhs->arcount != rhs->arcount)
    return false;
  for (uint16_t i = 0; i < lhs->qdcount; i++) {
    bool res = false;
    for (uint16_t j = 0; j < lhs->qdcount; j++) {
      if (is_question_equal(lhs->question_section[i],
                            rhs->question_section[j])) {
        res = true;
        break;
      }
    }
    if (!res) {
      return false;
    }
  }
  for (uint16_t i = 0; i < lhs->ancount; i++) {
    bool res = false;
    for (uint16_t j = 0; j < lhs->ancount; j++) {
      if (is_packedrr_equal(lhs->answers_section[i], rhs->answers_section[j])) {
        res = true;
        break;
      }
    }
    if (!res) {
      return false;
    }
  }
  for (uint16_t i = 0; i < lhs->nscount; i++) {
    bool res = false;
    for (uint16_t j = 0; j < lhs->nscount; j++) {
      if (is_packedrr_equal(lhs->authoritative_section[i],
                            rhs->authoritative_section[j])) {
        res = true;
        break;
      }
    }
    if (!res) {
      return false;
    }
  }
  for (uint16_t i = 0; i < lhs->arcount; i++) {
    bool res = false;
    for (uint16_t j = 0; j < lhs->arcount; j++) {
      if (is_packedrr_equal(lhs->additional_section[i],
                            rhs->additional_section[j])) {
        res = true;
        break;
      }
    }
    if (!res) {
      return false;
    }
  }
  return true;
}
