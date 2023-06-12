#include <packedrr.h>
#include <resource_record.h>
#include <rrfrag.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

int packedrr_destroy(PackedRR **prr) {
  if (prr == NULL)
    return 0;
  if (*prr == NULL)
    return 0;
  PackedRR *_prr = *prr;
  if (_prr->isRRFrag) {
    RRFrag *rrfrag = _prr->data.rrfrag;
    rrfrag_destroy(&rrfrag);
  } else {
    ResourceRecord *rr = _prr->data.rr;
    resource_record_destroy(&rr);
  }
  *prr = NULL;
  return 0;
}

int packedrr_create(void *in, PackedRR **out) {
  ResourceRecord *tmp = (ResourceRecord *)in;
  PackedRR *res = malloc(sizeof(PackedRR));
  if (res == NULL)
    return -1;
  // RRFRAG and ResourceRecords have the same format for the first two
  // fields, so I can just pick one to figure out what I'm dealing with
  bool isrrfrag = (tmp->type == RRFRAG);
  if (isrrfrag) {
    rrfrag_clone((RRFrag *)in, &(res->data.rrfrag));
  } else {
    resource_record_clone((ResourceRecord *)in, &(res->data.rr));
  }
  res->isRRFrag = isrrfrag;
  *out = res;
  return 0;
}

int packedrr_clone(PackedRR *in, PackedRR **out) {
  int rc = 0;
  PackedRR *res;
  if (in->isRRFrag) {
    rc = packedrr_create(in->data.rrfrag, &res);
  } else {
    rc = packedrr_create(in->data.rr, &res);
  }
  *out = res;
  return rc;
}

int packedrr_to_bytes(PackedRR *in, unsigned char **out, size_t *out_len) {
  unsigned char *res;
  size_t len;
  int rc = 0;
  if (in->isRRFrag) {
    rc = rrfrag_to_bytes(in->data.rrfrag, &res, &len);
    if (rc != 0)
      goto err;
  } else {
    rc = resource_record_to_bytes(in->data.rr, &res, &len);
    if (rc != 0)
      goto err;
  }
  *out = res;
  *out_len = len;
err:
  return rc;
}

// This could be a dangerous function... Basically no bounds checking happens
int packedrr_from_bytes(unsigned char *in, size_t in_len,
                        size_t *bytes_processed, bool is_dns_message_query,
                        PackedRR **out) {
  int rc = 0;
  PackedRR *prr = malloc(sizeof(PackedRR));
  if (is_rrfrag(in)) {
    rc = rrfrag_from_bytes(in, in_len, bytes_processed, is_dns_message_query,
                           &(prr->data.rrfrag));
    prr->isRRFrag = true;
    if (rc != 0)
      goto err;
  } else {
    rc = resource_record_from_bytes(in, in_len, bytes_processed,
                                    &(prr->data.rr));
    prr->isRRFrag = false;
    if (rc != 0)
      goto err;
  }
  *out = prr;
  return rc;
err:
  free(prr);
  return rc;
}

char *packedrr_to_string(PackedRR *prr) {
  if (prr == NULL)
    return "";
  if (prr->isRRFrag) {
    return rrfrag_to_string(prr->data.rrfrag);
  } else {
    return resource_record_to_string(prr->data.rr);
  }
}

bool is_packedrr_equal(PackedRR *lhs, PackedRR *rhs) {
  if (lhs == NULL && rhs != NULL)
    return false;
  if (lhs != NULL && rhs == NULL)
    return false;
  if (lhs->isRRFrag && rhs->isRRFrag)
    return is_rrfrag_equal(lhs->data.rrfrag, rhs->data.rrfrag);
  if (!lhs->isRRFrag && !rhs->isRRFrag)
    return is_resource_record_equal(lhs->data.rr, rhs->data.rr);
  return false;
}
