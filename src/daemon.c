#include <arpa/inet.h>
#include <assert.h>
#include <dns_message.h>
#include <libnetfilter_queue/libnetfilter_queue.h>
#include <linux/ip.h>
#include <linux/netfilter.h>
#include <linux/tcp.h>
#include <linux/udp.h>
#include <map.h>
#include <math.h>
#include <netdb.h>
#include <poll.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#include <log.h>

#define RRFRAGHEADER 15 // 14 for the fields, + 1 for the name
#define RRHEADER 10
#define DNSMESSAGEHEADER DNSHEADERSIZE
#define SIDECAR_BUFSIZ 0xFFFF

uint32_t SIDECAR_IP_ADDRESS;
uint32_t OPT_SIDECAR_MAX_UDP_SIZE = 1232;
uint32_t OPT_SIDECAR_RESOLVER = false;
uint32_t OPT_SIDECAR_BYPASS = false;

void prepare_env();

char *itoa(uint16_t in) {
  char *res = NULL;
  int num_bytes = snprintf(NULL, 0, "%hu", in) + 1;
  res = malloc(sizeof(char) * num_bytes);
  snprintf(res, num_bytes, "%hu", in);
  return res;
}

char *ip_to_string(uint32_t ip) {
  struct in_addr addr;
  addr.s_addr = ip;
  return inet_ntoa(addr);
}

void ERROR(void) { assert(false); }

#define BLOCKSIZE 32

#define BLOCKRECVD 0
#define BLOCKFREE -1
#define BLOCKWAITING 1

typedef struct PartialRR {
  unsigned char *bytes;
  size_t rrsize;
  size_t bytes_received;
  bool is_complete;
  uint16_t rrid; // 0 will represent an uninitalized PartialRR. There must be no
                 // rr's with rrid 0
  size_t blocks_received;
  size_t expected_blocks;
  int8_t *block_markers; // -1 == not requested, 0 == received, 1 == requested
                         // but not received
} PartialRR;

int init_partialrr(PartialRR **prr) {
  assert(*prr == NULL);
  PartialRR *_prr = malloc(sizeof(PartialRR));
  if (_prr == NULL) {
    return -1;
  }
  _prr->bytes = NULL;
  _prr->rrsize = 0;
  _prr->bytes_received = 0;
  _prr->is_complete = false;
  _prr->rrid = 0;
  _prr->blocks_received = 0;
  _prr->expected_blocks = 0;
  _prr->block_markers = NULL;
  *prr = _prr;
  return 0;
}

typedef struct PartialDNSMessage {
  sem_t lock;
  uint16_t identification;
  bool identification_set;
  uint16_t flags;
  bool flags_set;
  uint16_t qdcount;
  bool qdcount_set;
  uint16_t ancount;
  bool ancount_set;
  uint16_t nscount;
  bool nscount_set;
  uint16_t arcount;
  bool arcount_set;
  Question **question_section;
  uint16_t questions_done;
  PartialRR **answers_section;
  uint16_t answers_done;
  PartialRR **authoritative_section;
  uint16_t authoritative_done;
  PartialRR **additional_section;
  uint16_t additionals_done;
} PartialDNSMessage;

bool init_partialdnsmessage(PartialDNSMessage **msg) {
  PartialDNSMessage *m = *msg;
  if (m == NULL) {
    m = malloc(sizeof(PartialDNSMessage));
  }
  sem_init(&(m->lock), 0, 1);
  m->identification_set = false;
  m->flags_set = false;
  m->qdcount_set = false;
  m->ancount_set = false;
  m->nscount_set = false;
  m->arcount_set = false;
  m->questions_done = false;
  m->answers_done = false;
  m->authoritative_done = false;
  m->additionals_done = false;
  m->question_section = NULL;
  m->answers_section = NULL;
  m->authoritative_section = NULL;
  m->additional_section = NULL;
  m->qdcount = 0;
  m->ancount = 0;
  m->nscount = 0;
  m->arcount = 0;
  *msg = m;
  return true;
}

PartialRR *find_partialrr(PartialDNSMessage *pm, uint16_t rrid,
                          uint8_t *section) {
  if (pm == NULL) {
    return NULL;
  }
  for (uint16_t i = 0; i < pm->ancount; i++) {
    if (pm->answers_section[i]->rrid == rrid) {
      *section = 0;
      return pm->answers_section[i];
    }
  }
  for (uint16_t i = 0; i < pm->nscount; i++) {
    if (pm->authoritative_section[i]->rrid == rrid) {
      *section = 1;
      return pm->authoritative_section[i];
    }
  }
  for (uint16_t i = 0; i < pm->arcount; i++) {
    if (pm->additional_section[i]->rrid == rrid) {
      *section = 2;
      return pm->additional_section[i];
    }
  }
  return NULL;
}

void copy_section(PartialDNSMessage *pm, PackedRR **msgsection,
                  uint16_t sec_len, uint8_t section) {
  for (uint16_t i = 0; i < sec_len; i++) {
    if (msgsection[i]->isRRFrag) {
      RRFrag *rrfrag = msgsection[i]->data.rrfrag;
      uint16_t rrid = rrfrag->rrid;
      uint32_t curidx = rrfrag->curidx;
      uint16_t fragsize = rrfrag->fragsize;
      uint8_t section;
      // Find the associated record somewhere in the partialDNSMessage
      PartialRR *prr = find_partialrr(pm, rrid, &section);
      if (prr->rrid == 0) {
        prr->rrid = rrid;
      }
      // Sanity check that we aren't overwriting anything we shouldn't.
      uint16_t blockidx = curidx / (double)BLOCKSIZE;
      uint16_t lastblockidx = blockidx + ceil(fragsize / (double)BLOCKSIZE);
      uint16_t totalblocks = ceil(rrfrag->rrsize / (double)BLOCKSIZE);
      if (prr->block_markers == NULL) {
        prr->block_markers = malloc(sizeof(int8_t) * totalblocks);
        for (uint16_t j = 0; j < totalblocks; j++) {
          prr->block_markers[j] = BLOCKFREE;
        }
        prr->expected_blocks = totalblocks;
      }
      if (prr->bytes == NULL) {
        prr->bytes = malloc(sizeof(unsigned char) * rrfrag->rrsize);
        if (prr->bytes == NULL) {
          printf("Error allocating bytes in prr\n");
          fflush(stdout);
          exit(-1);
        }
        prr->rrsize = rrfrag->rrsize;
      }
      for (uint16_t j = blockidx; j < lastblockidx; j++) {
        if (prr->block_markers[j] == BLOCKRECVD) {
          printf("block wasn't waiting for data\n");
          ERROR();
        }
      }
      memcpy(prr->bytes + rrfrag->curidx, rrfrag->fragdata, rrfrag->fragsize);
      for (uint16_t j = blockidx; j < lastblockidx; j++) {
        prr->block_markers[j] = BLOCKRECVD;
      }
      prr->blocks_received += lastblockidx - blockidx;
      prr->bytes_received += rrfrag->fragsize;
      if (prr->expected_blocks == prr->blocks_received) {
        prr->is_complete = true;
        for (uint16_t j = 0; j < prr->expected_blocks; j++) {
          assert(prr->block_markers[j] == BLOCKRECVD);
        }
        if (section == 0) {
          // answer section
          pm->answers_done++;
        } else if (section == 1) {
          // authoritative section
          pm->authoritative_done++;
        } else if (section == 2) {
          // additional section
          pm->additionals_done++;
        } else {
          ERROR();
        }
      }
    } else {
      ResourceRecord *rr = msgsection[i]->data.rr;
      size_t outlen;
      unsigned char *out;
      resource_record_to_bytes(rr, &out, &outlen);
      PartialRR **prrs;
      uint16_t prrs_len;
      uint16_t *rrs_done;
      if (section == 0) {
        // answer section
        prrs = pm->answers_section;
        prrs_len = pm->ancount;
        rrs_done = &(pm->answers_done);
      } else if (section == 1) {
        // authoritative section
        prrs = pm->authoritative_section;
        prrs_len = pm->nscount;
        rrs_done = &(pm->authoritative_done);
      } else if (section == 2) {
        // additional section
        prrs = pm->additional_section;
        prrs_len = pm->arcount;
        rrs_done = &(pm->additionals_done);
      } else {
        ERROR();
      }
      for (uint16_t j = 0; j < prrs_len; j++) {
        if (!prrs[j]->is_complete && prrs[j]->rrid == 0) {
          prrs[j]->bytes = malloc(outlen);
          prrs[j]->bytes_received = outlen;
          prrs[j]->rrsize = outlen;
          memcpy(prrs[j]->bytes, out, outlen);
          free(out);
          prrs[j]->is_complete = true;
          (*rrs_done)++;
          break;
        }
      }
    }
  }
}

void copy_message_contents(PartialDNSMessage *data, DNSMessage *msg) {
  sem_wait(&(data->lock));
  if (!data->identification_set) {
    data->identification = msg->identification;
    data->identification_set = true;
  }
  if (!data->flags_set) {
    data->flags = msg->flags;
    data->flags_set = true;
  }
  if (!data->qdcount_set) {
    data->qdcount = msg->qdcount;
    data->qdcount_set = true;
  }
  if (!data->ancount_set) {
    data->ancount = msg->ancount;
    data->ancount_set = true;
  }
  if (!data->nscount_set) {
    data->nscount = msg->nscount;
    data->nscount_set = true;
  }
  if (!data->arcount_set) {
    data->arcount = msg->arcount;
    data->arcount_set = true;
  }
  if (data->question_section == NULL && msg->qdcount != 0) {
    data->question_section = malloc(sizeof(Question *) * data->qdcount);
    for (uint16_t i = 0; i < msg->qdcount; i++) {
      data->question_section[i] = NULL;
      assert(msg->question_section[i]->qtype != RRFRAG);
      question_clone(msg->question_section[i], data->question_section + i);
    }
  }
  if (data->answers_section == NULL && msg->ancount != 0) {
    data->answers_section = malloc(sizeof(PartialRR *) * data->ancount);
    for (uint16_t i = 0; i < msg->ancount; i++) {
      data->answers_section[i] = NULL;
      init_partialrr(data->answers_section + i);
      if (msg->answers_section[i]->isRRFrag) {
        data->answers_section[i]->rrid =
            msg->answers_section[i]->data.rrfrag->rrid;
      }
    }
  }
  if (data->authoritative_section == NULL && msg->nscount != 0) {
    data->authoritative_section = malloc(sizeof(PartialRR *) * data->nscount);
    for (uint16_t i = 0; i < data->nscount; i++) {
      data->authoritative_section[i] = NULL;
      init_partialrr(data->authoritative_section + i);
      if (msg->authoritative_section[i]->isRRFrag) {
        data->authoritative_section[i]->rrid =
            msg->authoritative_section[i]->data.rrfrag->rrid;
      }
    }
  }
  if (data->additional_section == NULL && msg->arcount != 0) {
    data->additional_section = malloc(sizeof(PartialRR *) * data->arcount);
    for (uint16_t i = 0; i < data->arcount; i++) {
      data->additional_section[i] = NULL;
      init_partialrr(data->additional_section + i);
      if (msg->additional_section[i]->isRRFrag) {
        data->additional_section[i]->rrid =
            msg->additional_section[i]->data.rrfrag->rrid;
      }
    }
  }
  copy_section(data, msg->answers_section, msg->ancount, 0);
  copy_section(data, msg->authoritative_section, msg->nscount, 1);
  copy_section(data, msg->additional_section, msg->arcount, 2);
  sem_post(&(data->lock));
}

bool message_complete(PartialDNSMessage *msg) {
  sem_wait(&(msg->lock));
  bool res = ((msg->ancount == msg->answers_done && msg->ancount_set) &&
              (msg->nscount == msg->authoritative_done && msg->nscount_set) &&
              (msg->arcount == msg->additionals_done && msg->arcount_set));
  sem_post(&(msg->lock));
  return res;
}

#define OPT 41

bool update_max_udp(DNSMessage *msg, uint16_t new_size) {
  bool res = false;
  // First we need to find opt. It's always located in
  // the additional section.
  uint16_t arcount = msg->arcount;
  for (uint16_t i = 0; i < arcount; i++) {
    ResourceRecord *rr = msg->additional_section[i]->data.rr;
    if (rr->type == OPT) {
      rr->clas = new_size; // the class field in opt is used for max UDP size
      res = true;
      break;
    }
  }
  return res;
}

bool construct_intermediate_message(DNSMessage *in, DNSMessage **out) {
  dns_message_clone(in, out);
  return update_max_udp(*out, 65535U);
}

// From The Practice of Programming
uint16_t hash_16bit(unsigned char *in, size_t in_len) {
  uint16_t h;
  unsigned char *p = in;

  h = 0;
  for (size_t i = 0; i < in_len; i++) {
    h = 37 * h + p[i];
  }
  return h;
}

void insert_rrfrag(DNSMessage *msg, size_t i, RRFrag *rrfrag) {
  if (i < msg->ancount) {
    free(msg->answers_section[i]->data.rr);
    msg->answers_section[i]->data.rrfrag = malloc(sizeof(rrfrag));
    rrfrag_clone(rrfrag, &(msg->answers_section[i]->data.rrfrag));
    msg->answers_section[i]->isRRFrag = true;
  } else if (i < (msg->ancount + msg->nscount)) {
    i -= msg->ancount;
    free(msg->authoritative_section[i]->data.rr);
    msg->authoritative_section[i]->data.rrfrag = malloc(sizeof(rrfrag));
    rrfrag_clone(rrfrag, &(msg->authoritative_section[i]->data.rrfrag));
    msg->authoritative_section[i]->isRRFrag = true;
  } else if (i < (msg->ancount + msg->nscount + msg->arcount)) {
    i -= (msg->ancount + msg->nscount);
    free(msg->additional_section[i]->data.rr);
    msg->additional_section[i]->data.rrfrag = malloc(sizeof(rrfrag));
    rrfrag_clone(rrfrag, &(msg->additional_section[i]->data.rrfrag));
    msg->additional_section[i]->isRRFrag = true;
  }
}

typedef struct shared_map {
  sem_t lock;
  hashmap *map;
} shared_map;

shared_map responder_cache;
hashmap *requester_state;
shared_map connection_info;

typedef struct conn_info {
  int fd;
  void *transport_header;
  bool is_tcp;
  struct iphdr *iphdr;
} conn_info;

void init_shared_map(shared_map *map) {
  sem_init(&(map->lock), 0, 1);
  map->map = hashmap_create();
}

void create_generic_socket(uint32_t dest_addr, uint16_t dest_port, int *out_fd) {
  struct sockaddr_in addrinfo;
  addrinfo.sin_family = AF_INET;
  addrinfo.sin_addr.s_addr = dest_addr;
  int sock_type = SOCK_DGRAM;
  addrinfo.sin_port = dest_port;
  char ip[INET_ADDRSTRLEN];
  inet_ntop(AF_INET, &addrinfo.sin_addr, ip, INET_ADDRSTRLEN);
  char *port = itoa(ntohs(addrinfo.sin_port));
  struct addrinfo hints, *res;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_INET;
  hints.ai_socktype = sock_type;
  getaddrinfo(ip, port, &hints, &res);
  int fd = socket(addrinfo.sin_family, sock_type, 0);
  if (fd < 0) {
    printf("Error creating socket to send rrfrag\n");
    exit(-1);
  }
  connect(fd, res->ai_addr, res->ai_addrlen);
  *out_fd = fd;
}

void generic_close(int *fd) { close(*fd); }

void generic_send(int fd, unsigned char *bytes, size_t byte_len) {
  int bytes_sent = send(fd, bytes, byte_len, 0);
  if (bytes_sent != byte_len) {
    printf("Error! Didn't send enough.\n");
    exit(-1);
  }
}

// The internal packet functions are to get around an issue
// where netfilter queue prevents packets between the daemon
// and dns server from being sent. There is probably a better
// way to do this, but I can't find it right now.
// Need to figure out a good way to clean up this map.

bool is_internal_packet(struct iphdr *iphdr) {
  return !OPT_SIDECAR_RESOLVER
    && iphdr->saddr == SIDECAR_IP_ADDRESS
    && iphdr->daddr == SIDECAR_IP_ADDRESS;
}

// If we get an internal message that looks like an DNSMessage, then we can
// assume it is passing information between the daemon and either the requester
// or receiver

// Going to need to use raw sockets when responding to an rrfrag request
// so that the sorce destination and ports match up

uint16_t csum(uint16_t *ptr, int32_t nbytes) {
  int32_t sum;
  uint16_t oddbyte;
  uint16_t answer;

  sum = 0;
  while (nbytes > 1) {
    sum += htons(*ptr);
    ptr++;
    nbytes -= 2;
  }
  if (nbytes == 1) {
    oddbyte = 0;
    *((unsigned char *)&oddbyte) = *(unsigned char *)ptr;
    sum += oddbyte;
  }
  sum = (sum >> 16) + (sum & 0xffff);
  sum = sum + (sum >> 16);
  answer = (int16_t)~sum;

  return answer;
}

bool create_raw_socket(int *fd) {
  int _fd = socket(PF_INET, SOCK_RAW, IPPROTO_RAW);
  if (_fd < 0) {
    return false;
  }
  *fd = _fd;
  return true;
}

bool raw_socket_send(int fd, unsigned char *payload, size_t payload_len,
                     uint32_t saddr, uint32_t daddr, uint16_t sport,
                     uint16_t dport) {
  unsigned char *datagram = malloc(sizeof(struct iphdr) + sizeof(struct udphdr) + (sizeof(char) * payload_len));
  struct iphdr *iph = (struct iphdr *) datagram;
  unsigned char *data = datagram + sizeof(struct iphdr) + sizeof(struct udphdr);

  iph->id = htons(1234); // This is fine for a PoC but not ready for deployment
  iph->ihl = 5;
  iph->version = 4;
  iph->tos = 0;
  iph->tot_len = htons(sizeof(struct iphdr) + sizeof(struct udphdr) + payload_len);
  memcpy(data, payload, payload_len);
  iph->frag_off = 0;
  iph->ttl = 255;
  iph->protocol = IPPROTO_UDP;
  iph->check = 0;
  iph->saddr = saddr;
  iph->daddr = daddr;
  iph->check = htons(csum((uint16_t *)datagram, sizeof(struct iphdr)));

  struct sockaddr_in sin;
  sin.sin_family = AF_INET;
  sin.sin_port = htons(dport);
  sin.sin_addr.s_addr = daddr;

  unsigned char *tphdr = datagram + sizeof(struct iphdr);
  struct udphdr *udph = (struct udphdr *)tphdr;
  udph->source = sport;
  udph->dest = dport;
  udph->check = 0;
  udph->len = htons(payload_len + sizeof(struct udphdr));

  int value = 1;
  if (setsockopt(fd, IPPROTO_IP, IP_HDRINCL, &value, sizeof(value))) {
    log_error("failed to set IP_HDRINCL, exiting");
    exit(-1);
  }

  if (sendto(fd, datagram, ntohs(iph->tot_len), 0, (struct sockaddr *)&sin,
             sizeof(sin)) < 0) {
    log_error("failed to send datagram");
    return false;
  }
  close(fd); // we don't need to wait for a response for these, so just close the socket.
  return true;
}

bool handle_internal_packet(struct nfq_q_handle *qh, uint32_t id,
                            struct iphdr *iphdr, uint64_t *question_hash_port,
                            unsigned char *outbuff, size_t *outbuff_len,
                            char *qname) {
  assert(is_internal_packet(iphdr));
  uint32_t verdict = NF_ACCEPT;
  if (!nfq_set_verdict(qh, id, verdict, 0, NULL)) {
    printf("Failed to accept internal packet\n");
    fflush(stdout);
    exit(-1);
  }
  printf("[pqc-dns-sidecar] sent the query for name '%s' to the DNS server.\n",
         qname);

  // We need to get the file descriptor from a previous cb, so get it from
  // a hashtable based on the dest (original socket's source port)
  // if there is something there, receive it, otherwise just return
  conn_info *ci;
  int fd;
  if (!hashmap_get(connection_info.map, question_hash_port, sizeof(uint64_t),
                   (uintptr_t *)&ci)) {
    return false;
  }
  fd = ci->fd;
  struct pollfd ufd;
  memset(&ufd, 0, sizeof(struct pollfd));
  ufd.fd = fd;
  ufd.events = POLLIN;
  int rv = poll(&ufd, 1, 0);
  if (rv == -1) {
    perror("Failed to poll");
    fflush(stdout);
    exit(-1);
  } else if (rv == 0) {
    // This must be an "outgoing" internal message
    // so we just need to accept
    return false;
  } else {
    if (ufd.revents & POLLIN) {
      *outbuff_len = recv(fd, outbuff, *outbuff_len, 0);
      printf("[pqc-dns-sidecar] received a response for name '%s' from the DNS "
             "server.\n",
             qname);
      return true;
    } else {
      printf("poll returned on an event we don't care about\n");
      exit(-1);
    }
  }
}

void internal_close(int fd, uint64_t question_hash_port) {
  hashmap_remove(connection_info.map, &question_hash_port, sizeof(uint64_t));
  generic_close(&fd);
}

void get_rrfrags(DNSMessage *msg, uint8_t section, uint16_t *num_rrfrags,
                 RRFrag ***rrfrags) {
  // 0 == answer section
  // 1 == authoritative section
  // 2 == additional section
  PackedRR **packed_section = NULL;
  size_t section_size = 0;
  if (section == 0) {
    packed_section = msg->answers_section;
    section_size = msg->ancount;
  } else if (section == 1) {
    packed_section = msg->authoritative_section;
    section_size = msg->nscount;
  } else if (section == 2) {
    packed_section = msg->additional_section;
    section_size = msg->arcount;
  } else {
    printf("Failed in get_rrfrags\n");
    fflush(stdout);
    ERROR();
  }
  uint16_t rrfrag_count = 0;
  for (uint16_t i = 0; i < section_size; i++) {
    if (packed_section[i]->isRRFrag) {
      rrfrag_count++;
    }
  }
  RRFrag **_rrfrags = malloc(sizeof(RRFrag *) * rrfrag_count);
  rrfrag_count = 0;
  for (uint16_t i = 0; i < section_size; i++) {
    if (packed_section[i]->isRRFrag) {
      rrfrag_clone(packed_section[i]->data.rrfrag, _rrfrags + rrfrag_count++);
    }
  }
  *rrfrags = _rrfrags;
  *num_rrfrags = rrfrag_count;
}

void partial_to_dnsmessage(PartialDNSMessage *in, DNSMessage **out) {
  assert(message_complete(in));

  Question **questions = in->question_section;

  PackedRR **answers = malloc(sizeof(PackedRR *) * in->ancount);
  for (uint16_t i = 0; i < in->ancount; i++) {
    ResourceRecord *rr;
    size_t bytes_processed;
    if (resource_record_from_bytes(in->answers_section[i]->bytes,
                                   in->answers_section[i]->rrsize,
                                   &bytes_processed, &rr) != 0) {
      printf("Failed to make rr from received bytes\n");
      fflush(stdout);
      exit(-1);
    }
    packedrr_create(rr, answers + i);
  }
  PackedRR **authoritative = malloc(sizeof(PackedRR *) * in->nscount);
  for (uint16_t i = 0; i < in->nscount; i++) {
    ResourceRecord *rr = NULL;
    size_t bytes_processed;
    if (resource_record_from_bytes(in->authoritative_section[i]->bytes,
                                   in->authoritative_section[i]->rrsize,
                                   &bytes_processed, &rr) != 0) {
      printf("Failed to make rr from received bytes\n");
      fflush(stdout);
      exit(-1);
    }
    packedrr_create(rr, authoritative + i);
  }
  PackedRR **additional = malloc(sizeof(PackedRR *) * in->arcount);
  for (uint16_t i = 0; i < in->arcount; i++) {
    ResourceRecord *rr;
    size_t bytes_processed;
    if (resource_record_from_bytes(in->additional_section[i]->bytes,
                                   in->additional_section[i]->rrsize,
                                   &bytes_processed, &rr) != 0) {
      printf("Failed to make rr from received bytes\n");
      fflush(stdout);
      exit(-1);
    }
    packedrr_create(rr, additional + i);
  }
  DNSMessage *msg;
  dns_message_create(&msg, in->identification, in->flags, in->qdcount,
                     in->ancount, in->nscount, in->arcount, questions, answers,
                     authoritative, additional);
  *out = msg;
}

void pack_section(PackedRR ***packed_rrfrags, PartialRR **section,
                  uint16_t section_len, uint16_t *rrfrag_count,
                  uint16_t *rrids_to_complete, uint16_t rrs_not_complete,
                  uint16_t *cur_message_size) {
  uint16_t cursize = *cur_message_size;
  PackedRR **rrfrags = malloc(sizeof(PackedRR *) * rrs_not_complete);
  uint16_t _rrfrag_count = 0;
  for (uint16_t i = 0; (i < rrs_not_complete) && cursize < OPT_SIDECAR_MAX_UDP_SIZE; i++) {
    RRFrag *rrf;
    uint16_t rrid = rrids_to_complete[i];
    PartialRR *prr = NULL;
    for (uint16_t j = 0; j < section_len; j++) {
      if (section[j]->rrid == rrid) {
        prr = section[j];
        break;
      }
    }
    assert(prr != NULL);
    // Find the first block that we haven't requested yet and use that to
    // determine curidx and fragsize to request
    ssize_t curidx = -1;
    size_t numblocks = 0;
    for (size_t j = 0; j < prr->expected_blocks; j++) {
      if (prr->block_markers[j] == BLOCKFREE && curidx == -1) {
        curidx = j;
        numblocks++;
      } else if (prr->block_markers[j] == BLOCKFREE && curidx != -1) {
        numblocks++;
      }
    }
    if (curidx == -1)
      continue;
    size_t lastblocksize = prr->rrsize % BLOCKSIZE;
    if (lastblocksize == 0)
      lastblocksize = BLOCKSIZE;

    size_t canfit = abs(OPT_SIDECAR_MAX_UDP_SIZE - cursize);
    size_t numblockscanfit = floor((float)canfit / BLOCKSIZE);

    if (numblockscanfit >= numblocks) {
      // ask for all
      uint16_t fragsize = numblocks * BLOCKSIZE;
      if (fragsize > prr->rrsize - (curidx * BLOCKSIZE)) {
        fragsize = prr->rrsize - (curidx * BLOCKSIZE);
      }
      if (rrfrag_create(&rrf, fragsize, curidx * BLOCKSIZE, prr->rrsize,
                        prr->rrid, NULL) != 0) {
        printf("Error making rrfrag for follow up request\n");
        ERROR();
      }
      cursize += ((numblocks - 1) * BLOCKSIZE) + lastblocksize - RRHEADER +
                 RRFRAGHEADER;
      if (packedrr_create(rrf, rrfrags + _rrfrag_count) != 0) {
        printf("Error creating packedrr 1\n");
        fflush(stdout);
        ERROR();
      }
      for (int j = curidx; j < curidx + numblocks; j++) {
        prr->block_markers[j] = BLOCKWAITING;
      }
      _rrfrag_count++;
    } else if (numblockscanfit > 0) {
      // ask for what we can
      uint16_t fragsize = numblockscanfit * BLOCKSIZE;
      if (rrfrag_create(&rrf, fragsize, curidx * BLOCKSIZE, prr->rrsize,
                        prr->rrid, NULL) != 0) {
        printf("Error making rrfrag for follow up request\n");
        ERROR();
      }
      cursize += (numblockscanfit * BLOCKSIZE) - RRHEADER + RRFRAGHEADER;
      if (packedrr_create(rrf, rrfrags + _rrfrag_count) != 0) {
        printf("Error creating packedrr 1\n");
        fflush(stdout);
        ERROR();
      }
      for (int j = curidx; j < curidx + numblockscanfit; j++) {
        prr->block_markers[j] = BLOCKWAITING;
      }
      _rrfrag_count++;
      *packed_rrfrags = rrfrags;
      *cur_message_size = cursize;
      *rrfrag_count = _rrfrag_count;
      return;
    } else {
      // Pack RRFrags and return
      *packed_rrfrags = rrfrags;
      *cur_message_size = cursize;
      *rrfrag_count = _rrfrag_count;
      return;
    }
  }
  *packed_rrfrags = rrfrags;
  *cur_message_size = cursize;
  *rrfrag_count = _rrfrag_count;
}

void request_next_fragment(
    DNSMessage *fragment,
    PartialDNSMessage *pm,
    struct iphdr *ip_header,
    void *transport_header
) {
  // Calculate the number of incomplete sections
  uint16_t num_incomplete_an = 0;
  uint16_t num_incomplete_ns = 0;
  uint16_t num_incomplete_ar = 0;

  for (uint16_t i = 0; i < pm->ancount; i++) {
    if (pm->answers_section[i]->is_complete) continue;
    num_incomplete_an++;
  }
  for (uint16_t i = 0; i < pm->nscount; i++) {
    if (pm->authoritative_section[i]->is_complete) continue;
    num_incomplete_ns++;
  }
  for (uint16_t i = 0; i < pm->arcount; i++) {
    if (pm->additional_section[i]->is_complete) continue;
    num_incomplete_ar++;
  }

  // Get the RRIDs of these incomplete sections
  uint16_t an_rrids_to_complete[num_incomplete_an];
  uint16_t ns_rrids_to_complete[num_incomplete_ns];
  uint16_t ar_rrids_to_complete[num_incomplete_ar];

  int offset = 0;

  for (uint16_t i = 0; i < pm->ancount; i++) {
    if (pm->answers_section[i]->is_complete) continue;
    if (pm->answers_section[i]->rrid == 0) continue; // Not sure why, does setting it to zero mean it's complete?
    an_rrids_to_complete[offset] = pm->answers_section[i]->rrid;
    offset++;
  }

  offset = 0;

  for (uint16_t i = 0; i < pm->nscount; i++) {
    if (pm->authoritative_section[i]->is_complete) continue;
    if (pm->authoritative_section[i]->rrid == 0) continue;
    ns_rrids_to_complete[offset] = pm->authoritative_section[i]->rrid;
    offset++;
  }

  offset = 0;

  for (uint16_t i = 0; i < pm->arcount; i++) {
    if (pm->additional_section[i]->is_complete) continue;
    if (pm->additional_section[i]->rrid == 0) continue;
    ar_rrids_to_complete[offset] = pm->additional_section[i]->rrid;
    offset++;
  }

  uint16_t current_message_size = DNSMESSAGEHEADER;

  uint16_t num_an_rrfrags = 0;
  uint16_t num_ns_rrfrags = 0;
  uint16_t num_ar_rrfrags = 0;

  PackedRR **an_rrfrags = NULL;
  PackedRR **ns_rrfrags = NULL;
  PackedRR **ar_rrfrags = NULL;

  pack_section(
      &an_rrfrags,
      pm->answers_section,
      pm->ancount,
      &num_an_rrfrags,
      an_rrids_to_complete,
      num_incomplete_an,
      &current_message_size
  );

  pack_section(
      &ns_rrfrags,
      pm->authoritative_section,
      pm->nscount,
      &num_ns_rrfrags,
      ns_rrids_to_complete,
      num_incomplete_ns,
      &current_message_size
  );

  pack_section(
      &ar_rrfrags,
      pm->additional_section,
      pm->arcount,
      &num_ar_rrfrags,
      ar_rrids_to_complete,
      num_incomplete_ar,
      &current_message_size
  );

  uint16_t final_size = num_an_rrfrags + num_ns_rrfrags + num_ar_rrfrags;
  PackedRR **final_section = malloc(sizeof(PackedRR *) * final_size);

  for (uint16_t i = 0; i < num_an_rrfrags; i++) {
    packedrr_clone(an_rrfrags[i], final_section + i);
  }
  for (uint16_t i = 0; i < num_ns_rrfrags; i++) {
    packedrr_clone(ns_rrfrags[i], final_section + i + num_an_rrfrags);
  }
  for (uint16_t i = 0; i < num_ar_rrfrags; i++) {
    packedrr_clone(ar_rrfrags[i], final_section + i + num_an_rrfrags + num_ns_rrfrags);
  }

  if (an_rrfrags != NULL) {
    free(an_rrfrags);
  }
  if (ns_rrfrags != NULL) {
    free(ns_rrfrags);
  }
  if (ar_rrfrags != NULL) {
    free(ar_rrfrags);
  }

  Question *question;
  question_create(&question, "", 108, 1);

  DNSMessage *next_fragment_request;

  int status = dns_message_create(
      &next_fragment_request,
      pm->identification,
      0,
      1,
      0,
      0,
      final_size,
      &question,
      NULL,
      NULL,
      final_section
  );

  if (status != 0) {
    log_error("failed to create dns message requesting the next fragment, exiting");
    exit(-1);
  }

  int fd;

  if (!create_raw_socket(&fd)) {
    log_error("failed to create socket when attempting to ask for next fragment, exiting");
    exit(-1);
  }

  unsigned char *bytes;
  size_t bytes_length;

  if (dns_message_to_bytes(next_fragment_request, &bytes, &bytes_length) != 0) {
    log_error("failed to convert DNS message requesting the next fragment to bytes, exiting");
    exit(-1);
  }

  raw_socket_send(
      fd,
      bytes,
      bytes_length,
      ip_header->daddr,
      ip_header->saddr,
      ((struct udphdr *)transport_header)->dest,
      ((struct udphdr *)transport_header)->source
  );

  free(bytes);
  close(fd);
}

void responding_thread_start(DNSMessage *message, struct iphdr *ip_header, void *transport_header) {
  if (message->qdcount != 1) {
    log_error("qdcount should always be one, exiting");
    exit(-1);
  }

  // re-send the query from the sidecar, we will drop the original request
  unsigned char *message_bytes;
  size_t message_bytes_size;
  dns_message_to_bytes(message, &message_bytes, &message_bytes_size);

  int fd;
  create_generic_socket(ip_header->daddr, ((struct udphdr *) transport_header)->dest, &fd);
  generic_send(fd, message_bytes, message_bytes_size);
  log_info("re-sent the query from the sidecar");

  // construct information to save
  conn_info *connection = malloc(sizeof(conn_info));
  connection->fd = fd;
  connection->is_tcp = false;
  connection->transport_header = malloc(sizeof(struct udphdr));
  connection->iphdr = malloc(sizeof(struct iphdr));
  memcpy(connection->transport_header, transport_header, sizeof(struct udphdr));
  memcpy(connection->iphdr, ip_header, sizeof(struct iphdr));

  // derive the key needed to save the above information
  struct sockaddr_in sin;
  memset(&sin, 0, sizeof(sin));
  socklen_t len = sizeof(sin);

  if (getsockname(fd, (struct sockaddr *) &sin, &len) == -1) {
    log_error("couldn't get information that needs to be saved from the socket");
    exit(-1);
  }

  unsigned char *question_bytes;
  size_t question_bytes_size;
  question_to_bytes(message->question_section[0], &question_bytes, &question_bytes_size);

  uint64_t *question_hash_and_port = malloc(sizeof(uint64_t));
  memset(question_hash_and_port, 0, sizeof(uint64_t));

  uint32_t *question_hash_and_port_offset = (uint32_t *) question_hash_and_port;
  *question_hash_and_port_offset = hash_16bit(question_bytes, question_bytes_size);
  *(question_hash_and_port_offset + 1) = ntohs(sin.sin_port);

  uintptr_t test;
  if (hashmap_get(connection_info.map, question_hash_and_port, sizeof(uint64_t), (uintptr_t *)&test)) {
    log_error("there's already a connection saved at this key, exiting");
    exit(-1);
  }

  hashmap_set(connection_info.map, question_hash_and_port, sizeof(uint64_t), (uintptr_t)connection);
  if (!hashmap_get(connection_info.map, question_hash_and_port, sizeof(uint64_t), (uintptr_t *)&connection)) {
    log_error("failed to save connection information to memory, exiting");
    exit(-1);
  }

  log_info("saved connection information for client that queried name: '%s'", message->question_section[0]->qname);
  dns_message_destroy(&message);
}

void insert_into_state(ResourceRecord *rr, uint16_t *rrids, size_t *rrcount,
                       size_t *rrsize) {
  size_t _rrcount = *rrcount;
  size_t _rrsize = *rrsize;
  unsigned char *rrout;
  size_t rr_outlen;
  resource_record_to_bytes(rr, &rrout, &rr_outlen);
  uint16_t hash = hash_16bit(rrout, rr_outlen);
  ResourceRecord *out;
  _rrsize += rr_outlen;
  sem_wait(&(responder_cache.lock));
  if (!hashmap_get(responder_cache.map, &hash, sizeof(uint16_t),
                   (uintptr_t *)&out)) {
    uint16_t *_hash = malloc(sizeof(uint16_t));
    *_hash = hash;
    ResourceRecord *crr;
    if (resource_record_clone(rr, &crr) != 0) {
      printf("Failed to clone rr before inserting into hashtable\n");
      ERROR();
    }
    hashmap_set(responder_cache.map, _hash, sizeof(uint16_t), (uintptr_t)crr);
    rrids[_rrcount++] = hash;
  } else {
    if (is_resource_record_equal(rr, out)) {
      // it's already in our hashmap, so just continue
      sem_post(&(responder_cache.lock));
      rrids[_rrcount++] = hash;
      ;
      *rrcount = _rrcount;
      *rrsize = _rrsize;
      return;
    }
    hash++;
    while (hashmap_get(responder_cache.map, &hash, sizeof(uint16_t),
                       (uintptr_t *)&out)) {
      hash++;
    }
    uint16_t *_hash = malloc(sizeof(uint16_t));
    *_hash = hash;
    hashmap_set(responder_cache.map, _hash, sizeof(uint16_t), (uintptr_t)rr);
    rrids[_rrcount++] = hash;
  }
  sem_post(&(responder_cache.lock));
  *rrcount = _rrcount;
  *rrsize = _rrsize;
}

void insert_into_state_and_construct_map(DNSMessage *msg, size_t max_size) {
  size_t total_records = msg->ancount + msg->nscount + msg->arcount;
  uint16_t *rrids = malloc(sizeof(uint16_t) * total_records);
  size_t rrcount = 0;
  size_t rrsize = DNSMESSAGEHEADER;

  // We won't fragment questions since they are very small, but we must include
  // them in responses, and must account for their size when calculating
  // FRAGSIZEs

  for (int i = 0; i < msg->qdcount; i++) {
    size_t q_len;
    unsigned char *q_bytes;
    question_to_bytes(msg->question_section[i], &q_bytes, &q_len);
    free(q_bytes);
    rrsize += q_len;
  }

  // Answers
  for (int i = 0; i < msg->ancount; i++) {
    ResourceRecord *rr = msg->answers_section[i]->data.rr;
    insert_into_state(rr, rrids, &rrcount, &rrsize);
  }

  // Authoritative
  for (int i = 0; i < msg->nscount; i++) {
    ResourceRecord *rr = msg->authoritative_section[i]->data.rr;
    insert_into_state(rr, rrids, &rrcount, &rrsize);
  }

  // Additional Section (make sure to not add opt)
  for (int i = 0; i < msg->arcount; i++) {
    ResourceRecord *rr = msg->additional_section[i]->data.rr;
    insert_into_state(rr, rrids, &rrcount, &rrsize);
  }

  size_t cur_size = rrsize;
  if (cur_size > max_size - DNSMESSAGEHEADER) {
    printf("[pqc-dns-sidecar] Response message is %ld bytes which exceeds the "
           "%ld byte limit. Fragmentation will be performed.\n",
           rrsize, max_size - DNSMESSAGEHEADER);
  } else {
    printf("[pqc-dns-sidecar] Response message is %ld bytes which fits within "
           "the %ld byte limit. No fragmentation required.\n",
           rrsize, max_size - DNSMESSAGEHEADER);
  }
  while (cur_size > max_size - DNSMESSAGEHEADER) {
    size_t cur_max = 0;
    uint16_t hash;
    ResourceRecord *rr;
    size_t idx = 0;
    for (int i = 0; i < rrcount; i++) {
      uint16_t cur_hash = rrids[i];
      if (cur_hash == 0) {
        continue;
      }
      if (!hashmap_get(responder_cache.map, &cur_hash, sizeof(uint16_t),
                       (uintptr_t *)&rr)) {
        printf("RRID: %hu, type: %hu\n", hash, rr->type);
        fflush(stdout);
        assert("[ERROR]Couldn't find rr with that rrid" == false);
      }
      if (rr->rdsize > cur_max) {
        cur_max = rr->rdsize;
        hash = cur_hash;
        idx = i;
      }
    }
    if (!hashmap_get(responder_cache.map, &hash, sizeof(uint16_t),
                     (uintptr_t *)&rr)) {
      printf("rrid: %hu\n", hash);
      fflush(stdout);
      assert("[ERROR]Couldn't find rr with that rrid" == false);
    }
    // mark rrfrag as compressed.
    rrids[idx] = 0;
    if ((cur_size - rr->rdsize) >= max_size - DNSMESSAGEHEADER) {
      // make an rrfrag with fragsize 0
      printf("[pqc-dns-sidecar] Creating final fragment with RRID %d.\n", hash);
      fflush(stdout);
      RRFrag *rrfrag;
      unsigned char *bytes;
      size_t out_len;
      resource_record_to_bytes(rr, &bytes, &out_len);
      rrfrag_create(&rrfrag, 0, 0, out_len, hash, NULL);
      free(bytes);
      insert_rrfrag(msg, idx, rrfrag);
      cur_size -= out_len;
      cur_size += RRFRAGHEADER;
    } else {
      // How much do we have to work with?
      printf("[pqc-dns-sidecar] Creating fragment with RRID %d.\n", hash);
      fflush(stdout);
      size_t cs = abs(cur_size + (RRFRAGHEADER - RRHEADER - rr->name_byte_len) -
                      (max_size - DNSMESSAGEHEADER));
      if (cs > rr->rdsize) {
        cs = 0;
      } else {
        cs = rr->rdsize - cs;
      }
      double numblocks = ((double)cs) / ((double)BLOCKSIZE);
      RRFrag *rrfrag;
      unsigned char *bytes;
      size_t out_len;
      resource_record_to_bytes(rr, &bytes, &out_len);
      uint16_t fragsize = floor(numblocks) * BLOCKSIZE;
      if (cs > 0) {
        rrfrag_create(&rrfrag, fragsize, 0, out_len, hash, bytes);
        cur_size -= out_len;
      } else {
        rrfrag_create(&rrfrag, fragsize, 0, 0, hash, NULL);
        cur_size -= out_len;
      }
      free(bytes);
      insert_rrfrag(msg, idx, rrfrag);
      rrfrag_to_bytes(rrfrag, &bytes, &out_len);
      free(bytes);
      cur_size += out_len;
      // if we get to this case, we're done and can just break out of our loop
      break;
    }
  }
}

void responding_thread_end(struct iphdr *iphdr, void *transport_hdr,
                           bool is_tcp, unsigned char *recvd, size_t recvd_len,
                           uint64_t *question_hash_port, int fd) {
  internal_close(fd, *question_hash_port);
  DNSMessage *recvd_msg;
  // Probably what's best is to have a centralized hashmap that we index using
  // RRIDs when we get a response from the name server containing all the RRs we
  // add them to the hash table. If there is something already there, just
  // increase the proposed RRID by one until we find a blank spot. Keep a note
  // of these RRIDs for reassembly
  if (dns_message_from_bytes(recvd, recvd_len, &recvd_msg) != 0) {
    assert("Failed to build dnsmessage from response to imsg" == false);
  }
  // Finally we can make our new DNSMessage and send it back to who we got it
  // from.
  insert_into_state_and_construct_map(recvd_msg, OPT_SIDECAR_MAX_UDP_SIZE);
  fd = -1;
  unsigned char *msg_bytes;
  size_t byte_len;
  dns_message_to_bytes(recvd_msg, &msg_bytes, &byte_len);
  dns_message_destroy(&recvd_msg);
  create_raw_socket(&fd);
  if (is_tcp) {
    raw_socket_send(fd, msg_bytes, byte_len, iphdr->daddr, iphdr->saddr,
                    ((struct tcphdr *)transport_hdr)->dest,
                    ((struct tcphdr *)transport_hdr)->source);
  } else {
    if (byte_len > OPT_SIDECAR_MAX_UDP_SIZE) {
      printf("byte_len: %lu, MAXUDP: %u, difference: %lu\n", byte_len, OPT_SIDECAR_MAX_UDP_SIZE,
             byte_len - (size_t)OPT_SIDECAR_MAX_UDP_SIZE);
      assert(byte_len <= OPT_SIDECAR_MAX_UDP_SIZE);
    }
    raw_socket_send(fd, msg_bytes, byte_len, iphdr->daddr, iphdr->saddr,
                    ((struct udphdr *)transport_hdr)->dest,
                    ((struct udphdr *)transport_hdr)->source);
  }
  close(fd);
}

void return_reassembled_message(
    PartialDNSMessage* reassembled,
    struct iphdr *ip_header,
    void *transport_header
) {
  DNSMessage *response;
  partial_to_dnsmessage(reassembled, &response);
  response->flags = response->flags | (1 << 15);

  unsigned char* response_bytes;
  size_t response_length;
  if (dns_message_to_bytes(response, &response_bytes, &response_length) != 0) {
    log_error("failed to convert final, re-assembled dns message to bytes, exiting");
    exit(-1);
  }

  int socket;
  if (!create_raw_socket(&socket)) {
    log_error("failed to create socket for sending re-assembled message with id %d, exiting", response->identification);
    exit(-1);
  }
  raw_socket_send(
    socket,
    response_bytes,
    response_length,
    ip_header->saddr,
    ip_header->daddr,
    ((struct udphdr *)transport_header)->source,
    ((struct udphdr *)transport_header)->dest
  );
  generic_close(&socket);
}

int internal_packet_filter_chain(
    struct iphdr *iphdr,
    struct nfq_q_handle *qh,
    uint32_t id,
    DNSMessage *message,
    uint16_t destination_port
) {
  if (message->qdcount != 1) {
    log_error("qdcount should be one, exiting");
    exit(-1);
  }

  size_t outbuff_len = 65355; // Need to account for large messages because of SPHINCS+
  unsigned char outbuff[outbuff_len];

  unsigned char *question_bytes;
  size_t question_bytes_size;
  question_to_bytes(message->question_section[0], &question_bytes, &question_bytes_size);

  uint64_t *question_hash_port = malloc(sizeof(uint64_t));
  memset(question_hash_port, 0, sizeof(uint64_t));

  uint32_t *question_hash = (uint32_t *)question_hash_port;
  *question_hash = hash_16bit(question_bytes, question_bytes_size);
  *(question_hash + 1) = destination_port;

  if (handle_internal_packet(
          qh,
          id,
          iphdr,
          question_hash_port,
          outbuff,
          &outbuff_len,
          message->question_section[0]->qname)
          && destination_port != 53) {

    conn_info *connection;
    if (!hashmap_get(connection_info.map, question_hash_port, sizeof(uint64_t), (uintptr_t *)&connection)) {
      log_error("failed to find connection in memory, accepting anyway");
      return NF_ACCEPT;
    }

    responding_thread_end(
      connection->iphdr,
      connection->transport_header,
      connection->is_tcp,
      outbuff,
      outbuff_len,
      question_hash_port,
      connection->fd
    );
  } else {
    return NF_ACCEPT;
  }
  return 0xFFFF;
}

uint32_t query_ingress_filter_chain(DNSMessage *message, struct iphdr *ip_header, void* transport_header) {
  if (is_dns_message_contains_rrfrag(message)) {
    uint16_t num_rrfrags;
    RRFrag **rrfrags;
    PackedRR **rrfrags_to_send;
    get_rrfrags(message, 2, &num_rrfrags, &rrfrags);
    rrfrags_to_send = malloc(sizeof(RRFrag *) * num_rrfrags);
    for (uint16_t i = 0; i < num_rrfrags; i++) {
      RRFrag *rrf = rrfrags[i];
      uint16_t rrid = rrf->rrid;
      uint32_t curidx = rrf->curidx;
      uint32_t fragsize = rrf->fragsize;
      ResourceRecord *rr;
      if (!hashmap_get(responder_cache.map, &rrid, sizeof(uint16_t),
                       (uintptr_t *)&rr)) {
        printf("Failed to find a rr with that rrid... shouldn't happen\n");
        fflush(stdout);
        exit(-1);
      }
      unsigned char *rrbytes;
      size_t rrbyte_len;
      resource_record_to_bytes(rr, &rrbytes, &rrbyte_len);
      RRFrag *_rrf;
      if (rrfrag_create(&_rrf, fragsize, curidx, rrf->rrsize, rrf->rrid,
                        rrbytes + curidx) != 0) {
        assert("Failed to make new rrfrag" == false);
      }
      free(rrbytes);
      packedrr_create(_rrf, rrfrags_to_send + i);
    }
    DNSMessage *resp;
    uint16_t flags = message->flags;
    flags = (flags | (1 << 15)); // mark message as response
    if (dns_message_create(&resp, message->identification, flags, 0,
                           num_rrfrags, 0, 0, NULL, rrfrags_to_send, NULL,
                           NULL) != 0) {
      assert("Failed to make dnsmessage containing rrfrags" == false);
    }
    unsigned char *msgbytes;
    size_t msgbyte_len;
    dns_message_to_bytes(resp, &msgbytes, &msgbyte_len);
    int out_fd;
    if (!create_raw_socket(&out_fd)) {
      printf("Failed to make raw socket to respond to rrfrag request\n");
      fflush(stdout);
      ERROR();
    }
    raw_socket_send(out_fd, msgbytes, msgbyte_len, ip_header->daddr,
                    ip_header->saddr,
                    ((struct udphdr *)transport_header)->dest,
                    ((struct udphdr *)transport_header)->source);
    generic_close(&out_fd);
    free(msgbytes);
    return NF_DROP;
  } else if (!OPT_SIDECAR_RESOLVER) {
    responding_thread_start(message, ip_header, transport_header);
    return NF_DROP;
  } else {
    printf("[pqc-dns-sidecar] received a query for name: '%s', "
           "forwarding it to the underlying recursive resolver without "
           "modification.\n",
           message->question_section[0]->qname);
    fflush(stdout);
    return NF_ACCEPT;
  }
}

uint32_t response_ingress_filter_chain(
    DNSMessage *message,
    struct iphdr *ip_header,
    void *transport_header
) {
  if (!is_dns_message_contains_rrfrag(message)) {
    log_info("the message was not a fragment, releasing any memory allocated for message id %d", message->identification);
    hashmap_remove(requester_state, &(message->identification), sizeof(uint16_t));
    return NF_ACCEPT;
  }

  PartialDNSMessage *partial_dns_message;

  bool found = hashmap_get(
      requester_state,
      &(message->identification),
      sizeof(uint16_t),
      (uintptr_t *) &partial_dns_message
  );

  if (!found) {
    log_info("could not find a partially reconstructed message with id %d", message->identification);
    return NF_DROP;
  }

  copy_message_contents(partial_dns_message, message);

  if (message_complete(partial_dns_message)) {
    log_info("finished re-assembling message with id %id, returning completed response", message->identification);
    return_reassembled_message(partial_dns_message, ip_header, transport_header);
    return NF_DROP;
  }

  log_info("the message is still not complete, requesting the next fragment for message with id %d", message->identification);
  request_next_fragment(message, partial_dns_message, ip_header, transport_header);
  return NF_DROP;
}

uint32_t query_egress_filter_chain(DNSMessage* message, uint32_t destination_address) {
  log_info(
      "recursive resolver is making a query on behalf of the client for record '%s' - destination %s",
      message->question_section[0]->qname,
      ip_to_string(destination_address)
  );

  if (!hashmap_get(requester_state, &(message->identification), sizeof(uint16_t), NULL)) {
    PartialDNSMessage *partial_dns_message = NULL;
    init_partialdnsmessage(&partial_dns_message);
    hashmap_set(requester_state, &(message->identification), sizeof(uint16_t), (uintptr_t) partial_dns_message);
  }

  return NF_ACCEPT;
}

uint32_t response_egress_filter_chain(DNSMessage *message, uint32_t destination_address) {
  log_info(
      "returning response for record '%s' - destination %s",
      message->question_section[0]->qname,
      ip_to_string(destination_address)
  );
  return NF_ACCEPT;
}

uint32_t process_dns_message(
    struct nfq_q_handle *qh,
    uint32_t id,
    unsigned char *payload,
    size_t payload_length,
    struct iphdr *ip_header,
    void *transport_header
) {
  unsigned char *packet = payload + sizeof(struct udphdr) + sizeof(struct iphdr);
  size_t message_size = payload_length - (sizeof(struct udphdr) + sizeof(struct iphdr));

  uint32_t source_address = ip_header->saddr;
  uint16_t source_port = ntohs(((struct udphdr *)transport_header)->source);

  uint32_t destination_address = ip_header->daddr;
  uint16_t destination_port = ntohs(((struct udphdr *)transport_header)->dest);

  if (destination_port != 53 && source_port != 53) {
    log_info("packet source and destination was not the expected DNS port (53), ignoring packet");
    return NF_ACCEPT;
  }

  DNSMessage *message;

  if (dns_message_from_bytes(packet, message_size, &message) != 0) {
    log_error("failed to convert bytes from packet to a DNS message");
    exit(-1);
  }

  if (is_internal_packet(ip_header)) {
    return internal_packet_filter_chain(
        ip_header,
        qh,
        id,
        message,
        destination_port
    );
  }

  if (destination_address == SIDECAR_IP_ADDRESS) {
    return is_dns_message_query(message)
        ? query_ingress_filter_chain(message, ip_header, transport_header)
        : response_ingress_filter_chain(message, ip_header, transport_header);
  }

  if (source_address == SIDECAR_IP_ADDRESS) {
    return is_dns_message_query(message)
      ? query_egress_filter_chain(message, destination_address)
      : response_egress_filter_chain(message, destination_address);
  }

  return NF_ACCEPT;
}

uint32_t process_udp(struct nfq_q_handle *qh, uint32_t id,
                     struct iphdr *ipv4hdr, unsigned char *payload,
                     size_t payloadLen) {
  if (OPT_SIDECAR_BYPASS) {
    return NF_ACCEPT;
  }
  struct udphdr *udphdr = (struct udphdr *)((char *)payload + sizeof(*ipv4hdr));
  return process_dns_message(qh, id, payload, payloadLen, ipv4hdr, udphdr);
}

uint32_t process_packet(struct nfq_q_handle *qh, struct nfq_data *data, uint32_t **verdict) {
  unsigned char *payload = NULL;
  size_t payload_length = nfq_get_payload(data, &payload);

  struct nfqnl_msg_packet_hdr *pkthdr = nfq_get_msg_packet_hdr(data);
  uint32_t id = ntohl(pkthdr->packet_id);

  struct iphdr *iphdr = (struct iphdr *)payload;
  uint32_t src_ip = iphdr->saddr;
  uint32_t dst_ip = iphdr->daddr;

  uint32_t res;

  if (dst_ip == SIDECAR_IP_ADDRESS || src_ip == SIDECAR_IP_ADDRESS) {
    if (iphdr->protocol == IPPROTO_UDP) {
      printf("UDP packet - process_udp\n");
      res = process_udp(qh, id, iphdr, payload, payload_length);
    } else {
      res = NF_ACCEPT;
    }
  } else if (iphdr->protocol == IPPROTO_UDP) {
    res = NF_DROP;
  } else if (iphdr->protocol == IPPROTO_ICMP) {
    res = NF_DROP;
  } else {
    res = NF_ACCEPT;
  }

  **verdict = res;

  if (res == 0xFFFF) {
    return 0;
  }

  return id;
}

static int cb(struct nfq_q_handle *qh, struct nfgenmsg *nfmsg, struct nfq_data *nfa, void *data) {
  uint32_t verdict;
  uint32_t *verdict_p = &verdict;
  uint32_t id = process_packet(qh, nfa, &verdict_p);
  if (*verdict_p == 0xFFFF)
    return 0;
  verdict = *verdict_p;
  if (nfq_set_verdict(qh, id, verdict, 0, NULL) < 0) {
    printf("Verdict error\n");
    fflush(stdout);
    exit(-1);
  }
  return 0;
}

int main() {
  prepare_env();

  init_shared_map(&responder_cache);
  init_shared_map(&connection_info);
  requester_state = hashmap_create();

  struct nfq_handle *h;
  struct nfq_q_handle *qh;

  if ((h = nfq_open()) == NULL) {
    log_error("nfq_open failed, exiting");
    exit(-1);
  }
  if (nfq_bind_pf(h, AF_INET) < 0) {
    log_error("nfq_bind_pf failed, exiting");
    exit(-1);
  }
  if ((qh = nfq_create_queue(h, 0, &cb, NULL)) == NULL) {
    log_error("nfq_create_queue failed, exiting");
    exit(-1);
  }
  if ((nfq_set_mode(qh, NFQNL_COPY_PACKET, SIDECAR_BUFSIZ)) == -1) {
    log_error("nfq_set_mode failed, exiting");
    exit(-1);
  }

  int fd = nfq_fd(h);
  char buf[SIDECAR_BUFSIZ];
  struct pollfd ufd = { .fd = fd, .events = POLLIN };

  log_info("Started pqc-dns-sidecar application");

  while (true) {
    if (poll(&ufd, 1, 0) < 0) {
      log_error("Failed to poll nfq, exiting");
      exit(-1);
    }

    int rv = recv(fd, buf, sizeof(buf), 0);
    if (rv < 0) {
      log_error("Failed to receive data, exiting");
      exit(-1);
    }

    nfq_handle_packet(h, buf, rv);
  }

  return 0;
}

void prepare_env() {
  log_info("Preparing environment for pqc-dns-sidecar");

  const char *sidecar_ip_address = getenv("SIDECAR_IP_ADDRESS");
  const char *sidecar_resolver = getenv("SIDECAR_RESOLVER_ENABLED");
  const char *sidecar_bypass = getenv("SIDECAR_BYPASS_ENABLED");
  const char *sidecar_max_udp_size = getenv("SIDECAR_MAX_UDP_SIZE");

  if (sidecar_ip_address == NULL) {
    log_error("Mandatory environment variable Sidecar IP address was not specified, exiting");
    exit(-1);
  } else {
    inet_pton(AF_INET, sidecar_ip_address, &SIDECAR_IP_ADDRESS);
  }
  if (sidecar_resolver != NULL) {
    log_info("Found SIDECAR_RESOLVER_ENABLED, starting in resolver mode");
    OPT_SIDECAR_RESOLVER = true;
  }
  if (sidecar_bypass != NULL) {
    log_info("Found SIDECAR_BYPASS_ENABLED, bypass mode enabled");
    OPT_SIDECAR_BYPASS = true;
  }
  if (sidecar_max_udp_size != NULL) {
    log_info("Found SIDECAR_MAX_UDP_SIZE, configuring UDP fragment size");
    OPT_SIDECAR_MAX_UDP_SIZE = strtol(sidecar_max_udp_size, NULL, 10);
  }
}

