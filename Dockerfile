FROM --platform=linux/amd64 ubuntu:22.04

ENV LD_LIBRARY_PATH=/usr/local/lib

WORKDIR /

RUN DEBIAN_FRONTEND=noninteractive TZ=Australia/Sydney  \
        apt update -y                                   \
        && apt upgrade -y                               \
        && apt install wget unzip rsync libssl-dev libuv1-dev libnghttp2-dev libtool libcap-dev libnetfilter-queue-dev iptables -y

RUN wget https://github.com/nirajsapkota/pqc-bind/releases/latest/download/pqc-bind.zip \
        && mkdir pqc-bind                                                               \
        && unzip pqc-bind.zip -d pqc-bind                                               \
        && rsync -a pqc-bind/* /usr/local/                                              \
        && rm -rf pqc-bind pqc-bind.zip

COPY ./build/pqc-dns-sidecar /usr/local/bin/

CMD iptables -A INPUT -p ip -j NFQUEUE --queue-num 0            \
        && iptables -A OUTPUT -p ip -j NFQUEUE --queue-num 0    \
        && /usr/local/bin/pqc-dns-sidecar                      \
        & named -g -d 3
