# Building

Please note that there is a workflow setup to release the binary to GitHub packages on every push or merge to the main branch.

In most cases, it will be sufficient for you to use the published binary.

However, if you wish to build the binary locally, you can follow the instructions below.

Please note, building requires ubuntu:20.04. Windows and MacOS are not supported.

## Install dependencies

```sh
apt update

apt upgrade -y

apt install cmake g++ netfilter-queue-dev
```

## Build

Run the following commands from the root of the project, i.e. where this README file is located.

```sh
mkdir build

cd build

cmake ..

make
```

## Run

```sh
./build/placeholder <arguments>
```