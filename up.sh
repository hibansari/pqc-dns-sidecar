#!/bin/bash

# Build the Docker image
docker build -t sidecar .

# Navigate to the pqc-developer directory
cd ../pqc-developer-environment

# Start the containers using docker-compose
docker compose up