# Download the base image ubuntu 20.04
FROM ubuntu:20.04

# Install the prerequisites + git, wget, unzip, sudo
RUN apt-get update
RUN apt-get install -y openjdk-11-jdk 
RUN apt-get install -y python python3-pip
RUN apt-get install -y build-essential 
RUN apt-get install -y git wget unzip sudo curl

# Clone our repository and build our tool
RUN git clone https://github.com/alebugariu/UnsatY.git UnsatY
RUN cd UnsatY && chmod +x install.sh 
RUN cd UnsatY && . ./install.sh