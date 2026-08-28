FROM ubuntu:25.04
MAINTAINER Joel Martin <github@martintribe.org>

##########################################################
# General requirements for testing or common across many
# implementations
##########################################################

RUN apt-get -y update

# Required for running tests
RUN apt-get -y install make python3
RUN ln -fs /usr/bin/python3 /usr/local/bin/python

RUN mkdir -p /mal
WORKDIR /mal

##########################################################
# Specific implementation requirements
##########################################################

# Some dependencies require rust/1.95, not yet in Ubuntu.
RUN apt-get -y install debian-archive-keyring
RUN printf 'Types: deb\nURIs: http://deb.debian.org/debian\nSuites: forky\nComponents: main\nSigned-By: /usr/share/keyrings/debian-archive-keyring.gpg\n' > /etc/apt/sources.list.d/rust195.sources
RUN apt update
RUN apt-get -y install cargo \
  librust-fnv-dev \
  librust-itertools-dev \
  librust-regex-dev \
  librust-rustyline-dev \
  rust-clippy rustfmt

ENV CARGO_HOME /mal
