# Compilation notes

## Mac OSX

This C++ implementation was developed on Mac OS X Yosemite, and uses the
stock g++ compiler.

The only other requirement is GNU Readline, which I got from homebrew.

    brew install readline

You may need to edit the READLINE path in the Makefile.

## Ubuntu 14.10/15.04

This should compile on Ubuntu 14.10 and 15.04 with the following packages

    apt-get install clang-3.5 libreadline-dev libgc-dev make

## Docker

For everyone else, there is a Dockerfile and associated docker.sh script which
can be used to make and run this implementation.

    * build the docker image

        ./docker build

    * make the MAL binaries:

        ./docker make

    * run one of the implementations:

        ./docker run ./stepA_mal

    * open a shell inside the docker container:

        ./docker run

#About garbage collection.

Destructors were once used to trace deallocations, but in order to
call them we need to inherit from gc_cleanup instead of gc.  The
collection then fails because it cannot guess in which order it must
invoke the destructor in cycles.

The heap does not seem to grow forever when the following program runs
with GC_PRINT_STATS=1 in the environment.
for (int i = 0; i < 10000; i++) {
    rep("(let* [f (fn* [] nil)] nil)", replEnv);
    GC_gcollect();
}
