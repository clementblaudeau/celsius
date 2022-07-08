# Install/Build

There are three possibilities:

## Docker image
??

## Local opam switch
You need to have [opam](https://opam.ocaml.org/doc/Install.html) installed.
First, you can clone the project with
```sh
git clone https://github.com/clementblaudeau/celsius
cd celsius
```
Then, just run :
```
opam switch create ./
```

## If you already have Coq (>= `8.15.2`)
First, you can clone the project with
```sh
git clone https://github.com/clementblaudeau/celsius
cd celsius
```
Then, just run :
```
make Makefile.coq
make -j 4
```

# Check you installation
In all cases, you should be able to run the following commands:
```sh
coqtop -Q src Celsius
```
And then:
```coq
From Celsius Require Import Soundness.
Check Soundness.
Print Assumptions Soundness.
```
