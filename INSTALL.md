# Install/Build

There are three distinct possibilities:

## 1) Docker image
You can download the Docker image using [this link](https://drive.google.com/file/d/1FyKCJ16dM8UiRvz6CrChu_WtJPvfukwU/view?usp=sharing) (md5sum: `94f7ec5bc7ba16abd907fdf714742c70`)
After unziping it, load and start the image with:
```sh
docker load -i celsius.tar
docker run -it celsius
```
Inside the container, go to the celsius directory (with `cd celsius`).

## 2) Local opam switch
You need to have [opam](https://opam.ocaml.org/doc/Install.html) installed.
First, you can clone the project with
```sh
git clone https://github.com/clementblaudeau/celsius
cd celsius
```
Then, just run (~15 minutes as it recompiles Coq and rechecks the proofs):
```
opam switch create ./
```

## 3) If you already have Coq (>= `8.15.2`)
First, you can clone the project with
```sh
git clone https://github.com/clementblaudeau/celsius
cd celsius
```
Then, just run (~5/10 minutes):
```
make Makefile.coq
make -j 4
```

# Check you installation
In all cases, you should be able to run the following commands (in the `celsius` directory):
```sh
coqtop -Q src Celsius
```
And then:
```coq
From Celsius Require Import Soundness.
Check Soundness.
Print Assumptions Soundness.
```
