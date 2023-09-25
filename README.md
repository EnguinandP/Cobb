# Cobb
One who searches underneath the bottom of consciousness: Inception(2010)

## Getting started
1. [Install opam](https://opam.ocaml.org/doc/Install.html)
2. [`opam switch create ./ --deps-only`](https://opam.ocaml.org/blog/opam-local-switches/#A-reminder-about-switches)
3. Inside the `Cobb` directory run `eval $(opam env)`
4. Build with `dune build`
5. Run with `dune exec Cobb`

### Updating submodules
1. `git submodule sync`
2. `git submodule update --remote`
