# Installation procedure for SMTCoq-API
First, you need to install the development version of SMTCoq for
Coq-8.19. In a new switch:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-smtcoq.dev+8.19
```

Then, simply run:
```
make
```
