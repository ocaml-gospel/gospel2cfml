# gospel2cfml

A tool that translated *Gospel*-annotaded `.mli` files into *Coq* terms that can
be processed by *CFML*.

## Installation

After cloning the repository, simply do:
```
opam pin add <path/to/gospel2cfml>
```

## Usage

To translate the *OCaml* declarations and *Gospel* specification contained in
file `f.mli`, just do:
```
gospel2cfml f.mli
```

This command will produce the file `f_mli.v`, which contains the result of
translating *OCaml* and *Gospel* elements into the Separation Logic embedded in
*Coq* by *CFML*.
