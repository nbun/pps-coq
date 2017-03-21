## Installation
Binaries for Windows and MacOS can be found [here](https://coq.inria.fr/download). Unix users may install Coq via the package manager or by compiling the sources, as described [here](https://coq.inria.fr/cocorico/Installation%20of%20Coq%20on%20Linux).

## Compiling Coq programs
The provided Coq files can be compiled by running
``` bash
coq_makefile -f _CoqProject -o Makefile
```
followed by `make`. The generated `Makefile` updates itself upon execution; therefore, subsequent compilations do not require manually using `coq_makefile`. The Coq compiler `coqc` can be invoked manually when working with small projects.

## Working with Coq
There are two popular options for writing code and constructing proofs in Coq: CoqIDE and Proof General. The former is a [graphical tool](https://coq.inria.fr/refman/Reference-Manual018.html) that features basic editing capabilities, a simple interface and allows the user to easily navigate and view a proof and its current (sub)goals.![CoqIDE](images/CoqIDE.png) 

[Proof General](https://proofgeneral.github.io/) is an Emacs extension that, similar to CoqIDE, provides a front-end to Coq for the popular ~~operating system~~ editor. The extension collection [Company-Coq](https://github.com/cpitclaudel/company-coq) includes Proof General and adds even more features, such as prettification of operators and types, powerful auto-completion and other nice-to-have-but-probably-not-necessary functions.

### Proof General

TODO: Introduction + explanation + the rest

`C-c C-n` proof-assert-next-command-interactive

`C-c C-u` proof-undo-last-successful-command 

`C-c C-BS` proof-undo-and-delete-successful-command 

`C-c C-RET` proof-goto-point 

`C-c C-b` proof-process-buffer

`C-c C-r` proof-retract-buffer

`C-c .` proof-electric-terminator-toggle 

