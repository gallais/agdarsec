# agdarsec - Total Parser Combinators in Agda

The motivation and design decisions behind agdarsec are detailed in:

* [this paper](https://gallais.github.io/pdf/agdarsec18.pdf) for the core design
* [this blog post](https://gallais.github.io/blog/instrumenting-agdarsec) for the instrumentation

## Compilation

[![Travis Status](https://api.travis-ci.org/gallais/agdarsec.svg?branch=master)](https://travis-ci.org/gallais/agdarsec)

To typecheck and compile this project you will need:

* Agda version 2.5.4
* Agda's standard library Version 0.16

## Ports

I have ported this library to other dependently-typed languages:

* [parseque](https://github.com/gallais/parseque) is the port to [Coq](https://github.com/coq/coq)
* and [idris-tparsec](https://github.com/gallais/idris-tparsec) the one for [Idris](https://github.com/idris-lang/idris-dev)
