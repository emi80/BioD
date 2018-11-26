# BioD [![Build Status](https://travis-ci.org/biod/BioD.svg?branch=master)](https://travis-ci.org/biod/BioD) [![DUB Package](https://img.shields.io/badge/dub-v0.1.0-red.svg)](https://code.dlang.org/packages/biod)

[BioD](https://github.com/biod/BioD) is a fast and memory efficient bioinformatics library written in the [D programming language](http://dlang.org).

BioD aims to:

* Provide a platform for writing high-performance bioinformatics applications in the D programming language. BioD achieves this by:
  - automatic parallelization of tasks where possible
  - reducing the GC overhead by avoiding unnecessary memory allocations
* Offer support for manipulating common biological data formats

## Why D?

[D](http://www.d-lang.,org) is a language that suits parallel programming
because  the compiler provides certain guarantees. The D programmming language is both a low and high-level
hybrid object orientated and functional (OOP/FP) programming language. D provides a templating/generics features that are
far easier than that of C++. Few languages if any matches these set of features.

## D programming language resources
* [The D Programming Language](https://www.amazon.com/D-Programming-Language-Andrei-Alexandrescu/dp/0321635361) by Andrei Alexandrecu 
* [Programming in D](http://ddili.org/ders/d.en/index.html) by Ali Çehreli.

## Current development
Our aim is to provide several modules to work with biological datasets for example
one of our main focus is to provide a modules for working with high throughput sequencing for example a
native bamreader and bamwriter that is really fast and easy to use. With D we have an good way to write performance parsers, particularly with three typical scenarios:

1. Go through a BAM file a read at a time
2. Go through a BAM file a nucleotide at a time (pileup)
3. Go through a BAM file with a sliding window

The sliding window is a derivation of the first - a read at a time or
a nucleotide at a time.


# Install

The current default is to provide the path to the checked out repo to the D-compiler. For example
in sambamba we use

    DFLAGS = -wi -I. -IBioD -g

# Usage

See the [examples directory](https://github.com/biod/BioD/tree/master/examples)
for examples and usage.

BioD is also a crucial part of the [sambamba](https://github.com/biod/sambamba) tool.

# Contributing

Simply clone the repository on github and put in a pull request.

# BioD contributors and support

See
[contributors](https://github.com/biod/BioD/graphs/contributors). For
support use the [issue tracker](https://github.com/biod/BioD/issues) or contact

* [Pjotr Prins](https://github.com/pjotrp)
* [Artem Tarasov](https://github.com/lomereiter)
* [George Githinji](https://github.com/George-Githinji)

# License

BioD is licensed under the liberal MIT (expat) [license](./LICENSE).
