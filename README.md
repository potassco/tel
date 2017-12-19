# tel

A translator for temporal formulas.

## Usage

To translate a temporal formula to ASP and solve with clingo call

    tel translate 3 < formula | clingo 0

For further information run

    tel --help

## Installation

The package can be build using stack. To install stack go to
<https://docs.haskellstack.org> and follow the instructions how to install.

Then you can install `tel` by calling

    stack setup
    stack build
    stack install

Note that this will take some time and requires quite some space on your hard
disk. On unix systems the installed executable will be in `~/.local/bin/tel`,
which you might have to add to your PATH environment variable.

An alternative is to build the program using packages shipping with your
distribution. Development happens on a Debian 9 machine, which ships all the
necessary packages. The required packages are listed in the `tel.cabal` file.
After installing those run

    cabal build
