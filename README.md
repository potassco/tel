# tel

A translator for temporal formulas.

## Usage

To translate a temporal formula to ASP and solve with clingo call

    tel translate 3 < example.tel | clingo -Wnone 0

For further information run

    tel --help

## Input

The `tel` program reads a set of formulas as input. Each formula has to be
terminated with a `.`. Formulas of the following format are supported:

- Atoms
  - `p(t1,...,tn)`
    - similar to what is supported in the input language of gringo
    - the parenthesis are optional if `n` is zero
- Boolean connectives
  - `~ F`
  - `F & G`
  - `F | G`
  - `F -> G`
- Basic temporal connectives
  - for the past
    - `#previous F`
    - `F #since G`
    - `F #trigger G`
  - for the future
    - `#next F`
    - `F #until G`
    - `F #release G`
- Derived temporal connectives (and formulas)
  - for the past
    - `#always- F`
    - `#eventually- F`
    - `#initial`
    - `#previous^ F`
  - for the future
    - `#always+ F`
    - `#eventually+ F`
    - `#final`
    - `#next^ F`
- Disambiguation
  - The grammar uses the following precedences (strongest first)
    1. `~`, `#previous`, `#previous^`, `#next`, `#next^`, `#always+`,
       `#always-`, `#eventually+`, `#eventually-`
    2. `#since`, `#until`, `#release`, `#trigger`
    3. `&`
    4. `|`
    5. `->`
  - `(F)` (parenthesis have to be used when chaining unary connectives)
- Comments
  - strings starting with '%' are ignored until the end of the line

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
