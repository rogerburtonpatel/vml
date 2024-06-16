# vml
This repository contains the source for $V^{-}$ and $P^{+}$, a subset of Verse and a pattern-based language.


The code is the implementation component of *An Alternative to Pattern Matching,
Inspired by Verse*, my undergraduate senior thesis with Norman Ramsey and Milod
Kazerounian. The repository also contains the source for the paper. The full
paper can be found [here](https://rogerburtonpatel.github.io/fullpaper.pdf). 

## Dependencies 

### To build ML Source

`mosmlc` or `mlton` is required. Compilation instructions for each are below.

`make` is required. 

### To build the paper 

`latexmk` and `xelatex` are required. `simplebnf` is the only package that gave
install trouble to others; if you have latex build issues due to another
package, please open a github issue. 

## Building

### To build ML Source
 While in `src`: 
 
 `make $progname`, where `$progname` is one of `vminus`, `dtran`, or `pplus`,
 builds `$progname`. `make` by iteslf builds `dtran` by default. 

 This build uses `mosmlc`. If you don't have `mosmlc` and you do have `mlton`,
`make $progname-mlton` builds `$progname` (same as above) with `mlton`. 

For example:

`make vminus` -> Builds `vminus` with `mosmlc`. 

`make pplus-mlton` -> Builds `pplus` with `mlton`. 

All targets are built into **bin**. 

### To build the paper

In `tex/thesis`: `make` builds the paper. The builds runs all `bibtex` passes until it
reaches a fix point, so compilation can take a few tens of seconds. 

## Directory Structure 

**src**: source code for `dtran`, `pplus`, and `vminus`. 

**tests**: testing code. Mostly for parsers; correctness testing yet to be made public. 

**bin**: binaries, including scripts. All compiled binaries live here. 

**tex**: tex source and generated pdfs. 

**tex/thesis**: contains the build of full paper. `make` compiles it. `xelatex` is required. 

**tex/.tex-out**: the glut of latex build output lives here. 

**tex/old**: outdated files, or for later use. 

**tex-tech**: source for some of the latex tricks used during paper-writing. 

**tex-util**: latex macros and templates. 

**futurework**: Contains directories that exist as digital reminders for future work. 

## Running the Code

**bin** contains the `vminus`, `pplus`, and `dtran` binaries after compilation.

`vminus` and `pplus` can be executed as an interpreter or with a filename as a
single argument. 

`dtran` is a differentiable compiler, and it takes two arguments: *from* and
*to*. Each of *from* and *to*, separated by a dash to form a single command-line
argument, and an optional filename. Each of *from* and *to* is a language, and
`dtran` will attempt to compile from *from* as source to *to* as target. For
example, `dtran pp-vm` will translate $P^{+}$ to $V^{-}$. All output 
is written to stdout. 

Example commands: 

`dtran pp-vm test.pp` -> Translates `test.pp` to $V^{-}$, writing the result to stdout. 

`dtran vm-vm test.vm` -> Parses and unparses `test.vm`. 

`dtran pp-d` -> Runs `dtran` as an interpreter that takes in $P^{+}$ code and emits $D$ code. 


`dtran` can also execute programs: 

`dtran vm-eval test.vm` -> Interprets and evaluates `test.vm`. 

All language names can be found by running `dtran` with no arguments. 

`dtran` has some limitations; an ongoing bugfix means it currently cannot parse
$D$. A fix is in progress. 

## Bugs, limitations, and contributions

If you want to contribute, please open an issue or PR! 

