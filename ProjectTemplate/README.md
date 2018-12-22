# Muds checker project

## Architecture of the project

* `dependencies/` some binaries required by the project
* `src/parser/` sub directory (package) for parsing facilities (__don't look, don't touch__)
* `src/mudspg/` sub directory (package) for program graph and temporal formula structures (__don't touch__, you may want to have a look)
* `src/mudschecker/` sub directory (package) for the labelled transition system (__don't touch__, you may want to have a look)
* `src/helper/`sub directory (package) with helper functions you may want to use/modify
* `src/`  main directory of the project, we provided you with a template
* `samples/` sample model files, in Muds language
* `bin/` compiled project files

The main source code you will be asked to write in the project assignments has
to be located in the `src/` directory. For the first part of the project, you
are given a template answer `src/Part1.java` which each function to implement.

You may create sub-directories but you are not allowed to modify already existing files.
Grading of your submission will consist in dumping your source file into
a fresh folder, re-initialize pre-existing files, then making several calls to the
implemented functions of class `Part1` with several test inputs and checking
for the output.

As a consequence, you may write additional messages on stdout/stderr at your
convenience, as long as implemented methods have the correct signature
and required semantics.

## Input format
Example files can be found in the `samples` directory, but you are encouraged
to write your own. As a matter of fact, grading will involve test cases of this
repository but also new original examples. Some of them will target the
scalability of your implementation (think of the complexity of your
algorithms !) so you may want to design such examples too.

### Muds language
In order to describe models, a toy language called "Muds" has been developed
for this project. It is a subset of the Modest language 
[[http://www.modestchecker.net/]] used by the dependable system&software chair.

You can find the full grammar of this language in the `src/parser/Muds.g4`
file. A document with the full semantics of Muds language is available on
__dcms__.

### Temporal formulae
Temporal formulae, should it be CTL, LTL or others, are formula composed
of boolean operations over variables of a model, and composed of the usual
temporal modalities: boolean operations, quantification over paths (E, A)
and linear time modalities (X, U, W, G, F...).

We emphasize here that temporal formulas are __not necessarily__ CTL or LTL
formula and the first task of your model checking procedure would be to
check that the formula given as an input fits in the corresponding class.


## Changelog
### Rev1
Initial release
### Rev2
* fixed Eventually symbol ("G"->"F"). Should not affect code as this symbol is only used for debugging (toString) purpose
* fixed missing ";" in `samples/prog0`
### Rev3
* add support for parenthesis in integer expressions
### Rev4
* missing parenthesis in samples `goat` and `squared` for the property
### Rev5
* fixed parallel update of variables
### Rev6
* Project part2 content
* decrease ';' priority, so that if(g) P1 else P2; P3 = {if(g) P1 else P2}; P3
* add parenthesis on toString of formulae
### Rev7
* fixed parallel updates of variables (bis)
* fixed translation from LTL to NBA (negation case)
* merge jhoafparser and owl jar files (to avoid conflicts)
