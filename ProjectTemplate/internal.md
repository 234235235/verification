# Internal notes

## antlr4 build chain
```bash
alias antlr4='java -Xmx500M -cp "/usr/local/lib/antlr-4.7.1-complete.jar:$CLASSPATH" org.antlr.v4.Tool'
alias grun='java org.antlr.v4.gui.TestRig'
```

Assuming the correct position of the jar file.

## How to rebuild parser

First `cd src/parser`, then `antlr4 Muds.g4 -visitor -no-listener`

In case you want to regenerate the program graph generator from a default
visitor:```bash
cp MudsBaseVisitor.java MudsToPGVisitor.java
sed -i "s/\([^a-zA-Z]\)T\([^a-zA-Z]\)/\1AstNode\2/g" MudsToPGVisitor.java
sed -i "s/@Override//" MudsToPGVisitor.java   #useless by now
```

By hand, for testing of the grammar:
```bash
antlr4 Muds.g4
javac Muds*java
grun Muds bexpr -gui < sample_bexpr_formula
```

### Part0

* VLTS

Relabelling
Parallel composition of VLTS

### Part1
1/ You are given a CTL* formula, say if it is a CTL formula
2/ Put it in normal form
3/ Modelcheck it !

