# cpl
A (partial) implementation of Tatsuya Hagino's categorical programming language (cpl).

## Usage

Clone this repo and run
```sh
dune build
dune install
```
then start interactive cpl based on the definition file by
```sh
cpl -f <definition file path>
```

## Features

`cpl` will read definitions in your definition file specified in command line. The format for a definition is
```
(left | right) <functor name>[(arg list)] with <factorizer name> is
    <1st natural transformation name> : <expression including functors and args> -> <expression including functors and args>;
    ...
end
```

Also refer to `examples/example.cpl`.

Then `cpl` will start an environment for you to do each of the following commands:

- `simp <expression>;`. `cpl` will simplify (in FULL mode) the expression.

- `var <name>;`. `cpl` will record the name and view it as a free morphism variable, which can be used later.

- `let <name> = <expression>;`. `cpl` will bind the expression to the name, and you can use it later.

Note: (i) remember the semicolons; (ii) `I` denotes the identity morphism.

## Examples

In this directory, start the example definition file with
```
cpl -f ./examples/example.cpl
```
Then, you can input as follows: (things following `cpl>` is what you input)
```
./examples/example.cpl-info> right object 1 defined.
./examples/example.cpl-info> left object nat defined.
./examples/example.cpl-info> right object prod(+, +) defined.
./examples/example.cpl-info> right object exp(-, +) defined.
./examples/example.cpl-info> left object list(+) defined.
./examples/example.cpl-info> left object coprod(+, +) defined.
./examples/example.cpl-info> right object inflist(+) defined.
cpl> let add=eval.pair(pr(curry(pi2),curry(s.eval)).pi1,pi2);
info> add : prod(nat, nat) -> nat defined.
cpl> simp add.pair(s.0,s.s.0);
info> s.s.s.0
 : 1 -> nat
cpl> let mult=eval.prod(pr(curry(0.!),curry(add.pair(eval,pi2))),I);
info> mult : prod(nat, nat) -> nat defined.
cpl> simp mult.pair(s.s.0,s.s.s.0);
info> s.s.s.s.s.s.0
 : 1 -> nat
cpl> var f;
info> f defined.
cpl> var g;
info> g defined.
cpl> simp pi1.prod(f,g).pair(0,s.0);
info> f.0
 : 1 -> X1
```

## TODO

- better error messages
    - parsing error
    - type check failure
    - computation failure

## Uninstall

```sh
rm $(which cpl)
```
