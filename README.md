# TinyML
TinyML is an interpreter (mainly a type checker) for a tiny subset of expressions of the language ML.

This project was developed as final project for the exam in Functional Languages 2022-2023 held by Prof. [Alvise Spanò](https://github.com/alvisespano) in Univeristy of Padova. 
The original skeleton of the project can be found at the following [Functional Languages repository](https://github.com/alvisespano/FunctionalLanguages-UniPD/tree/main/2022-23/TinyML).

## Implementation
The skeleton already contains:
- **Lexer**: parses the source code into tokens (Lexer.fsl);
- **Parser**: receives the output of the lexer as input and produces an Abstract Syntax Tree (Parsers.fsy);
- **Type checker**: checks the types of the expressions (Typing.fs);
- **Evaluator**: evaluates the expressions (Eval.fs).

The goal of the project was to implement a type inference algorithm, to be used while checking the correctness of the types of the expressions.
