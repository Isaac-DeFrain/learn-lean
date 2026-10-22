# Learn Lean

## Intro to lean

[IntroToLean](/IntroToLean/) modules follow [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/):

1. Introduction
2. Dependent Type Theory
3. [Propositions and Proofs](/IntroToLean/PropositionsAndProofs.lean)
4. [Quantifiers and Equality](/IntroToLean/QuantifiersAndEquality.lean)
5. [Tactics](/IntroToLean/Tactics.lean)
6. [Interacting with Lean](/IntroToLean/InteractingWithLean.lean)
7. [Inductive Types](/IntroToLean/InductiveTypes.lean)
8. [Induction and Recursion](/IntroToLean/InductionAndRecursion.lean)
9. [Structures and Records](/IntroToLean/StructuresAndRecords.lean)
10. [Types Classes](/IntroToLean/TypeClasses.lean)
11. [The Conversion Tactic Mode](/IntroToLean/TheConversionTacticMode.lean)
12. [Axioms and Computation](/IntroToLean/AxiomsAndComputation.lean)

## Lambda Calculus and Combinators

[Lambda Calculus and Combinators](https://www.amazon.com/Lambda-Calculus-Combinators-Introduction-Roger-Hindley/dp/0521898854) pg. 212, last line, has the definition of the _existential quantifier projection operator_. It reads:

$$
proj \equiv λu : *. \ λv : (u → *) . \ λw : * . \ λz : (Πx : u . \ v x → w) . \ λy : (Πx : u . \ v x) . \ y w z
$$

This definition is incorrect as it does not type check in [`lean4`](https://github.com/leanprover/lean4). I played around with it until I got it to satisfy the properties expressed on pg. 213, lines 10 and 12.

$$
proj \ u v w z (D' u v x y) : w
$$

and

$$
proj \ u v w z (D' u v x y) =_β zxy
$$

I propose the correction:

$$
proj \equiv λu : * . \ λv : (u → *) . \ λw : * . \ λz : (Πx : u . \ v x → w) . \ λy : (Πt : * . \ (Πx : u . \ v x → t) → t) . \ y w z
$$

[Errata](/LambdaCalculus/Errata.lean) contains the relevant lean4 proofs.

## Quickstart

Install lean4 via the [nix flake](./flake.nix).

Execute the code / check the proofs:

```shell
lake exe errata
```
