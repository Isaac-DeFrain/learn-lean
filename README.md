# Lambda Calculus and Combinators

## A minor typo (pg. 198-199)

The last equation on pg. 198 reads as follows:

```lean
u : *, p : (u → *) (λx : u . λy : p a . x) : (Πx : u . (p x → p x))
```

I believe that the `a` should be an `x` and the following `x` should be a `y` and thus it should read:

```lean
u : *, p : (u → *) (λx : u . λy : p x . y) : (Πx : u . (p x → p x))
```

## A more serious typo (pg. 212-213)

The last line on pg. 212 has the definition of the existential quantifier projection operator, it reads:

```lean
λu : *. λv : (u → *) . λw : * . λz : (Πx : u . v x → w) . λy : (Πx : u . v x) . y w z
```

I believe this definition is incorrect. It did not type check it in [`lean4`](https://github.com/leanprover/lean4) so I played around with the definition until I got it to satisfy the property expressed on pg. 213, lines 10 and 12. This is what I propose:

```lean
λu : * . λv : (u → *) . λw : * . λz : (Πx : u . v x → w) . λy : (Πw : * . (Πx : u . v x → w) → w) . y w z
```

[Errata](/Errata.lean) contains the relevant lean4 proofs.

## Quickstart

Install lean4 via the [nix flake](./flake.nix).

Execute the code / check the proofs:

```shell
lake exe lambda-calculus
```
