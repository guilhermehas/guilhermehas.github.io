---
date: 2021-08-30
title: Concurrency language with small-step semantics
author: Guilherme
---

# Motivation

My motivation to formalize a concurrency programming language using small-step semantics
is to use this concept for a no deterministic programming languge.

# Imports

Importing from [Agda standard library](https://github.com/agda/agda-stdlib).

```
{-# OPTIONS --sized-types #-}

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.List
open import Data.Maybe
open import Codata.Thunk
open import Codata.Stream using (Stream; _∷_; repeat)
```

# Defining the language

The programming language is a simple expression that can be a natural number,
two concurrency programs or two programs that happen one next the other.
In the end, the main idea is that this program just returns a list of natural numbers.

```
infixr 6 _||_
infixr 7 _,,_
data Expr : Set where
  nat : ℕ → Expr
  _||_ : Expr → Expr → Expr
  _,,_ : Expr → Expr → Expr
```


# Small-Step

Now, it will be defined the small-step semantic of this programming language:

```
NextExpr = ℕ × Maybe Expr
```

The expression will be reduced to a natural number that it produced or
maybe a new expression if there is still a new program to reduce.

```
infixr 2 _—→_
data _—→_ : Expr → NextExpr → Set where
  ξℕ : ∀ {n}
    ----------------------
    → nat n —→ n , nothing
```

The simplest reduction is when there is a simple program with just a natural number
This program will be reduced to it and there is no programing remaining.

```
  ξ||ₗ : ∀ {M M' N n}
    → M —→ n , just M'
    ------------------------------
    → M || N —→ n , just (M' || N)
```

If there is a parallel program, the left program will be reduced by one step.

```
  ξ||∅ₗ : ∀ {M N n}
    → M —→ n , nothing
    ----------------------
    → M || N —→ n , just N
```

The new program after the left ends in the parallel program is just the right program.

```
  ξ||ᵣ : ∀ {M N N' n}
    → N —→ n , just N'
    ------------------------------
    → M || N —→ n , just (M || N')
```

It is the same thing of a previous step but for the right program.

```
  ξ||∅ᵣ : ∀ {M N n}
    → N —→ n , nothing
    ----------------------
    → M || N —→ n , just M
```

It is the same thing of a previous step but for the right program.

```
  ξ,, : ∀ {M M' N n}
    → M —→ n , just M'
    ------------------------------
    → M ,, N —→ n , just (M' ,, N)
```

When there is a sequence program, the left part is reduced once and the rest of the expression
is just the join of the both of these programs.

```
  ξ,,∅ : ∀ {M N n}
    → M —→ n , nothing
    ----------------------
    → M ,, N —→ n , just N
```

When the left program ends, the rest of the program is the right one.

In this example, a parallel program can be reduced in two ways:

```
||prog = nat 0 || nat 1

_ : ||prog —→ 0 , just (nat 1)
_ = ξ||∅ₗ ξℕ

_ : ||prog —→ 1 , just (nat 0)
_ = ξ||∅ᵣ ξℕ
```

# Multi-step

Now, it will be defined the multi-step of the language.
It can be a zero step, so an expression `M` can go to `M` (`M —↠ M`),
it can be multiple steps (that can be one, two, or any natural number)
or it can be a step that the expression finishes.

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Expr → List ℕ × Maybe Expr → Set where

  _∎ : ∀ M
      ----------------
    → M —↠ [] , just M

  _—→⟨_⟩_ : ∀ L {x xs M N}
    → L —→ x , just M
    → M —↠ xs , N
      ---------------
    → L —↠ x ∷ xs , N

  _—→⟨⟩_ : ∀ L {x}
    → L —→ x , nothing
      --------------------
    → L —↠ [ x ] , nothing

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

When the expression evaluates to nothing, it finishes:

```
infix 2 _—⇀_
_—⇀_ : Expr → List ℕ → Set
L —⇀ xs = L —↠ xs , nothing
```

This is small lemma that you can concat the result of two sequence expressions:

```
,,-sequence : ∀ {M N xs ys}
  → M —⇀ xs
  → N —⇀ ys
  → M ,, N —⇀ xs ++ ys
,,-sequence (_ —→⟨⟩ st1) st2 = _ ,, _ —→⟨ ξ,,∅ st1 ⟩ st2
,,-sequence (_ —→⟨ st ⟩ st1) st2 = _ ,, _ —→⟨ ξ,, st ⟩ ,,-sequence st1 st2
```

# Single-step

The single-step is just the small-step that you hide the result of the small-step in the type.

```
data SingleStep : Expr → Set where
  singleStep : ∀ {L} n L'
    → L —→ n , L'
      ----------
    → SingleStep L
```

With the eval step, I proof that every expression has single-step associated with that.
If the program is parallel, it will consume a boolean from the stream and
this boolean represents which part of the program will be evaluated.
The false represents the left part while true represents the right.

```
eval-step :
  Stream Bool _
  → (L : Expr)
  → Stream Bool _ × SingleStep L
eval-step sxs (nat x) = sxs , (singleStep x nothing ξℕ)
eval-step sxs (M ,, N) with eval-step sxs M
... | sys , singleStep n (just M') st = sys , (singleStep n (just (M' ,, N)) (ξ,, st))
... | sys , singleStep n nothing st = sys , (singleStep n (just N) (ξ,,∅ st))
eval-step (false ∷ sxs) (M || N) with eval-step (sxs .force) M
... | sys , singleStep n (just M') st = sys , (singleStep n (just (M' || N) ) (ξ||ₗ st))
... | sys , singleStep n nothing st = sys , (singleStep n (just N) (ξ||∅ₗ st))
eval-step (true ∷ sxs) (M || N) with eval-step (sxs .force) N
... | sys , singleStep n (just N') st = sys , (singleStep n (just (M || N') ) (ξ||ᵣ st))
... | sys , singleStep n nothing st = sys , (singleStep n (just M) (ξ||∅ᵣ st))
```

# Evaluation

For the definition of evaluation, it will necessary to be defined when an
expression was finished in the evaluation and the steps of the evaluation.

```
data Steps : Expr → Set where
  steps : ∀ {L} xs
    → L —⇀ xs
      ----------
    → Steps L

data Finished (N : Expr) : Set where
   done :
       Steps N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

An expression is finished when it is a value or when there is no more gas
available to calculate it.
In Agda, every computation must terminates. So it is impossible to have
an infinite loop. So when an expression takes so much time
to finish, it runs out of gas and there is no result.

The evaluation finishes when there is proof of multi-step for the value
and it is already finished.

```
eval :
  ℕ
  → Stream Bool _
  → (L : Expr)
  → Finished L
eval 0 sxs L = out-of-gas
eval (suc gas) sxs L with eval-step sxs L
... | sys , singleStep n nothing st = done (steps [ n ] (L —→⟨⟩ st))
... | sys , singleStep n (just M) st with eval gas sys M
...   | out-of-gas = out-of-gas
...   | done (steps xs st2) = done (steps (n ∷ xs) (L —→⟨ st ⟩ st2))
```

The evaluation takes gas and the expression to evaluate.
In the end, it returns the value with proof that the expression evaluates
to this value.

Here, some examples of the evaluation:

```
rfalse = repeat false
rtrue = repeat true
evalf = eval 100 rfalse
evalt = eval 100 rtrue

_ : evalf ||prog ≡ done
  (steps (0 ∷ [ 1 ])
  (nat 0 || nat 1 —→⟨ ξ||∅ₗ ξℕ ⟩
  (nat 1 —→⟨⟩ ξℕ)))
_ = refl

_ : evalt ||prog ≡ done
  (steps (1 ∷ [ 0 ])
  (nat 0 || nat 1 —→⟨ ξ||∅ᵣ ξℕ ⟩
  (nat 0 —→⟨⟩ ξℕ)))
_ = refl

_ : evalf (nat 0 ,, nat 1) ≡ done
  (steps (0 ∷ [ 1 ])
  (nat 0 ,, nat 1 —→⟨ ξ,,∅ ξℕ ⟩
  (nat 1 —→⟨⟩ ξℕ)))
_ = refl
```
