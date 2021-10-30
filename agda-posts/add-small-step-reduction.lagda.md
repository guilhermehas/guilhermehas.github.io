---
date: 2021-08-28
title: Using small step reduction in addition
author: Guilherme
---

# Motivation

The objective of this project is to do a minimalistic example of small step semantics using
the concepts of the book [Programming Language Foundations in Agda](https://plfa.github.io/).

# Imports

Importing from [Agda standard library](https://github.com/agda/agda-stdlib).

```
open import Data.Nat hiding (_+_)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to ⟨_,_⟩)
```

# Defining the language

The language is a simple expression that can be a natural number or a sum of two expressions.

```
infixr 6 _+_
data Expr : Set where
  nat : ℕ → Expr
  _+_ : Expr → Expr → Expr
```

## Values

Value represents its normal form. It is the final answer when the expression is fully evaluated.

```
data Value : Expr → Set where
  nat  : ∀ x
      -------------
    → Value (nat x)
```

# Small Step

Now, it will be defined the small step semantic of this programming language:

```
infixr 2 _—→_
data _—→_ : Expr → Expr → Set where
  ξ₁ : ∀ {m m' n}
    → m —→ m'
    → m + n —→ m' + n
  ξ₂ : ∀ {m n n'}
    → Value m
    → n —→ n'
    → m + n —→ m + n'
  ϕ0 : ∀ {n} → nat 0 + nat n —→ nat n
  ϕ+ : ∀ {m n} → nat (suc m) + nat n —→ nat m + nat (suc n)

_ : nat 0 + nat 0 —→ nat 0
_ = ϕ0
```

The first two steps are reduction of some part of the addition.
`ϕ0` is related to the reduction when the left part is zero.
`ϕ+` is the reduction when the left part is the successor of a natural number.
 The definitions of `ϕ0` and `ϕ+` look like the induction definition of addition.
 While `ξ₁` and `ξ₂` are extra steps.

## Deterministic

With determinism, it is only possible to have one step of reduction.
If there are two, both reduce to the same expression.

```
deterministic : ∀ {L M N}
  → L —→ M
  → L —→ N
      ------
  → M ≡ N
deterministic ϕ0 ϕ0 = refl
deterministic ϕ+ ϕ+ = refl
deterministic (ξ₁ LM) (ξ₁ LN) with deterministic LM LN
... | refl = refl
deterministic (ξ₁ ()) (ξ₂ (nat x) LN)
deterministic (ξ₂ (nat x) LM) (ξ₁ ())
deterministic (ξ₂ x LM) (ξ₂ x₁ LN) with deterministic LM LN
... | refl = refl
```

## Progress

Progress means that the expression is a value or there is a next step to reduce.

```
data Progress (M : Expr) : Set where
  step : ∀ {N}
    → M —→ N
      ----------
    → Progress M

  done :
      Value M
      ----------
    → Progress M
```

I will show that every expression has this property:

```
progress : ∀ M → Progress M
progress (nat x) = done (nat x)
progress (M + N) with ⟨ progress M , progress N ⟩
... | ⟨ step x , snd ⟩ = step (ξ₁ x)
... | ⟨ done x , step x₁ ⟩ = step (ξ₂ x x₁)
... | ⟨ done (nat zero) , done (nat y) ⟩ = step ϕ0
... | ⟨ done (nat (suc x)) , done (nat y) ⟩ = step ϕ+
```

## Multi step

Now, it will be defined the multi step of the language.
It can be a zero step, so an expression `M` can go to `M` (`M —↠ M`)
or it can be a multiple step (that can be one, two or any natural number).

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Expr → Expr → Set where

  _∎ : ∀ M
      --------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N
```

## Evaluation

For the definition evaluation, it will be necessary to defined when an
expression was finished in the evaluation and the steps of the evaluation.

```
data Finished (N : Expr) : Set where
   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

A expression is finished when it is a value or when there is no more gas
available to calculate it.
In Agda, every computation must terminates. So it is impossible to have
an infinite loop. So when an expression takes so much time
to finish, it runs out of gas and there is no result.

```
data Steps : Expr → Set where
  steps : ∀ {L N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L
```

The evaluation finishes when there is a proof of multi step for the value
and it is already finished.

```
eval :
    ℕ
  → (L : Expr)
    -----------
  → Steps L
eval zero L = steps (L ∎) out-of-gas
eval (suc n) L with progress L
... | done x = steps (L ∎) (done x)
... | step {M} L—→M with eval n M
...   | steps M—→N fin = steps (L —→⟨ L—→M ⟩ M—→N) fin
```

The evaluation takes gas and the expression to evaluate.
In the end, it returns the value with a proof that the expression evaluates
to this value.

Here, some examples of the evaluation:

```
_ : eval 100 (nat 2 + nat 2) ≡ steps
  (nat 2 + nat 2 —→⟨ ϕ+ ⟩
   nat 1 + nat 3 —→⟨ ϕ+ ⟩
   nat 0 + nat 4 —→⟨ ϕ0 ⟩
   nat 4 ∎)
   (done (nat 4))
_ = refl

_ : eval 100 (nat 1 + nat 1 + nat 2) ≡ steps
    (nat 1 + nat 1 + nat 2 —→⟨ ξ₂ (nat 1) ϕ+ ⟩
       nat 1 + nat zero + nat 3 —→⟨ ξ₂ (nat 1) ϕ0 ⟩
       nat 1 + nat 3 —→⟨ ϕ+ ⟩ nat zero + nat 4 —→⟨ ϕ0 ⟩ nat 4 ∎)
   (done (nat 4))
_ = refl

_ : eval 100 ((nat 1 + nat 1) + nat 2) ≡ steps
  ((nat 1 + nat 1) + nat 2 —→⟨ ξ₁ ϕ+ ⟩
   (nat 0 + nat 2) + nat 2 —→⟨ ξ₁ ϕ0 ⟩
    nat 2 + nat 2          —→⟨ ϕ+    ⟩
    nat 1 + nat 3          —→⟨ ϕ+    ⟩
    nat 0 + nat 4          —→⟨ ϕ0    ⟩
    nat 4 ∎)
  (done (nat 4))
_ = refl
```

## Proofs for later use

I will prove some axioms to use it later in the part of parallel reduction:

```
—↠-trans : ∀ {L M N}
         → L —↠ M
         → M —↠ N
         → L —↠ N
—↠-trans (M ∎) mn = mn
—↠-trans (L —→⟨ r ⟩ lm) mn = L —→⟨ r ⟩ (—↠-trans lm mn)

infixr 2 _—↠⟨_⟩_

_—↠⟨_⟩_ : ∀ L {M N}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = —↠-trans L—↠M M—↠N

appL-cong : ∀ {L L' M}
         → L —↠ L'
           ---------------
         → L + M —↠ L' + M
appL-cong {L}{L'}{M} (L ∎) = L + M ∎
appL-cong {L}{L'}{M} (L —→⟨ r ⟩ rs) = L + M —→⟨ ξ₁ r ⟩ appL-cong rs

appR-cong : ∀ {L M M'}
         → Value L
         → M —↠ M'
           ---------------
         → L + M —↠ L + M'
appR-cong {L}{M}{M'} VL (M ∎) = L + M ∎
appR-cong {L}{M}{M'} VL (M —→⟨ r ⟩ rs) = L + M —→⟨ ξ₂ VL r ⟩ appR-cong VL rs

abs-cong : ∀ {M M' N N'}
         → Value M'
         → M —↠ M'
         → N —↠ N'
           ----------
         → M + N —↠ M' + N'
abs-cong VM (M ∎) (N ∎) = M + N ∎
abs-cong VM (M ∎) (N —→⟨ st ⟩ N') = M + N —→⟨ ξ₂ VM st ⟩ abs-cong VM (M ∎) N'
abs-cong VM (M —→⟨ st ⟩ M') (N ∎) = M + N —→⟨ ξ₁ st ⟩ abs-cong VM M' (N ∎)
abs-cong VM (M —→⟨ stm ⟩ M') (N —→⟨ stn ⟩ N') = M + N —→⟨ ξ₁ stm ⟩ abs-cong VM M' (N —→⟨ stn ⟩ N')
```

# Parallel Reduction

The parallel reduction is good for doing reductions in parallel,
so it can run faster in a multi core computer.

## Single step

Here, the definition of single step of the parallel reduction.

```
infix 2 _⇛_

data _⇛_ : Expr → Expr → Set where
  pnat : ∀ {x}
      -----------------
    → nat x ⇛ nat x

  papp : ∀ {L L′ M M′}
    → L ⇛ L′
    → M ⇛ M′
      ---------------
    → L + M ⇛ L′ + M′

  pzero : ∀ {N}
    → nat 0 + N ⇛ N

  padd : ∀ {m n}
    → nat (suc m) + nat n ⇛ nat m + nat (suc n)
```

The biggest difference of this reduction is `papp`, that
does two reductions at the same time.
It can run faster in a multi core computer.

## Multi step

The sequences of parallel reduction will be defined in this way:

```
infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎₂

data _⇛*_ : Expr → Expr → Set where
  _∎₂ : ∀ M
      --------
    → M ⇛* M

  _⇛⟨_⟩_ : ∀ L {M N}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
```

## Theorems for latter use

Some theorems to use latter:

```
par-refl : ∀ {M} → M ⇛ M
par-refl {nat _} = pnat
par-refl {_ + _} = papp par-refl par-refl

beta-par : ∀ {M N}
  → M —→ N
    ------
  → M ⇛ N
beta-par ϕ0 = pzero
beta-par ϕ+ = padd
beta-par (ξ₁ st) = papp (beta-par st) par-refl
beta-par (ξ₂ _ st) = papp par-refl (beta-par st)

par-nat : ∀ {x M}
  → nat x ⇛ M
  → M ≡ nat x
par-nat pnat = refl
```

## Progress

I will define progress in the same way that I defined previouly.
It will be used to prove that an expression is already a value
or there is a step to reduce.

```
data Progress⇛ (M : Expr) : Set where
  step : ∀ {N}
    → M ⇛ N
      ----------
    → Progress⇛ M

  done :
      Value M
      ----------
    → Progress⇛ M

progress⇛ : ∀ M → Progress⇛ M
progress⇛ (nat x) = done (nat x)
progress⇛ (M + N) with progress⇛ M
... | step st = step (papp st par-refl)
... | done (nat zero) = step pzero
... | done (nat (suc _)) with progress⇛ N
...   | step st = step (papp pnat st)
...   | done (nat _) = step padd
```
