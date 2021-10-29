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

Now, it will be defined the small step semantic of this programming language:

```
infixr 2 _—→_
data _—→_ : Expr → Expr → Set where
  ξ₁ : ∀ {m m' n}
    → m —→ m'
    → m + n —→ m' + n
  ξ₂ : ∀ {m n n'}
    → n —→ n'
    → m + n —→ m + n'
  ϕ0 : ∀ {n} → nat 0 + n —→ n
  ϕ+ : ∀ {m n} → nat (suc m) + nat n —→ nat m + nat (suc n)

_ : nat 0 + nat 0 —→ nat 0
_ = ϕ0
```

The first two steps are reduction of some part of the addition.
`ϕ0` is related to the reduction when the left part is zero.
`ϕ+` is the reduction when the left part is the successor of a natural number.
 The definitions of `ϕ0` and `ϕ+` look like the induction definition of addition.
 While `ξ₁` and `ξ₂` are extra steps.

# Multi step

Now, it will be defined the multi step of the language.
It can be a zero step, so an expression `M` can go to `M` (`M —↠ M`)
or a multiple step (that can be one, two or any natural number).

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

# Values

Value represents its normal form. It is the final answer when the expression is fully evaluated.

```
data Value : Expr → Set where
  nat  : ∀ x
      -------------
    → Value (nat x)
```

# Progress

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
progress (M + N) with progress M
... | step M—→M' = step (ξ₁ M—→M')
... | done (nat zero) = step ϕ0
... | done (nat (suc x)) with progress N
...   | step N—→N' = step (ξ₂ N—→N')
...   | done (nat _) = step ϕ+

data Finished (N : Expr) : Set where
   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

data Steps : Expr → Set where
  steps : ∀ {L N}
    → L —↠ N
    → Finished N
      ----------
    → Steps L

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

_ : eval 100 (nat 2 + nat 2) ≡ steps
  (nat 2 + nat 2 —→⟨ ϕ+ ⟩
   nat 1 + nat 3 —→⟨ ϕ+ ⟩
   nat 0 + nat 4 —→⟨ ϕ0 ⟩
   nat 4 ∎)
   (done (nat 4))
_ = refl

_ : eval 100 (nat 1 + nat 1 + nat 2) ≡ steps
  (nat 1 + nat 1 + nat 2 —→⟨ ξ₂ ϕ+ ⟩
   nat 1 + nat 0 + nat 3 —→⟨ ξ₂ ϕ0 ⟩
   nat 1 + nat 3         —→⟨ ϕ+    ⟩
   nat 0 + nat 4         —→⟨ ϕ0    ⟩
   nat 4 ∎)
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
         → M —↠ M'
           ---------------
         → L + M —↠ L + M'
appR-cong {L}{M}{M'} (M ∎) = L + M ∎
appR-cong {L}{M}{M'} (M —→⟨ r ⟩ rs) = L + M —→⟨ ξ₂ r ⟩ appR-cong rs

abs-cong : ∀ {M M' N N'}
         → M —↠ M'
         → N —↠ N'
           ----------
         → M + N —↠ M' + N'
abs-cong (M ∎) (N ∎) = M + N ∎
abs-cong (M ∎) (N —→⟨ st ⟩ N') = M + N —→⟨ ξ₂ st ⟩ abs-cong (M ∎) N'
abs-cong (M —→⟨ st ⟩ M') (N ∎) = M + N —→⟨ ξ₁ st ⟩ abs-cong M' (N ∎)
abs-cong (M —→⟨ stm ⟩ M') (N —→⟨ stn ⟩ N') = M + N —→⟨ ξ₁ stm ⟩ abs-cong M' (N —→⟨ stn ⟩ N')

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

par-refl : ∀ {M} → M ⇛ M
par-refl {nat x} = pnat
par-refl {M + N} = papp par-refl par-refl

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

beta-par : ∀ {M N}
  → M —→ N
    ------
  → M ⇛ N
beta-par ϕ0 = pzero
beta-par ϕ+ = padd
beta-par (ξ₁ st) = papp (beta-par st) par-refl
beta-par (ξ₂ st) = papp par-refl (beta-par st)

par-betas : ∀ {M N}
  → M ⇛ N
    ------
  → M —↠ N
par-betas pnat = nat _ ∎
par-betas pzero = nat zero + _ —→⟨ ϕ0 ⟩ _ ∎
par-betas padd = nat (suc _) + nat _ —→⟨ ϕ+ ⟩ nat _ + nat (suc _) ∎
par-betas (papp {M} {M'} {N} {N'} p₁ p₂) =
  begin
  M  + N  —↠⟨ appL-cong (par-betas p₁) ⟩
  M' + N  —↠⟨ appR-cong (par-betas p₂) ⟩
  M' + N' ∎

pars-betas : ∀ {M N}
  → M ⇛* N
    ------
  → M —↠ N
pars-betas (M ∎₂) = M ∎
pars-betas (L ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)

infix 25 _⁺
_⁺ : Expr → Expr
nat x ⁺ = nat x
(nat zero + s₂) ⁺ = s₂
(nat (suc x) + nat y) ⁺ = nat x + nat (suc y)
(s₁@(nat (suc x)) + s₂@(s₃ + s₄)) ⁺ = s₁ ⁺  +  s₂ ⁺
(s₁@(s₃ + s₄) + s₂) ⁺ = s₁ ⁺  +  s₂ ⁺

par-nat : ∀ {x M}
  → nat x ⇛ M
  → M ≡ nat x
par-nat pnat = refl

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
... | done (nat (suc x)) with progress⇛ N
...   | step x = step (papp pnat x)
...   | done (nat x) = step padd
```
