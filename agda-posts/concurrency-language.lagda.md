---
date: 2021-08-30
title: Concurrency language with small step semantics
author: Guilherme
---

```
{-# OPTIONS --sized-types #-}

open import Data.Bool
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.List
open import Data.Maybe
open import Codata.Thunk
import Codata.Stream as Stream
open Stream using (Stream; _∷_)

infixr 6 _||_
infixr 7 _!!_
data Expr : Set where
  nat : ℕ → Expr
  _||_ : Expr → Expr → Expr
  _!!_ : Expr → Expr → Expr

infixr 2 _—→_
data _—→_ : Expr → ℕ × Maybe Expr → Set where
  ξℕ : ∀ {n}
    → nat n —→ n , nothing
  ξ||ₗ : ∀ {M M' N n}
    → M —→ n , just M'
    → M || N —→ n , just (M' || N)
  ξ||∅ₗ : ∀ {M N n}
    → M —→ n , nothing
    → M || N —→ n , just N
  ξ||ᵣ : ∀ {M N N' n}
    → N —→ n , just N'
    → M || N —→ n , just (M || N')
  ξ||∅ᵣ : ∀ {M N n}
    → N —→ n , nothing
    → M || N —→ n , just M
  ξ!! : ∀ {M M' N n}
    → M —→ n , just M'
    → M !! N —→ n , just (M' !! N)
  ξ!!∅ : ∀ {M N n}
    → M —→ n , nothing
    → M !! N —→ n , just N

||prog = nat 0 || nat 1

_ : ||prog —→ 0 , just (nat 1)
_ = ξ||∅ₗ ξℕ

_ : ||prog —→ 1 , just (nat 0)
_ = ξ||∅ᵣ ξℕ

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

infix 2 _—⇀_
_—⇀_ : Expr → List ℕ → Set
L —⇀ xs = L —↠ xs , nothing

!!-sequence : ∀ {M N xs ys}
  → M —⇀ xs
  → N —⇀ ys
  → M !! N —⇀ xs ++ ys
!!-sequence (_ —→⟨⟩ st1) st2 = _ !! _ —→⟨ ξ!!∅ st1 ⟩ st2
!!-sequence (_ —→⟨ st ⟩ st1) st2 = _ !! _ —→⟨ ξ!! st ⟩ !!-sequence st1 st2

data SingleStep : Expr → Set where
  singleStep : ∀ {L} n L'
    → L —→ n , L'
      ----------
    → SingleStep L

data Steps : Expr → Set where
  steps : ∀ {L} xs
    → L —⇀ xs
      ----------
    → Steps L

-- eval :
--   Stream Bool _
--   → (L : Expr)
--   → Stream Bool _ × Steps L
-- eval sb (nat x) = sb , steps (x ∷ []) (nat x —→⟨⟩ ξℕ)
-- eval sb (M !! N) with eval sb M
-- ... | sb2 , steps xs st with eval sb2 N
-- ...   | sb3 , steps ys st2 = sb3 , steps (xs ++ ys) (!!-sequence st st2)
-- eval (false ∷ stxs) (nat y || N) with eval (stxs .force) N
-- ... | stys , steps ys st = stys , steps (y ∷ ys) (nat y || N —→⟨ ξ||∅ₗ ξℕ ⟩ st)
-- eval (true ∷ stxs)  (nat y || N) with eval (stxs . force) N
-- ... | stys , steps ys st = stys , (steps {!!} {!!})
-- eval (x ∷ xs)     ((L || M) || N)  = {!!}
-- eval (x ∷ xs)     (L !! M || N)    = {!!}

```
