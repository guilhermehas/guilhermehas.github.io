---
date: 2021-08-30
title: Concurrency language with small-step semantics
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
open Stream using (Stream; _∷_; repeat)

infixr 6 _||_
infixr 7 _,,_
data Expr : Set where
  nat : ℕ → Expr
  _||_ : Expr → Expr → Expr
  _,,_ : Expr → Expr → Expr

NextExpr = ℕ × Maybe Expr

infixr 2 _—→_
data _—→_ : Expr → NextExpr → Set where
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
  ξ,, : ∀ {M M' N n}
    → M —→ n , just M'
    → M ,, N —→ n , just (M' ,, N)
  ξ,,∅ : ∀ {M N n}
    → M —→ n , nothing
    → M ,, N —→ n , just N

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

,,-sequence : ∀ {M N xs ys}
  → M —⇀ xs
  → N —⇀ ys
  → M ,, N —⇀ xs ++ ys
,,-sequence (_ —→⟨⟩ st1) st2 = _ ,, _ —→⟨ ξ,,∅ st1 ⟩ st2
,,-sequence (_ —→⟨ st ⟩ st1) st2 = _ ,, _ —→⟨ ξ,, st ⟩ ,,-sequence st1 st2

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

data Finished (N : Expr) : Set where
   done :
       Steps N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N

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
