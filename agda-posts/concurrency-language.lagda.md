---
date: 2021-11-03
title: Concurrency language with small-step semantics
author: Guilherme
---

# Motivation

My motivation to formalize a concurrency programming language using small-step semantics
is to use this concept for a no deterministic programming language.

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

The programming language is a simple command that can be a natural number,
two concurrency programs, or two programs that happen one next to the other.
In the end, the main idea is that this program just returns a list of natural numbers.

```
infixr 6 _||_
infixr 7 _,,_
data Command : Set where
  print : ℕ → Command
  _||_ : Command → Command → Command
  _,,_ : Command → Command → Command
```


# Small-Step

Now, it will be defined the small-step semantic of this programming language:

```
NextCommand = ℕ × Maybe Command
```

The command will be reduced to a natural number that it produced or
maybe a new command if there is still a new program to reduce.

```
variable
  m n : ℕ
  M M' N N' : Command

infixr 2 _—→_
data _—→_ : Command → NextCommand → Set where
  ξℕ : print n —→ n , nothing
```

The simplest reduction is when there is a simple program with just a natural number.
This program will be reduced to it and there is no program remaining.

```
  ξ||ₗ : M —→ m , just M'
         ------------------------------
         → M || N —→ m , just (M' || N)
```

If there is a parallel program, the left program will be reduced by one step.

```
  ξ||∅ₗ : M —→ m , nothing
          ----------------------
          → M || N —→ m , just N
```

The new program after the left ends in the parallel program is just the right program.

```
  ξ||ᵣ : N —→ n , just N'
         ------------------------------
         → M || N —→ n , just (M || N')
```

It is the same thing of a previous step but for the right program.

```
  ξ||∅ᵣ : N —→ n , nothing
          ----------------------
          → M || N —→ n , just M
```

It is the same thing as a previous step but for the right program.

```
  ξ,, : M —→ m , just M'
       -----------------------------
       → M ,, N —→ m , just (M' ,, N)
```

When there is a sequence program, the left part is reduced once and the rest of the command
is just the join of both of these programs.

```
  ξ,,∅ : M —→ m , nothing
       ----------------------
       → M ,, N —→ m , just N
```

When the left program ends, the rest of the program is the right one.

In this example, a parallel program can be reduced in two ways:

```
||prog = print 0 || print 1

_ : ||prog —→ 0 , just (print 1)
_ = ξ||∅ₗ ξℕ

_ : ||prog —→ 1 , just (print 0)
_ = ξ||∅ᵣ ξℕ
```

# Multi-step

Now, it will be defined the multi-step of the language.
It can be a zero-step, so a command `M` can go to `M` (`M —↠ M`),
it can be multiple steps (that can be one, two, or any natural number)
or it can be a step that the command finishes.

```
infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Command → List ℕ × Maybe Command → Set where

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

When the command evaluates to nothing, it finishes:

```
infix 2 _—⇀_
_—⇀_ : Command → List ℕ → Set
L —⇀ xs = L —↠ xs , nothing
```

This is a small lemma that you can concatenate the result of two sequence commands:

```
,,-sequence : ∀ {M N xs ys}
  → M —⇀ xs
  → N —⇀ ys
  → M ,, N —⇀ xs ++ ys
,,-sequence (_ —→⟨⟩ st1) st2 = _ ,, _ —→⟨ ξ,,∅ st1 ⟩ st2
,,-sequence (_ —→⟨ st ⟩ st1) st2 = _ ,, _ —→⟨ ξ,, st ⟩ ,,-sequence st1 st2
```

# Single-step

The single-step is just the small step that you hide the result of the small step in the type.

```
data SingleStep : Command → Set where
  singleStep : ∀ {L} n L'
    → L —→ n , L'
      ----------
    → SingleStep L
```

With the eval step, I prove that every command has a single step associated with that.
If the program is parallel, it will consume a boolean from the stream and
this boolean represents which part of the program will be evaluated.
The false represents the left part while true represents the right.

```
eval-step :
  Stream Bool _
  → (L : Command)
  → Stream Bool _ × SingleStep L
eval-step sxs (print x) = sxs , (singleStep x nothing ξℕ)
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
command was finished in the evaluation and the steps of the evaluation.

```
data Steps : Command → Set where
  steps : ∀ {L} xs
    → L —⇀ xs
      ----------
    → Steps L

data Finished (N : Command) : Set where
   done :
       Steps N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N
```

A command is finished when it is a value or when there is no more gas
available to calculate it.
In Agda, every computation must terminate. So it is impossible to have
an infinite loop. So when a command takes so much time
to finish, it runs out of gas and there is no result.

The evaluation finishes when there is proof of multi-step for the value
and it is already finished.

```
eval :
  ℕ
  → Stream Bool _
  → (L : Command)
  → Finished L
eval 0 sxs L = out-of-gas
eval (suc gas) sxs L with eval-step sxs L
... | sys , singleStep n nothing st = done (steps [ n ] (L —→⟨⟩ st))
... | sys , singleStep n (just M) st with eval gas sys M
...   | out-of-gas = out-of-gas
...   | done (steps xs st2) = done (steps (n ∷ xs) (L —→⟨ st ⟩ st2))
```

The evaluation takes gas and the command to evaluate.
In the end, it returns the value with proof that the command evaluates
this value.

Here, some examples of the evaluation:

```
rfalse = repeat false
rtrue = repeat true
evalf = eval 100 rfalse
evalt = eval 100 rtrue

_ : evalf ||prog ≡ done
  (steps (0 ∷ [ 1 ])
  (print 0 || print 1 —→⟨ ξ||∅ₗ ξℕ ⟩
  (print 1 —→⟨⟩ ξℕ)))
_ = refl

_ : evalt ||prog ≡ done
  (steps (1 ∷ [ 0 ])
  (print 0 || print 1 —→⟨ ξ||∅ᵣ ξℕ ⟩
  (print 0 —→⟨⟩ ξℕ)))
_ = refl

_ : evalf (print 0 ,, print 1) ≡ done
  (steps (0 ∷ [ 1 ])
  (print 0 ,, print 1 —→⟨ ξ,,∅ ξℕ ⟩
  (print 1 —→⟨⟩ ξℕ)))
_ = refl
```
