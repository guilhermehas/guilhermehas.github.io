---
date: 2026-01-07
title: KeYther
author: Guilherme
---
# Latest achievements

We are pleased to announce the publication of **[An Axiomatisation of Solidity Memory and Storage](https://doi.org/10.1007/978-3-032-10444-1_5)** at the
23rd International Conference on Software Engineering and Formal Methods on November 2025.

# KeYther: A new theorem prover for Solidity Verification

KeYther is a theorem prover that we are creating for Solidity, which is the main programming language for the biggest smart contract plataform: Ethereum. KeYther is based on KeY system, that is used to verify Java programs using dynamic logic (which is a proof calculus on symbolic execution).

The basis of a program logic for a programming language is the formalisation of the data types offered by, and definable in, the language. In this work, we developed an axiomatisation of Solidity's data types, which is essentially an algebraic specification of these data types. The axioms, or rules, are meant to symbolically execute operations on symbolic expressions appearing in logical formulas. In on going work, this axiomatisation is embedded in a (symbolic execution based) proof calculus for Solidity dynamic logic. However, it can be equally used by other verification approaches, based on Hoare logic or weakest precondition calculi.

## Memory

In our work, we formalised a model of volatile memory that works like a memory table with pointers. Because of that, the copy is shallow. In addition, Solidty has arbitrarily nested data structures.
Therefore, the formalisation creates an identity for each sub-structure, and nested structures are formalised as a list of fields.

## Storage

The permanent storage works as value data. Therefore, every copy is a deep copy. We formalised storage in two ways: lazy and eager:

- In the eager formalisation, the storage is formalised as a tree, which is more intuitive.
- In the lazy formalisation, the storage is formalised as a list of key-pathes and values. So it has a flat data structure.

## Copying between Storage and Memory

In Solidity, it is possible to copy from storage to memory and vice-versa. We did also both formalisation of lazy and eager copy.
The eager does the "real copy" while the lazy delays the actual construction of the copy to the point where we read from the copy. We did some formalisation in Lean theorem prover that the eager approach respect the lazy definition.

# Related Work

The work of Diego Marmsoler and Achim D. Brucker of **Denotational semantics of Solidity in Isabelle/HOL** has the axiomatization of memory and storage, but does not achieve any high degree of automation.

The paper **SMT-Friendly formalisation of the Solidity Memory Model** has good automation because it relies on Boogie, which uses Z3 (an SMT solver). However, the memory and storage are still not fully covered.

Solidifier is another great theorem prover with high level of automation. However, it is a bounded model checker, so it can not verify all possible runs.

In conclusion, our work is the only one with full formalisation of memory and storage and with high degree of automation.
