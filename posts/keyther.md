---
date: 2026-01-07
title: KeYther
author: Guilherme
---

KeYther is a theorem prover that I am creating for Solidity, which is the main programming language for the biggest smart contract plataform: Ethereum. KeYther is based on KeY system, that is used to verify Java programs using dynamic logic (which is a proof calculus on symbolic execution).

The basis of a program logic for a programming language is the formalisation of the data types offered by, and definable in, the language. In this work, we already did an axiomatisation of Solidity's data types, which is essentially an algebraic specification of these data types. The axioms, or rules, are meant to symbolically execute operations on symbolic expressions appearing in logical formulas. In future work, this axiomatisation will be embedded in a (symbolic execution based) proof calculus for Solidity dynamic logic. However, it can be equally used by other verification approaches, based on Hoare logic or weakest precondition calculi.
