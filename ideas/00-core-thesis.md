# Core Thesis: Enriched Composition as Structural Precomputation

## The Problem

In Subset Sum, the brute-force approach explores 2^n branches of a decision tree.
Each branch is a sequence of "include" / "skip" decisions. Classical composition
treats these as opaque functions — you must *execute* the entire path to know its sum.

## The Insight

What if composition itself carried the answer?

In an **enriched category** over (Z, +, 0), each morphism is not a naked function
but a pair (metadata, function). The metadata is the partial sum accumulated along
that path. When you compose two morphisms, the metadata combines via (+).

This means: **the composition operator precomputes the answer structurally**.
You never need to "run" the path to know its sum — it's already in the metadata.

## Why This Might Be Radical (Not Just Memoization)

Memoization and dynamic programming collapse *states* — they say "two paths that
arrive at the same state are equivalent." That's already known to give pseudo-polynomial
time for Subset Sum.

We're asking a different question: **is there a categorical transformation (functor,
adjunction, Kan extension) that restructures the ENTIRE enriched category into one
where the answer is directly readable in polynomial time?**

The metadata isn't just an optimization — it's a *change of category*. We're not
working in Set anymore. We're working in a category enriched over a commutative monoid.
The structure of that monoid interacts with the structure of the decision tree.

## The Question

Does there exist a functor F: C_enriched → D_poly such that:
- F is faithful (preserves the problem structure)
- D_poly has polynomial-time decidable hom-objects
- F preserves the property "this path sums to target"

If yes → P = NP (at least for Subset Sum, which is NP-complete)
If no → we learn something about WHY the enrichment is insufficient
