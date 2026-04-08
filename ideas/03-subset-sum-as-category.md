# Subset Sum as a Category

## Setup

Given: a set S = {s1, s2, ..., sn} of integers, a target T.
Question: is there a subset of S that sums to T?

## The Decision Category C_S

**Objects**: Decision states (i, included_so_far)
  - i ranges from 0 to n (how many elements we've decided on)
  - But we don't need to track the full subset — that's the point

**Morphisms**: For each element s_i, two morphisms from state i to state i+1:
  - include_i : state_i → state_{i+1}   with metadata (Sum s_i)
  - skip_i    : state_i → state_{i+1}   with metadata (Sum 0)

**Composition**: enriched, carries partial sums

## Key Observation

A path from state_0 to state_n is a sequence of n decisions.
There are 2^n such paths. BUT their metadata lives in Z (integers),
which has at most (sum of all elements + 1) distinct values.

The enriched category "knows" this — the hom-object Hom(state_0, state_n)
is not just a set of 2^n arrows, it's an object in (Z, +, 0) that
has polynomial structure when the weights are polynomial.

## The Gap

This is exactly why Subset Sum is "weakly NP-complete" — it's solvable
in pseudo-polynomial time O(n * T) via dynamic programming.

For a truly polynomial algorithm, we need T to not matter.
The categorical question becomes:

**Can we quotient the enriched hom-object by an equivalence relation
that is coarser than "same sum" but still preserves the answer,
AND has polynomially many equivalence classes regardless of T?**

This is where the radical transformation must happen.

## Ideas

- Hashing / modular arithmetic on the metadata monoid?
- Replacing (Z, +) with a finite quotient monoid?
- Finding an adjunction that "compresses" the hom-object?

The enriched framework makes these questions precise and tractable
to explore algebraically.
