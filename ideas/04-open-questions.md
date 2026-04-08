# Open Questions

## Fundamental

1. **The Compression Question**: Is there a monoidal functor from (Z, +, 0) to
   a finite monoid M such that "sum equals T" is decidable in M?
   - If |M| is polynomial in n (not T), this gives P = NP for Subset Sum
   - Chinese Remainder Theorem flavor? Hash-based compression?

2. **Adjunction Existence**: Does the free enriched category over the decision
   graph have a left adjoint that's polynomial-time computable?

3. **Naturality of the Target Check**: Is "reachedTarget T" a natural
   transformation? If so, between which functors? Naturality would give
   us powerful structural constraints.

## Technical

4. What's the right Haskell encoding of V-enriched categories where V
   is not Hask but an arbitrary monoidal category?

5. Can we use GHC type-level naturals to track the partial sums at the
   type level? This would make invalid paths unrepresentable.

6. Should we use profunctors instead of arrows? A profunctor
   p :: C^op × C → V is exactly an enriched hom-functor.

## Experimental

7. Implement the classical Subset Sum and the enriched version.
   Benchmark. Even if complexity is the same, does the enriched
   structure reveal patterns in which instances are hard?

8. Visualize the enriched hom-object for small instances.
   What does its structure look like? Is there obvious redundancy?

9. Try different enrichment monoids beyond (Z, +, 0):
   - (Z/nZ, +, 0) — modular arithmetic
   - (Bool, OR, False) — just tracks "any element included?"
   - Polynomial rings — metadata is a generating function
