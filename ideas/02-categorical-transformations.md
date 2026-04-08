# Categorical Transformations to Explore

## 1. Left Kan Extension

If we have a functor F: DecisionTree → Enriched, can we compute Lan_F(eval)
where eval checks "does this path hit the target"?

The left Kan extension would "summarize" all paths, potentially collapsing
those with the same metadata. If the Kan extension is computable in poly-time,
we have our transformation.

```
DecisionTree ---F---> Enriched
     |                    |
     | eval               | Lan_F(eval)
     v                    v
   Bool               Bool (but poly-time?)
```

## 2. Adjunction: Free ⊣ Forgetful

Consider the free enriched category over a graph (the decision tree).
The forgetful functor U strips metadata. If the free functor F has
a left adjoint L, then:

  Hom_Enriched(F(x), y) ≅ Hom_Graph(x, U(y))

This could mean: answering questions in the enriched category
(exponential paths with metadata) is equivalent to answering
questions in the underlying graph (polynomial structure).

## 3. Yoneda Embedding

Embed each object in the enriched category via:
  y(a) = Hom(a, -)

The enriched Yoneda lemma says:
  Nat(Hom(a, -), F) ≅ F(a)

If we can show that the enriched hom-functor Hom(start, end)
has a polynomial representation, the natural transformations
give us a poly-time way to extract the answer.

## 4. Monad from Adjunction

Every adjunction gives rise to a monad. If the free/forgetful
adjunction above yields a monad T on the graph category, then
the Kleisli category for T might be where the polynomial computation lives.

The Kleisli morphisms a → T(b) would be "computations that
produce b with side-effects in T" — and T might encode exactly
the partial-sum accumulation.

## 5. Grothendieck Construction

View the enrichment as a fibration. The total category of the
fibration might have structure that makes the problem tractable.
Each fiber is the set of paths with a given partial sum.

## Priority

Start with (2) Free ⊣ Forgetful and (4) Kleisli, as they connect
most directly to the enriched composition operator we've built.
