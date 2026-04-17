In this branch I put everything that is annoying me in Type, so I can still go forward. It does not mean that everything that lives in Type *needs to* but that I couldn’t immedietaly see how to keep it in Prop.


## History

The disjunction case of the past lemma gave trouble because we had no choice principle to grab the covers we needed.
-> the forcing relation was changed to live in Type

However, this wasn’t enough to build the family of covers needed to apply `cov_union`. We want to build the union-cover of `C`, thus we need to decide which worlds are in `C`. The easy-solution was to add `cov_dec` (as a rule) which decides if a world is in a cover or not. This rule only applies to covers who live in Type (i.e. `C : worlds -> Type`). I tried to minimize the use of Type-covers :

The partial-order still lives in `Prop`, so does the valuation, (partially) the covering relations and the restriction.

