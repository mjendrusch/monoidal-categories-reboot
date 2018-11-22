-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import category_theory.tactics.obviously
open tactic
open category_theory

namespace category_theory.slice

meta def repeat_with_results {α : Type} (t : tactic α) : tactic (list α) :=
(do r ← t,
    s ← repeat_with_results,
    return (r :: s)) <|> return []

meta def repeat_count {α : Type} (t : tactic α) : tactic ℕ :=
do r ← repeat_with_results t,
   return r.length

/--
`slice` is a conv tactic; if the current focus is a composition of several morphisms,
`slice a b` reassociates as needed, and zooms in on the `a`-th through `b`-th morphisms.

Thus if the current focus is `(a ≫ b) ≫ ((c ≫ d) ≫ e)`, then `slice 2 3` zooms to `b ≫ c`.
 -/
meta def slice (a b : ℕ) : conv unit :=
do repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   iterate_range (a-1) (a-1) (do conv.congr, conv.skip),
   k ← repeat_count $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=tt},
   iterate_range (k+1+a-b) (k+1+a-b) conv.congr,
   repeat $ to_expr ``(category.assoc) >>= λ e, tactic.rewrite_target e {symm:=ff},
   rotate 1,
   iterate_exactly (k+1+a-b) conv.skip

end category_theory.slice
