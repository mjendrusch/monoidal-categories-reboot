-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import ..monoidal_category
import ..braided_monoidal_category
open category_theory
open tactic

universes u v

namespace category_theory.monoidal

section

open monoidal_category
open braided_monoidal_category

def types_left_unitor (α : Type u) : punit × α → α := λ X, X.2
def types_left_unitor_inv (α : Type u) : α → punit × α := λ X, ⟨punit.star, X⟩
def types_right_unitor (α : Type u) : α × punit → α := λ X, X.1
def types_right_unitor_inv (α : Type u) : α → α × punit := λ X, ⟨X, punit.star⟩
def types_associator (α β γ : Type u) : (α × β) × γ → α × (β × γ) :=
λ X, ⟨X.1.1, ⟨X.1.2, X.2⟩⟩
def types_associator_inv (α β γ : Type u) : α × (β × γ) → (α × β) × γ :=
λ X, ⟨⟨X.1, X.2.1⟩, X.2.2⟩
def types_braiding (α β : Type u) : α × β → β × α :=
λ X, ⟨X.2, X.1⟩
def types_braiding_inv := types_braiding

instance types : symmetric_monoidal_category.{(u+1)} (Type u) :=
{ tensor_obj := λ X Y, X × Y,
  tensor_hom := λ _ _ _ _ f g, prod.map f g,
  tensor_unit := punit,
  left_unitor := λ X,
    { hom := types_left_unitor X,
      inv := types_left_unitor_inv X },
  right_unitor := λ X,
    { hom := types_right_unitor X,
      inv := types_right_unitor_inv X },
  associator := λ X Y Z,
    { hom := types_associator X Y Z,
      inv := types_associator_inv X Y Z},
  braiding := λ X Y,
    { hom := types_braiding X Y,
      inv := types_braiding_inv Y X } }

end

end category_theory.monoidal
