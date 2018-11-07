-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .tensor_product
import .monoidal_category
open category_theory
open tactic

universes u₁ u₂ u₃ v₁ v₂ v₃

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal

section

open monoidal_category

structure monoidal_functor
  (C : Type u₁) [𝒞 : monoidal_category.{u₁ v₁} C]
  (D : Type u₂) [𝒟 : monoidal_category.{u₂ v₂} D]
extends category_theory.functor C D :=
-- unit morphism
(ε               : tensor_unit D ⟶ obj (tensor_unit C))
-- natural transformation
(μ_hom           : Π X Y : C, (obj X) ⊗ (obj Y) ⟶ obj (X ⊗ Y))
(μ_natural       : ∀ (X Y X' Y' : C)
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  (μ_hom X X') ≫ map' (f ⊗ g) = ((map' f) ⊗ (map' g)) ≫ (μ_hom Y Y')
  . obviously)
-- associativity
(associativity   : ∀ (X Y Z : C),
    (μ_hom X Y ⊗ 𝟙 (obj Z)) ≫ μ_hom (X ⊗ Y) Z ≫ map' (associator_hom X Y Z)
  = associator_hom (obj X) (obj Y) (obj Z) ≫ (𝟙 (obj X) ⊗ μ_hom Y Z) ≫ μ_hom X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality  : ∀ X : C,
    left_unitor_hom (obj X)
  = (ε ⊗ 𝟙 (obj X)) ≫ μ_hom (tensor_unit C) X ≫ map' (left_unitor_hom X)
  . obviously)
(right_unitality : ∀ X : C,
    right_unitor_hom (obj X)
  = (𝟙 (obj X) ⊗ ε) ≫ μ_hom X (tensor_unit C) ≫ map' (right_unitor_hom X)
  . obviously)

attribute [simp,ematch] monoidal_functor.left_unitality
attribute [simp,ematch] monoidal_functor.right_unitality
attribute [ematch] monoidal_functor.associativity

end

section

variables (C : Type u₁) [𝒞 : monoidal_category.{u₁ v₁} C]
variables (D : Type u₂) [𝒟 : monoidal_category.{u₂ v₂} D]
variables (E : Type u₃) [ℰ : monoidal_category.{u₃ v₃} E]

include 𝒞 𝒟 ℰ

def monoidal_functor.comp
  (F : monoidal_functor C D) (G : monoidal_functor D E) : monoidal_functor C E :=
{ obj             := λ X, G.obj (F.obj X),
  map'            := λ {X Y : C} (f : X ⟶ Y), G.map' (F.map' f),
  map_id'         := sorry,
  map_comp'       := sorry,
  ε               := sorry,
  μ_hom           := sorry,
  μ_natural       := sorry,
  associativity   := sorry,
  left_unitality  := sorry,
  right_unitality := sorry }

end

end category_theory.monoidal