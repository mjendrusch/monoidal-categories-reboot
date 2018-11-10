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
(μ                : Π X Y : C, (obj X) ⊗ (obj Y) ≅ obj (X ⊗ Y))
(μ_natural'       : ∀ (X Y X' Y' : C)
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  (μ X X').hom ≫ map (f ⊗ g) = ((map f) ⊗ (map g)) ≫ (μ Y Y').hom
  . obviously)
-- associativity
(associativity'   : ∀ (X Y Z : C),
    ((μ X Y).hom ⊗ 𝟙 (obj Z)) ≫ (μ (X ⊗ Y) Z).hom ≫ map (associator X Y Z).hom
  = (associator (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ (μ Y Z).hom) ≫ (μ X (Y ⊗ Z)).hom
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (left_unitor (obj X)).hom
  = (ε ⊗ 𝟙 (obj X)) ≫ (μ (tensor_unit C) X).hom ≫ map (left_unitor X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (right_unitor (obj X)).hom
  = (𝟙 (obj X) ⊗ ε) ≫ (μ X (tensor_unit C)).hom ≫ map (right_unitor X).hom
  . obviously)

restate_axiom monoidal_functor.μ_natural'
attribute [simp,search] monoidal_functor.μ_natural
restate_axiom monoidal_functor.left_unitality'
attribute [simp,search] monoidal_functor.left_unitality
restate_axiom monoidal_functor.right_unitality'
attribute [simp,search] monoidal_functor.right_unitality
restate_axiom monoidal_functor.associativity'
attribute [simp,search] monoidal_functor.associativity

end

namespace monoidal_functor
variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : monoidal_category.{u₂ v₂} D]
include 𝒞 𝒟

-- This is unfortunate; we need all sorts of struts to give
-- monoidal functors the features of functors...
@[reducible] def on_iso (F : monoidal_functor C D) {X Y : C} (f : X ≅ Y) : F.obj X ≅ F.obj Y :=
F.to_functor.on_iso f

end monoidal_functor

section

variables (C : Type u₁) [𝒞 : monoidal_category.{u₁ v₁} C]
variables (D : Type u₂) [𝒟 : monoidal_category.{u₂ v₂} D]
variables (E : Type u₃) [ℰ : monoidal_category.{u₃ v₃} E]

include 𝒞 𝒟 ℰ

def monoidal_functor.comp
  (F : monoidal_functor C D) (G : monoidal_functor D E) : monoidal_functor C E :=
{ ε                := G.ε ≫ (G.map F.ε),
  μ                := λ X Y, G.μ (F.obj X) (F.obj Y) ≪≫ G.on_iso (F.μ X Y),
  μ_natural'       := sorry,
  associativity'   := sorry,
  left_unitality'  := sorry,
  right_unitality' := sorry,
  .. (F.to_functor) ⋙ (G.to_functor) }

end

end category_theory.monoidal