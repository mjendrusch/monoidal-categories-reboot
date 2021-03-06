-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .tensor_product
import .monoidal_category
import tactic.rewrite_search
import tactic.interactive

open category_theory
open tactic

universe u

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal

section

open monoidal_category

structure monoidal_functor
  (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
  (D : Sort u₂) [𝒟 : monoidal_category.{v₂} D]
extends category_theory.functor C D :=
-- unit morphism
(ε               : tensor_unit D ≅ obj (tensor_unit C))
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
  = (ε.hom ⊗ 𝟙 (obj X)) ≫ (μ (tensor_unit C) X).hom ≫ map (left_unitor X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (right_unitor (obj X)).hom
  = (𝟙 (obj X) ⊗ ε.hom) ≫ (μ X (tensor_unit C)).hom ≫ map (right_unitor X).hom
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
variables {C : Sort u₁} [𝒞 : monoidal_category.{v₁} C]
variables {D : Sort u₂} [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟

-- This is unfortunate; we need all sorts of struts to give
-- monoidal functors the features of functors...
@[reducible] def on_iso (F : monoidal_functor C D) {X Y : C} (f : X ≅ Y) : F.obj X ≅ F.obj Y :=
F.to_functor.map_iso f

@[search] lemma map_id (F : monoidal_functor C D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id' X

@[search] lemma map_comp (F : monoidal_functor C D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp' f g

end monoidal_functor

section

variables (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
variables (D : Sort u₂) [𝒟 : monoidal_category.{v₂} D]
variables (E : Sort u₃) [ℰ : monoidal_category.{v₃} E]

include 𝒞 𝒟 ℰ

open tactic.rewrite_search.tracer
-- set_option profiler true

def monoidal_functor.comp
  (F : monoidal_functor C D) (G : monoidal_functor D E) : monoidal_functor C E :=
{ ε                := G.ε ≪≫ (G.on_iso F.ε),
  μ                := λ X Y, G.μ (F.obj X) (F.obj Y) ≪≫ G.on_iso (F.μ X Y),
  μ_natural'       :=
  begin
    tidy,
    /- `rewrite_search` says -/ -- FIXME actually, its output is broken
    conv_lhs { congr, skip, erw [←map_comp] },
    conv_lhs { erw [monoidal_functor.μ_natural] },
    conv_lhs { congr, skip, erw [map_comp] },
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [monoidal_functor.μ_natural] },
    conv_rhs { erw [←category.assoc] },
  end,
  associativity'   := λ X Y Z,
  begin
    -- obviously fails here, but it seems like it should be doable!
    dsimp,
    conv { to_rhs,
      rw ←interchange_right_identity,
      slice 3 4,
      rw ← G.map_id,
      rw ← G.μ_natural,
    },
    -- rewrite_search { view := visualiser, trace_summary := tt, explain := tt, max_iterations := 50 }, -- fails
    conv { to_rhs,
      slice 1 3,
      rw ←G.associativity,
    },
    -- rewrite_search (saw/visited/used) 137/23/16 expressions during proof of category_theory.monoidal.monoidal_functor.comp
    conv { to_lhs,
      rw ←interchange_left_identity,
      slice 2 3,
      rw ← G.map_id,
      rw ← G.μ_natural, },
    repeat { rw category.assoc },
    repeat { rw ←G.map_comp },
    rw F.associativity,
  end,
  left_unitality'  := λ X,
  begin
    -- Don't attempt to read this; it is a Frankenstein effort of Scott + rewrite_search
    dsimp,
    rw G.left_unitality,
    rw ←interchange_left_identity,
    repeat {rw category.assoc},
    apply congr_arg,
    /- `rewrite_search` says -/ -- FIXME actually, its output is broken
    rw F.left_unitality,
    conv_lhs { congr, skip, erw [map_comp] },
    conv_lhs { erw [←category.id_app] },
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, skip, erw [map_id] },
    conv_rhs { erw [←category.assoc] },
    erw map_comp,
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    rw G.right_unitality,
    rw ←interchange_right_identity,
    repeat {rw category.assoc},
    apply congr_arg,
    /- `rewrite_search` says -/ -- FIXME actually, its output is broken
    rw F.right_unitality,
    conv_lhs { congr, skip, erw [map_comp] },
    conv_lhs { erw [←category.id_app] },
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, erw [map_id] },
    conv_rhs { erw [←category.assoc] },
    erw map_comp,
  end,
  .. (F.to_functor) ⋙ (G.to_functor) }

end

end category_theory.monoidal