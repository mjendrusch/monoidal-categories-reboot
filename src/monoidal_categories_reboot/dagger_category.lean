-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import category_theory.tactics.obviously -- Give ourselves access to `rewrite_search`
import .slice_tactic
import .braided_monoidal_category
import .rigid_monoidal_category

universes u v

namespace category_theory.dagger
open category_theory
open category_theory.monoidal

class dagger_structure
    (C : Sort u) [𝒞 : category.{v} C] :=
(dagger_hom : Π {X Y : C} (f : X ⟶ Y), Y ⟶ X)
(dagger_comp'       : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z), dagger_hom (f ≫ g) = (dagger_hom g) ≫ (dagger_hom f)
                    . obviously)
(dagger_id'         : ∀ X, dagger_hom (𝟙 X) = 𝟙 X . obviously)
(dagger_involution' : ∀ {X Y : C} (f : X ⟶ Y), dagger_hom (dagger_hom f) = f . obviously)

restate_axiom dagger_structure.dagger_comp'
attribute [simp,search] dagger_structure.dagger_comp'
restate_axiom dagger_structure.dagger_id'
attribute [simp,search] dagger_structure.dagger_id'
restate_axiom dagger_structure.dagger_involution'
attribute [simp,search] dagger_structure.dagger_involution'

postfix ` † `:10000 := dagger_structure.dagger_hom

def dagger_structure.dagger
    {C : Sort u} [𝒞 : category.{v} C] [dagger_structure C] : Cᵒᵖ ⥤ C :=
{ map := λ {X Y} (f), (has_hom.hom.unop f)†,
  obj := λ X, unop X }

def is_unitary
    {C : Sort u} [category.{v} C] [dagger_structure C]
    {X Y : C} (f : X ≅ Y) : Prop :=
f.inv = f.hom†

open category_theory.monoidal.monoidal_category
open category_theory.monoidal.braided_monoidal_category
class monoidal_dagger_structure
    (C : Sort u) [symmetric_monoidal_category.{v u} C]
    extends dagger_structure.{u v} C :=
(dagger_tensor'        : ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), (f ⊗ g)† = f† ⊗ g†
                       . obviously)
(associator_unitary'   : ∀ X Y Z : C, is_unitary (associator X Y Z) . obviously)
(left_unitor_unitary'  : ∀ X : C, is_unitary (left_unitor X) . obviously)
(right_unitor_unitary' : ∀ X : C, is_unitary (right_unitor X) . obviously)
(braiding_unitary'     : ∀ X Y : C, is_unitary (braiding X Y) . obviously)

end category_theory.dagger
