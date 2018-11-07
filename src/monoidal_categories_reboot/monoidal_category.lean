-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .tensor_product
open category_theory
open tactic

universes u v

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal
class monoidal_category (C : Type u) extends category.{u v} C :=
-- curried tensor product of objects:
(tensor_obj               : C → C → C)
-- curried tensor product of morphisms:
(tensor_hom               : Π {X₁ Y₁ X₂ Y₂ : C}, hom X₁ Y₁ → hom X₂ Y₂ → hom (tensor_obj X₁ X₂) (tensor_obj Y₁ Y₂))
-- tensor product laws:
(tensor_map_id'           : ∀ (X₁ X₂ : C), tensor_hom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj X₁ X₂) . obviously)
(tensor_map_comp'         : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
  tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = (tensor_hom f₁ f₂) ≫ (tensor_hom g₁ g₂) . obviously)
-- tensor unit:
(tensor_unit              : C)
-- associator morphisms:
(associator               : Π X Y Z : C, (tensor_obj (tensor_obj X Y) Z) ⟶ (tensor_obj X (tensor_obj Y Z)))
(associator_inv           : Π X Y Z : C, (tensor_obj X (tensor_obj Y Z)) ⟶ (tensor_obj (tensor_obj X Y) Z))
-- natural isomorphism laws:
(associator_hom_inv_id'   : Π X Y Z : C, (associator X Y Z) ≫ (associator_inv X Y Z) = 𝟙 (tensor_obj (tensor_obj X Y) Z) . obviously)
(associator_inv_hom_id'   : Π X Y Z : C, (associator_inv X Y Z) ≫ (associator X Y Z) = 𝟙 (tensor_obj X (tensor_obj Y Z)) . obviously)
(associator_naturality'   : assoc_natural tensor_obj @tensor_hom associator . obviously)
-- left unitor morphisms:
(left_unitor              : Π X : C, tensor_obj tensor_unit X ⟶ X)
(left_unitor_inv          : Π X : C, X ⟶ tensor_obj tensor_unit X)
-- natural isomorphism laws:
(left_unitor_hom_inv_id'  : Π X : C, (left_unitor X) ≫ (left_unitor_inv X) = 𝟙 (tensor_obj tensor_unit X) . obviously)
(left_unitor_inv_hom_id'  : Π X : C, (left_unitor_inv X) ≫ (left_unitor X) = 𝟙 X . obviously)
(left_unitor_naturality'  : left_unitor_natural tensor_obj @tensor_hom tensor_unit left_unitor . obviously)
-- right unitor morphisms:
(right_unitor             : Π X : C, tensor_obj X tensor_unit ⟶ X)
(right_unitor_inv         : Π X : C, X ⟶ tensor_obj X tensor_unit)
-- natural isomorphism laws:
(right_unitor_hom_inv_id' : Π X : C, (right_unitor X) ≫ (right_unitor_inv X) = 𝟙 (tensor_obj X tensor_unit) . obviously)
(right_unitor_inv_hom_id' : Π X : C, (right_unitor_inv X) ≫ (right_unitor X) = 𝟙 X . obviously)
(right_unitor_naturality' : right_unitor_natural tensor_obj @tensor_hom tensor_unit right_unitor . obviously)
-- pentagon identity:
(pentagon'                : pentagon @tensor_hom associator . obviously)
-- triangle identity:
(triangle'                : triangle @tensor_hom left_unitor right_unitor associator . obviously)

restate_axiom monoidal_category.tensor_map_id'
attribute [simp,ematch] monoidal_category.tensor_map_id
restate_axiom monoidal_category.tensor_map_comp'
attribute [simp,ematch] monoidal_category.tensor_map_comp
restate_axiom monoidal_category.associator_hom_inv_id'
attribute [simp,ematch] monoidal_category.associator_hom_inv_id
restate_axiom monoidal_category.associator_inv_hom_id'
attribute [simp,ematch] monoidal_category.associator_inv_hom_id
restate_axiom monoidal_category.associator_naturality'
attribute [ematch] monoidal_category.associator_naturality
restate_axiom monoidal_category.left_unitor_hom_inv_id'
attribute [simp,ematch] monoidal_category.left_unitor_hom_inv_id
restate_axiom monoidal_category.left_unitor_inv_hom_id'
attribute [simp,ematch] monoidal_category.left_unitor_inv_hom_id
restate_axiom monoidal_category.left_unitor_naturality'
attribute [ematch] monoidal_category.left_unitor_naturality
restate_axiom monoidal_category.right_unitor_hom_inv_id'
attribute [simp,ematch] monoidal_category.right_unitor_hom_inv_id
restate_axiom monoidal_category.right_unitor_inv_hom_id'
attribute [simp,ematch] monoidal_category.right_unitor_inv_hom_id
restate_axiom monoidal_category.right_unitor_naturality'
attribute [ematch] monoidal_category.right_unitor_naturality
restate_axiom monoidal_category.pentagon'
attribute [ematch] monoidal_category.pentagon
restate_axiom monoidal_category.triangle'
attribute [ematch] monoidal_category.triangle

section

variables (C : Type u) [𝒞 : monoidal_category.{u v} C]
include 𝒞

open monoidal_category

infixr ` ⊗ `:80 := tensor_obj
infixr ` ⊗ `:80 := tensor_hom

@[reducible] def monoidal_category.tensor : (C × C) ⥤ C :=
{ obj       := λ X, X.1 ⊗ X.2,
  map'      := λ {X Y : C × C} (f : X ⟶ Y), f.1 ⊗ f.2 }

@[reducible] def monoidal_category.associator_transformation (X Y Z : C) : ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z)) :=
{ hom := associator X Y Z,
  inv := associator_inv X Y Z }

@[reducible] def monoidal_category.left_unitor_transformation (X : C) : (tensor_unit C ⊗ X) ≅ X :=
{ hom := left_unitor X,
  inv := left_unitor_inv X }

@[reducible] def monoidal_category.right_unitor_transformation (X : C) : (X ⊗ tensor_unit C) ≅ X :=
{ hom := right_unitor X,
  inv := right_unitor_inv X }

variables {U V W X Y Z : C}

@[ematch] definition interchange (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z)
  : (f ≫ g) ⊗ (h ≫ k) = (f ⊗ h) ≫ (g ⊗ k) :=
tensor_map_comp C f h g k

@[simp,ematch] lemma interchange_left_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) = (f ≫ g) ⊗ (𝟙 Z) :=
begin
  rw ←interchange,
  simp
end

@[simp,ematch] lemma interchange_right_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) = (𝟙 Z) ⊗ (f ≫ g) :=
begin
  rw ←interchange,
  simp
end

@[ematch] lemma interchange_identities (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) :=
begin
  rw ←interchange,
  rw ←interchange,
  simp
end

end

end category_theory.monoidal
