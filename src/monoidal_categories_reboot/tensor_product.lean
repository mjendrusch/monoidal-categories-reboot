-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
open category_theory

universes u v


open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans

namespace category_theory.monoidal

@[reducible] def tensor_obj_type
  (C : Type u) [category.{u v} C] :=
C → C → C

@[reducible] def tensor_hom_type
  {C : Type u} [category.{u v} C] (tensor_obj : tensor_obj_type C) : Type (max u v) :=
Π {X₁ Y₁ X₂ Y₂ : C}, hom X₁ Y₁ → hom X₂ Y₂ → hom (tensor_obj X₁ X₂) (tensor_obj Y₁ Y₂)

local attribute [tidy] tactic.assumption

def assoc_obj
  {C : Type u} [category.{u v} C] (tensor_obj : tensor_obj_type C) : Type (max u v) :=
Π X Y Z : C, (tensor_obj (tensor_obj X Y) Z) ≅ (tensor_obj X (tensor_obj Y Z))

def assoc_natural
  {C : Type u} [category.{u v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
  (tensor_hom (tensor_hom f₁ f₂) f₃) ≫ (assoc Y₁ Y₂ Y₃).hom = (assoc X₁ X₂ X₃).hom ≫ (tensor_hom f₁ (tensor_hom f₂ f₃))

def left_unitor_obj
  {C : Type u} [category.{u v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_unit : C) : Type (max u v) :=
Π X : C, (tensor_obj tensor_unit X) ≅ X

def left_unitor_natural
  {C : Type u} [category.{u v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (tensor_unit : C)
  (left_unitor : left_unitor_obj tensor_obj tensor_unit) : Prop :=
∀ {X Y : C} (f : X ⟶ Y),
  (tensor_hom (𝟙 tensor_unit) f) ≫ (left_unitor Y).hom = (left_unitor X).hom ≫ f

def right_unitor_obj
  {C : Type u} [category.{u v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_unit : C) : Type (max u v) :=
Π (X : C), (tensor_obj X tensor_unit) ≅ X

def right_unitor_natural
  {C : Type u} [category.{u v} C]
  (tensor_obj : tensor_obj_type C)
  (tensor_hom : tensor_hom_type tensor_obj)
  (tensor_unit : C)
  (right_unitor : right_unitor_obj tensor_obj tensor_unit) : Prop :=
∀ {X Y : C} (f : X ⟶ Y),
  (tensor_hom f (𝟙 tensor_unit)) ≫ (right_unitor Y).hom = (right_unitor X).hom ≫ f

@[reducible] def pentagon
  {C : Type u} [category.{u v} C]
  {tensor_obj : tensor_obj_type C}
  (tensor_hom : tensor_hom_type tensor_obj)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ W X Y Z : C,
  (tensor_hom (assoc W X Y).hom (𝟙 Z)) ≫ (assoc W (tensor_obj X Y) Z).hom ≫ (tensor_hom (𝟙 W) (assoc X Y Z).hom)
  = (assoc (tensor_obj W X) Y Z).hom ≫ (assoc W X (tensor_obj Y Z)).hom

@[reducible] def triangle
  {C : Type u} [category.{u v} C]
  {tensor_obj : tensor_obj_type C} {tensor_unit : C}
  (tensor_hom : tensor_hom_type tensor_obj)
  (left_unitor : left_unitor_obj tensor_obj tensor_unit)
  (right_unitor : right_unitor_obj tensor_obj tensor_unit)
  (assoc : assoc_obj tensor_obj) : Prop :=
∀ X Y : C,
  (assoc X tensor_unit Y).hom ≫ (tensor_hom (𝟙 X) (left_unitor Y).hom)
  = tensor_hom (right_unitor X).hom (𝟙 Y)

end category_theory.monoidal
