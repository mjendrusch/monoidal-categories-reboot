-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.binary_products
import category_theory.limits.terminal
import ..braided_monoidal_category

open category_theory
open category_theory.monoidal

@[obviously] meta def obviously_products := tactic.tidy { tactics := extended_tidy_tactics }

universes u v

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C] [has_binary_products.{u v} C]
include 𝒞

def binary_product.braiding (P Q : C) : limits.prod P Q ≅ limits.prod Q P :=
{ hom := prod.lift (prod.snd P Q) (prod.fst P Q),
  inv := prod.lift (prod.snd Q P) (prod.fst Q P) }

def binary_product.symmetry (P Q : C) : (binary_product.braiding P Q).hom ≫ (binary_product.braiding Q P).hom = 𝟙 _ :=
begin
  dunfold binary_product.braiding,
  obviously,
end

def binary_product.associativity (P Q R : C) : (limits.prod (limits.prod P Q) R) ≅ (limits.prod P (limits.prod Q R)) :=
{ hom := prod.lift (prod.fst _ _ ≫ prod.fst _ _) (prod.lift (prod.fst _ _ ≫ prod.snd _ _) (prod.snd _ _)),
  inv := prod.lift (prod.lift (prod.fst _ _) (prod.snd _ _ ≫ prod.fst _ _)) (prod.snd _ _ ≫ prod.snd _ _),
  hom_inv_id' := begin ext; simp; rw ← category.assoc; simp, end,
  inv_hom_id' := begin ext; simp; rw ← category.assoc; simp, end }

end category_theory.limits

open category_theory.limits

namespace category_theory.monoidal

variables {C : Type u} [𝒞 : category.{u v} C] [has_products.{u v} C]
include 𝒞

instance : has_binary_products.{u v} C := has_binary_products_of_has_products
instance : has_terminal.{u v} C := has_terminal_of_has_products C

instance monoidal_of_has_products : monoidal_category.{u v} C :=
{ tensor_obj := λ X Y, limits.prod X Y,
  tensor_hom := λ _ _ _ _ f g, limits.prod.map f g,
  tensor_unit := terminal C,
  tensor_map_id' := sorry,
  tensor_map_comp' := sorry,
  associator := sorry,
  associator_naturality' := sorry,
  left_unitor := sorry,
  left_unitor_naturality' := sorry,
  right_unitor := sorry,
  right_unitor_naturality' := sorry,
  pentagon' := sorry,
  triangle' := sorry }


end category_theory.monoidal