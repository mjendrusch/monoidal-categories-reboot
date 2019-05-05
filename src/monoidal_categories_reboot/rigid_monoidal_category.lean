-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import .monoidal_category
import .braided_monoidal_category

universes v u

namespace category_theory.monoidal

open monoidal_category
class right_duality {C : Sort u} (A A' : C) [monoidal_category.{v} C] :=
(right_unit        : tensor_unit C ⟶ A ⊗ A')
(right_counit      : A' ⊗ A ⟶ tensor_unit C)
(triangle_right_1' : ((𝟙 A') ⊗ right_unit) ≫ (associator A' A A').inv ≫ (right_counit ⊗ (𝟙 A'))
                   = (right_unitor A').hom ≫ (left_unitor A').inv
                   . obviously)
(triangle_right_2' : (right_unit ⊗ (𝟙 A)) ≫ (associator A A' A).hom ≫ ((𝟙 A) ⊗ right_counit)
                   = (left_unitor A).hom ≫ (right_unitor A).inv
                   . obviously)

class left_duality {C : Sort u} (A A' : C) [monoidal_category.{v} C] :=
(left_unit        : tensor_unit C ⟶ A' ⊗ A)
(left_counit      : A ⊗ A' ⟶ tensor_unit C)
(triangle_left_1' : ((𝟙 A) ⊗ left_unit) ≫ (associator A A' A).inv ≫ (left_counit ⊗ (𝟙 A))
                  = (right_unitor A).hom ≫ (left_unitor A).inv
                  . obviously)
(triangle_left_2' : (left_unit ⊗ (𝟙 A')) ≫ (associator A' A A').hom ≫ ((𝟙 A') ⊗ left_counit)
                  = (left_unitor A').hom ≫ (right_unitor A').inv
                  . obviously)

class duality {C : Sort u} (A A' : C) [braided_monoidal_category.{v} C]
  extends right_duality.{v} A A', left_duality.{v} A A'

def self_duality {C : Sort u} (A : C) [braided_monoidal_category.{v} C] :=
duality A A

-- Hmmm, constructivity/universe issues here:
class right_rigid (C : Type u) [monoidal_category.{v+1} C] :=
(right_rigidity' : Π X : C, Σ X' : C, right_duality X X')

class left_rigid (C : Type u) [monoidal_category.{v+1} C] :=
(left_rigidity' : Π X : C, Σ X' : C, left_duality X X')

class rigid (C : Type u) [monoidal_category.{v+1} C]
  extends right_rigid.{v} C, left_rigid.{v} C

class self_dual (C : Sort u) [braided_monoidal_category.{v} C] :=
(self_duality' : Π X : C, self_duality X)

def compact_closed (C : Type u) [symmetric_monoidal_category.{v+1} C] :=
rigid.{v} C

section
open self_dual
open left_duality

instance rigid_of_self_dual
    (C : Type u)
    [braided_monoidal_category.{v+1} C]
    [𝒟 : self_dual.{v+1} C] : rigid.{v} C :=
{ left_rigidity'  := λ X : C, sigma.mk X (self_duality' X).to_left_duality,
  right_rigidity' := λ X : C, sigma.mk X (self_duality' X).to_right_duality }

end

end category_theory.monoidal
