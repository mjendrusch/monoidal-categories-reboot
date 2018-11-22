-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import .monoidal_category
import .braided_monoidal_category

universes u v

namespace category_theory.monoidal

open monoidal_category
class right_duality {C : Type u} (A A' : C) [monoidal_category.{u v} C] :=
(right_unit        : tensor_unit C ⟶ A ⊗ A')
(right_counit      : A' ⊗ A ⟶ tensor_unit C)
(triangle_right_1' : ((𝟙 A') ⊗ right_unit) ≫ (associator A' A A').inv ≫ (right_counit ⊗ (𝟙 A'))
                   = (right_unitor A').hom ≫ (left_unitor A').inv
                   . obviously)
(triangle_right_2' : (right_unit ⊗ (𝟙 A)) ≫ (associator A A' A).hom ≫ ((𝟙 A) ⊗ right_counit)
                   = (left_unitor A).hom ≫ (right_unitor A).inv
                   . obviously)

class left_duality {C : Type u} (A A' : C) [monoidal_category.{u v} C] :=
(left_unit        : tensor_unit C ⟶ A' ⊗ A)
(left_counit      : A ⊗ A' ⟶ tensor_unit C)
(triangle_left_1' : ((𝟙 A) ⊗ left_unit) ≫ (associator A A' A).inv ≫ (left_counit ⊗ (𝟙 A))
                  = (right_unitor A).hom ≫ (left_unitor A).inv
                  . obviously)
(triangle_left_2' : (left_unit ⊗ (𝟙 A')) ≫ (associator A' A A').hom ≫ ((𝟙 A') ⊗ left_counit)
                  = (left_unitor A').hom ≫ (right_unitor A').inv
                  . obviously)

class duality {C : Type u} (A A' : C) [braided_monoidal_category.{u v} C]
  extends right_duality.{u v} A A', left_duality.{u v} A A'

class self_duality {C : Type u} (A : C) [braided_monoidal_category.{u v} C]
  extends duality A A

class is_right_rigid (C : Type u) [monoidal_category.{u v} C] :=
(right_rigid' : Π X : C, Σ X' : C, right_duality X X')

class is_left_rigid (C : Type u) [monoidal_category.{u v} C] :=
(left_rigid' : Π X : C, Σ X' : C, left_duality X X')

class is_rigid (C : Type u) [monoidal_category.{u v} C]
  extends is_right_rigid.{u v} C, is_left_rigid.{u v} C

class is_self_dual (C : Type u) [braided_monoidal_category.{u v} C] :=
(self_dual' : Π X : C, self_duality X)

class right_rigid_monoidal_category (C : Type u)
  extends monoidal_category.{u v} C, is_right_rigid.{u v} C

class left_rigid_monoidal_category (C : Type u)
  extends monoidal_category.{u v} C, is_left_rigid.{u v} C

class rigid_monoidal_category (C : Type u)
  extends monoidal_category.{u v} C, is_rigid.{u v} C

class compact_closed_category (C : Type u)
  extends symmetric_monoidal_category.{u v} C, is_rigid.{u v} C

class self_dual_category (C : Type u)
  extends symmetric_monoidal_category.{u v} C, is_self_dual.{u v} C

section
open is_self_dual
open self_duality
open left_duality

instance rigid_of_self_dual
    (C : Type u)
    [braided_monoidal_category.{u v} C]
    [𝒟 : is_self_dual.{u v} C] : is_rigid.{u v} C :=
{
  left_rigid'  := λ X : C, sigma.mk X (self_dual' X).to_duality.to_left_duality,
  right_rigid' := λ X : C, sigma.mk X (self_dual' X).to_duality.to_right_duality
}

end

instance compact_closed_category_of_symmetric_monoidal_category_and_is_rigid
    (C : Type u)
    [symmetric_monoidal_category.{u v} C]
    [is_rigid.{u v} C] : compact_closed_category.{u v} C :=
{}

instance self_dual_category_of_symmetric_monoidal_category_and_is_rigid
    (C : Type u)
    [symmetric_monoidal_category.{u v} C]
    [is_self_dual.{u v} C] : self_dual_category.{u v} C :=
{}

end category_theory.monoidal
