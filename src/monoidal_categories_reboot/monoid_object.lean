-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import .monoidal_category
import .braided_monoidal_category
import tidy.rewrite_search
import .monoidal_functor
import .slice_tactic

open tidy.rewrite_search.metric
open tidy.rewrite_search.strategy
open tidy.rewrite_search.tracer
open category_theory.slice

universes u v

namespace category_theory.monoidal

open monoidal_category
class monoid_object {C : Type u} (M : C) [monoidal_category.{u v} C] :=
(unit        : tensor_unit C ⟶ M)
(product     : M ⊗ M ⟶ M)
(pentagon'   : (associator M M M).hom ≫ ((𝟙 M) ⊗ product) ≫ product
             = (product ⊗ (𝟙 M)) ≫ product . obviously)
(left_unit'  : (left_unitor M).hom = (unit ⊗ (𝟙 M)) ≫ product . obviously)
(right_unit' : (right_unitor M).hom = ((𝟙 M) ⊗ unit) ≫ product . obviously)

restate_axiom monoid_object.pentagon'
attribute [simp,search] monoid_object.pentagon
restate_axiom monoid_object.left_unit'
attribute [simp,search] monoid_object.left_unit
restate_axiom monoid_object.right_unit'
attribute [search] monoid_object.right_unit

section
open braided_monoidal_category
open monoid_object

@[reducible]
def reassociate_and_braid_product {C : Type u} (X Y : C) [symmetric_monoidal_category.{u v} C] :=
(associator X Y (X ⊗ Y)).hom ≫ ((𝟙 X) ⊗ (associator Y X Y).inv) ≫
((𝟙 X) ⊗ (braiding Y X).hom ⊗ (𝟙 Y)) ≫ ((𝟙 X) ⊗ (associator X Y Y).hom) ≫
(associator X X (Y ⊗ Y)).inv

-- TODO: prove that the tensor product of two monoid objects is
-- again a monoid object in a symmetric monoidal category.
-- This is trivial on paper via string diagrams.
-- Would it be possible to write a string diagram tactic?
instance product_monoid_object_of_monoid_object
    {C : Type u} (M N : C) [symmetric_monoidal_category.{u v} C]
    [ℳ : monoid_object.{u v} M] [𝒩 : monoid_object.{u v} N] :
    monoid_object (M ⊗ N) :=
{ unit        := (left_unitor (tensor_unit C)).inv ≫ (ℳ.unit ⊗ 𝒩.unit),
  product     := reassociate_and_braid_product M N ≫ (ℳ.product ⊗ 𝒩.product),
  pentagon'   := sorry,
  left_unit'  := sorry,
  right_unit' := sorry }

end

class monoid_morphism
    {C : Type u} [monoidal_category.{u v} C] 
    {M M' : C} [monoid_object.{u v} M] [monoid_object.{u v} M']
    (f : M ⟶ M') :=
(square'   : (f ⊗ f) ≫ monoid_object.product M' = monoid_object.product M ≫ f . obviously)
(triangle' : monoid_object.unit M ≫ f = monoid_object.unit M' . obviously)

restate_axiom monoid_morphism.square'
attribute [search] monoid_morphism.square
restate_axiom monoid_morphism.triangle'
attribute [search] monoid_morphism.triangle

class is_commutative {C : Type u} (M : C) [symmetric_monoidal_category.{u v} C] [monoid_object M] :=
(symmetry' : (braided_monoidal_category.braiding M M).hom ≫ monoid_object.product M = monoid_object.product M)

restate_axiom is_commutative.symmetry'
attribute [search] is_commutative.symmetry'

-- TODO: rephrase this section as a monoid object in the category C^{op}.
section

class comonoid_object {C : Type u} (M : C) [monoidal_category.{u v} C] :=
(counit        : M ⟶ tensor_unit C)
(coproduct     : M ⟶ M ⊗ M)
(copentagon'   : coproduct ≫ ((𝟙 M) ⊗ coproduct) ≫ (associator M M M).inv
               = coproduct ≫ (coproduct ⊗ (𝟙 M)) . obviously)
(left_counit'  : (left_unitor M).inv = coproduct ≫ (counit ⊗ (𝟙 M)) . obviously)
(right_counit' : (right_unitor M).inv = coproduct ≫ ((𝟙 M) ⊗ counit) . obviously)

restate_axiom comonoid_object.copentagon'
attribute [search] comonoid_object.copentagon
restate_axiom comonoid_object.left_counit'
attribute [search] comonoid_object.left_counit
restate_axiom comonoid_object.right_counit'
attribute [search] comonoid_object.right_counit

class comonoid_morphism
    {C : Type u} [monoidal_category.{u v} C] 
    {M M' : C} [comonoid_object.{u v} M] [comonoid_object.{u v} M']
    (f : M ⟶ M') :=
(square'   : comonoid_object.coproduct M ≫ (f ⊗ f) = f ≫ comonoid_object.coproduct M' . obviously)
(triangle' : f ≫ comonoid_object.counit M' = comonoid_object.counit M . obviously)

restate_axiom comonoid_morphism.square'
attribute [search] comonoid_morphism.square
restate_axiom comonoid_morphism.triangle'
attribute [search] comonoid_morphism.triangle

class is_cocommutative {C : Type u} (M : C) [symmetric_monoidal_category.{u v} C] [comonoid_object M] :=
(symmetry' : comonoid_object.coproduct M ≫ (braided_monoidal_category.braiding M M).hom = comonoid_object.coproduct M)

restate_axiom is_cocommutative.symmetry'
attribute [search] is_cocommutative.symmetry'

end

section
open braided_monoidal_category

class bimonoid_object
    {C : Type u} (M : C) [braided_monoidal_category.{u v} C]
    extends monoid_object.{u v} M, comonoid_object.{u v} M :=
(product_coproduct' : product ≫ coproduct
                    = (coproduct ⊗ coproduct) ≫
                      (associator M M (M ⊗ M)).hom ≫ ((𝟙 M) ⊗ (associator M M M).inv) ≫
                      ((𝟙 M) ⊗ (braiding M M).hom ⊗ (𝟙 M)) ≫
                      ((𝟙 M) ⊗ (associator M M M).hom) ≫ (associator M M (M ⊗ M)).inv ≫
                      (product ⊗ product))
(product_counit'    : product ≫ counit = (counit ⊗ counit) ≫ (left_unitor (tensor_unit C)).hom)
(unit_coproduct'    : unit ≫ coproduct = (left_unitor (tensor_unit C)).inv ≫ unit ⊗ unit)
(unit_counit'       : unit ≫ counit = 𝟙 (tensor_unit C))

restate_axiom bimonoid_object.product_coproduct'
attribute [search] bimonoid_object.product_coproduct'
restate_axiom bimonoid_object.product_counit'
attribute [search] bimonoid_object.product_counit'
restate_axiom bimonoid_object.unit_coproduct'
attribute [search] bimonoid_object.unit_coproduct
restate_axiom bimonoid_object.unit_counit'
attribute [search] bimonoid_object.unit_counit

class hopf_monoid_object
    {C : Type u} (M : C) [braided_monoidal_category.{u v} C]
    extends bimonoid_object.{u v} M :=
(antipode           : M ⟶ M)
(antipode_property' : counit ≫ unit = coproduct ≫ ((𝟙 M) ⊗ antipode) ≫ product)

restate_axiom hopf_monoid_object.antipode_property'
attribute [search] hopf_monoid_object.antipode_property

end

class frobenius_object
    {C : Type u} (M : C) [monoidal_category.{u v} C] extends monoid_object.{u v} M, comonoid_object.{u v} M :=
(left_frobenius'  : (coproduct ⊗ (𝟙 M)) ≫ (associator M M M).hom ≫ ((𝟙 M) ⊗ product)
                  = (product ≫ coproduct) . obviously)
(right_frobenius' : ((𝟙 M) ⊗ coproduct) ≫ (associator M M M).inv ≫ (product ⊗ (𝟙 M))
                  = (product ≫ coproduct) . obviously)

restate_axiom frobenius_object.left_frobenius'
attribute [search] frobenius_object.left_frobenius
restate_axiom frobenius_object.right_frobenius'
attribute [search] frobenius_object.right_frobenius

class is_commutative_frobenius
    {C : Type u} (M : C) [symmetric_monoidal_category.{u v} C]
    [frobenius_object.{u v} M] :=
(commutative   : is_commutative M)
(cocommutative : is_cocommutative M)

class is_symmetric_frobenius
    {C : Type u} (M : C) [symmetric_monoidal_category.{u v} C]
    [frobenius_object.{u v} M] :=
(symmetry' : (braided_monoidal_category.braiding M M).hom ≫
             monoid_object.product M ≫ comonoid_object.counit M
           = monoid_object.product M ≫ comonoid_object.counit M
           . obviously)

restate_axiom is_symmetric_frobenius.symmetry'
attribute [search] is_symmetric_frobenius.symmetry

class is_special
    {C : Type u} (M : C) [monoidal_category.{u v} C] [frobenius_object.{u v} M] :=
(special' : comonoid_object.coproduct M ≫ monoid_object.product M = (𝟙 M))

restate_axiom is_special.special'
attribute [search] is_special.special

class is_extra
    {C : Type u} (M : C) [monoidal_category.{u v} C] [frobenius_object.{u v} M] :=
(extra' : monoid_object.unit M ≫ comonoid_object.counit M = 𝟙 (tensor_unit C))

restate_axiom is_extra.extra'
attribute [search] is_extra.extra

structure special_commutative_frobenius_object
    {C : Type u} (M : C) [symmetric_monoidal_category.{u v} C] extends frobenius_object.{u v} M :=
(special     : is_special M)
(commutative : is_commutative_frobenius M)

end category_theory.monoidal
