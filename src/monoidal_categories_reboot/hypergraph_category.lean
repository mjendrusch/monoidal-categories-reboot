-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import .monoidal_category
import .braided_monoidal_category
import .monoid_object

universes u v

namespace category_theory.hypergraph
open category_theory.monoidal
open category_theory.monoidal.monoidal_category
open category_theory.monoidal.braided_monoidal_category

@[reducible]
def reassociate_and_braid_product {C : Type u} (X Y : C) [symmetric_monoidal_category.{v} C] :=
(associator X Y (X ⊗ Y)).hom ≫ ((𝟙 X) ⊗ (associator Y X Y).inv) ≫
((𝟙 X) ⊗ (braiding Y X).hom ⊗ (𝟙 Y)) ≫ (associator X (X ⊗ Y) Y).inv ≫
((associator X X Y).inv ⊗ (𝟙 Y)) ≫ (associator (X ⊗ X) Y Y).hom

@[reducible]
def reassociate_and_braid_coproduct {C : Type u} (X Y : C) [symmetric_monoidal_category.{v} C] :=
(associator X X (Y ⊗ Y)).hom ≫ ((𝟙 X) ⊗ (associator X Y Y).inv) ≫
((𝟙 X) ⊗ (braiding X Y).hom ⊗ (𝟙 Y)) ≫
((𝟙 X) ⊗ (associator Y X Y).hom) ≫ (associator X Y (X ⊗ Y)).inv

class hypergraph_category (C : Type u) extends symmetric_monoidal_category.{v} C :=
-- each object is equipped with the structure of a special commutative Frobenius monoid:
(frobenius_structure : Π X : C, special_commutative_frobenius_object X)
-- the Frobenius structure and the tensor product interact in the obvious way:
(product_tensor'     : Π X Y : C,
                       reassociate_and_braid_product X Y ≫
                       ((frobenius_structure X).product ⊗ (frobenius_structure Y).product)
                     = (frobenius_structure (X ⊗ Y)).product
                     . obviously)
(coproduct_tensor'   : Π X Y : C,
                       ((frobenius_structure X).coproduct ⊗ (frobenius_structure Y).coproduct) ≫
                       reassociate_and_braid_coproduct X Y
                     = (frobenius_structure (X ⊗ Y)).coproduct
                     . obviously)
(unit_tensor'        : Π X Y : C,
                               (left_unitor tensor_unit).inv ≫
                               ((frobenius_structure X).unit ⊗ (frobenius_structure Y).unit)
                             = (frobenius_structure (X ⊗ Y)).unit
                             . obviously)
(counit_tensor'      : Π X Y : C,
                               ((frobenius_structure X).counit ⊗ (frobenius_structure Y).counit) ≫
                               (left_unitor tensor_unit).hom
                             = (frobenius_structure (X ⊗ Y)).counit
                             . obviously)

restate_axiom hypergraph_category.product_tensor'
attribute [search] hypergraph_category.product_tensor
restate_axiom hypergraph_category.coproduct_tensor'
attribute [search] hypergraph_category.coproduct_tensor
restate_axiom hypergraph_category.unit_tensor'
attribute [search] hypergraph_category.unit_tensor
restate_axiom hypergraph_category.counit_tensor'
attribute [search] hypergraph_category.counit_tensor

end category_theory.hypergraph
