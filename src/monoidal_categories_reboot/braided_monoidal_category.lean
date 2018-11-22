import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .monoidal_category
open category_theory
open tactic

universes u v

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal

class braided_monoidal_category (C : Type u) extends monoidal_category.{u v} C :=
-- braiding natural iso:
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
-- hexagon identities:
(hexagon_forward'     : Π X Y Z : C,
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (associator Y X Z).hom ≫ (𝟙 Y) ⊗ (braiding X Z).hom
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (associator X Z Y).inv ≫ (braiding X Z).hom ⊗ (𝟙 Y)
  . obviously)


restate_axiom braided_monoidal_category.braiding_naturality'
attribute [simp,search] braided_monoidal_category.braiding_naturality
restate_axiom braided_monoidal_category.hexagon_forward'
attribute [simp,search] braided_monoidal_category.hexagon_forward
restate_axiom braided_monoidal_category.hexagon_reverse'
attribute [simp,search] braided_monoidal_category.hexagon_reverse

section

variables (C : Type u) [𝒞 : braided_monoidal_category.{u v} C]
include 𝒞

@[reducible] def braided_monoidal_category.braiding_functor : (C × C) ⥤ C :=
{ obj := λ X, X.2 ⊗ X.1,
  map := λ {X Y : C × C} (f : X ⟶ Y), f.2 ⊗ f.1 }
@[reducible] def braided_monoidal_category.non_braiding_functor : (C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), f.1 ⊗ f.2 }

open monoidal_category
open braided_monoidal_category

@[simp,search] def braiding_of_product (X Y Z : C) :
  (braiding (X ⊗ Y) Z).hom =
  (associator X Y Z).hom ≫ ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (associator X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y)) ≫ (associator Z X Y).hom :=
begin
  obviously,
end

def braided_monoidal_category.braiding_nat_iso : braiding_functor C ≅ non_braiding_functor C :=
nat_iso.of_components
  (by intros; simp; apply braiding)
  (by intros; simp; apply braiding_naturality)

end

class symmetric_monoidal_category (C : Type u) extends braided_monoidal_category C :=
-- braiding symmetric:
(symmetry' : ∀ X Y : C, (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y) . obviously)

restate_axiom symmetric_monoidal_category.symmetry'
attribute [simp,search] symmetric_monoidal_category.symmetry

end category_theory.monoidal
