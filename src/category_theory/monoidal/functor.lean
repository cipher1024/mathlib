/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import category_theory.monoidal.category

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

section

open monoidal_category

variables {C : Type u₁} [category.{v₁} C] [𝒞 : monoidal_category.{v₁} C]
          {D : Type u₂} [category.{v₂} D] [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟

/-- A lax monoidal functor is a functor `F : C ⥤ D` between monoidal categories, equipped with morphisms
    `ε : 𝟙 _D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`, satisfying the
    the appropriate coherences. -/
class lax_monoidal_functor (F : C ⥤ D) :=
-- unit morphism
(ε               : 𝟙_ D ⟶ F.obj (𝟙_ C))
-- tensorator
(μ                : Π X Y : C, (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y))
(μ_natural'       : ∀ {X Y X' Y' : C}
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  ((F.map f) ⊗ (F.map g)) ≫ μ Y Y' = μ X X' ≫ F.map (f ⊗ g)
  . obviously)
-- associativity of the tensorator
(associativity'   : ∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙 (F.obj Z)) ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom
  = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (λ_ (F.obj X)).hom
  = (ε ⊗ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (ρ_ (F.obj X)).hom
  = (𝟙 (F.obj X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom
  . obviously)

restate_axiom lax_monoidal_functor.μ_natural'
attribute [simp] lax_monoidal_functor.μ_natural
restate_axiom lax_monoidal_functor.left_unitality'
attribute [simp] lax_monoidal_functor.left_unitality
restate_axiom lax_monoidal_functor.right_unitality'
attribute [simp] lax_monoidal_functor.right_unitality
restate_axiom lax_monoidal_functor.associativity'
attribute [simp] lax_monoidal_functor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality
-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

/-- A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms. -/
class monoidal_functor (F : C ⥤ D)
extends lax_monoidal_functor.{v₁ v₂} F :=
(ε_is_iso            : is_iso ε . obviously)
(μ_is_iso            : Π X Y : C, is_iso (μ X Y) . obviously)

attribute [instance] monoidal_functor.ε_is_iso monoidal_functor.μ_is_iso

variables {C D}
open lax_monoidal_functor monoidal_functor

def monoidal_functor.ε_iso (F : C ⥤ D) [monoidal_functor.{v₁ v₂} F] :
  tensor_unit D ≅ F.obj (tensor_unit C) :=
as_iso (ε F)

def monoidal_functor.μ_iso (F : C ⥤ D) [monoidal_functor.{v₁ v₂} F] (X Y : C) :
  (F.obj X) ⊗ (F.obj Y) ≅ F.obj (X ⊗ Y) :=
as_iso (μ F X Y)

end

open monoidal_category

namespace monoidal_functor
open lax_monoidal_functor

section
variables {C : Type u₁} [category.{v₁} C] [𝒞 : monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟

/-- The tensorator as a natural isomorphism. -/
def μ_nat_iso (F : C ⥤ D) [monoidal_functor.{v₁ v₂} F] :
  (functor.prod F F) ⋙ (tensor D) ≅ (tensor C) ⋙ F :=
nat_iso.of_components
  (by { intros, apply μ_iso F })
  (by { intros, apply μ_natural F })
end

section
variables (C : Type u₁) [category.{v₁} C] [𝒞 : monoidal_category.{v₁} C]
include 𝒞

/-- The identity monoidal functor. -/
instance id : monoidal_functor.{v₁ v₁} (functor.id C) :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _ }

-- @[simp] lemma id_obj (X : C) : (monoidal_functor.id C).obj X = X := rfl
-- @[simp] lemma id_map {X X' : C} (f : X ⟶ X') : (monoidal_functor.id C).map f = f := rfl
@[simp] lemma id_ε : (monoidal_functor.id C).ε = 𝟙 _ := rfl
@[simp] lemma id_μ (X Y) : μ (𝟭 C) X Y = 𝟙 _ := rfl

end

end monoidal_functor

variables {C : Type u₁} [category.{v₁} C] [𝒞 : monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D] [𝒟 : monoidal_category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E] [ℰ : monoidal_category.{v₃} E]

include 𝒞 𝒟 ℰ

namespace lax_monoidal_functor
variables (F : C ⥤ D) [lax_monoidal_functor.{v₁ v₂} F]
          (G : D ⥤ E) [lax_monoidal_functor.{v₂ v₃} G]

-- The proofs here are horrendous; rewrite_search helps a lot.
/-- The composition of two lax monoidal functors is again lax monoidal. -/
instance comp : lax_monoidal_functor.{v₁ v₃} (F ⋙ G) :=
{ ε                := ε G ≫ (G.map (ε _)),
  μ                := λ X Y : C, (μ G (F.obj X) (F.obj Y) ≫ G.map (μ F X Y) : G.obj (F.obj _) ⊗ _ ⟶ G.obj (F.obj _)),
  μ_natural'       := λ _ _ _ _ f g,
  begin
    simp only [functor.comp_map, assoc],
    rw [←category.assoc, lax_monoidal_functor.μ_natural, category.assoc, ←map_comp, ←map_comp,
        ←lax_monoidal_functor.μ_natural]
  end,
  associativity'   := λ X Y Z,
  begin
    dsimp,
    rw id_tensor_comp,
    slice_rhs 3 4 { rw [← G.map_id, μ_natural], },
    slice_rhs 1 3 { rw ←associativity, },
    rw comp_tensor_id,
    slice_lhs 2 3 { rw [← map_id, μ_natural], },
    rw [category.assoc, category.assoc, category.assoc, category.assoc, category.assoc,
        ←G.map_comp, ←G.map_comp, ←G.map_comp, ←G.map_comp,
        associativity],
  end,
  left_unitality'  := λ X,
  begin
    dsimp,
    rw [left_unitality G, comp_tensor_id, category.assoc, category.assoc],
    apply congr_arg,
    rw [left_unitality F, map_comp, ←nat_trans.id_app, ←category.assoc,
        ←lax_monoidal_functor.μ_natural, nat_trans.id_app, map_id, ←category.assoc, map_comp],
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    rw [right_unitality G, id_tensor_comp, category.assoc, category.assoc],
    apply congr_arg,
    rw [right_unitality F, map_comp, ←nat_trans.id_app, ←category.assoc,
        ←lax_monoidal_functor.μ_natural, nat_trans.id_app, map_id, ←category.assoc, map_comp],
  end
 }.

@[simp] lemma comp_obj (X : C) : (F.comp G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma comp_map {X X' : C} (f : X ⟶ X') :
  (F.comp G).map f = (G.map (F.map f) : G.obj (F.obj X) ⟶ G.obj (F.obj X')) := rfl
@[simp] lemma comp_ε : ε (F.comp G) = ε G ≫ (G.map $ ε F) := rfl
@[simp] lemma comp_μ (X Y : C) : μ (F ⋙ G) X Y =
                                 (μ G (F.obj X) (F.obj Y) : _) ≫ G.map (μ F X Y) := rfl

end lax_monoidal_functor

namespace monoidal_functor

variables (F : C ⥤ D) [monoidal_functor.{v₁ v₂} F] (G : D ⥤ E) [monoidal_functor.{v₂ v₃} G]

/-- The composition of two monoidal functors is again monoidal. -/
def comp : monoidal_functor.{v₁ v₃} (F ⋙ G) :=
{ ε_is_iso := by { dsimp, apply_instance },
  μ_is_iso := by { dsimp, apply_instance },
  .. lax_monoidal_functor.comp F G }.

end monoidal_functor

end category_theory
