/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.products.basic

open category_theory

namespace category_theory.bifunctor

universes v₁ v₂ v₃ u₁ u₂ u₃
variables {C : Type u₁} {D : Type u₂} {E : Type u₃}
variables [𝒞 : category.{v₁} C] [𝒟 : category.{v₂} D] [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

@[simp] lemma map_id (F : (C × D) ⥤ E) (X : C) (Y : D) :
  F.map ((𝟙 X, 𝟙 Y) : (X, Y) ⟶ (X, Y)) = 𝟙 (F.obj (X, Y)) :=
F.map_id (X, Y)

-- @[simp]
lemma map_id_comp (F : (C × D) ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((𝟙 W, f ≫ g) : (W, X) ⟶ (W, Z)) =
  F.map ((𝟙 W, f) : (W, X) ⟶ (W, Y)) ≫ F.map ((𝟙 W, g) : (W, Y) ⟶ (W, Z)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

-- @[simp]
lemma map_comp_id (F : (C × D) ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((f ≫ g, 𝟙 W) : (X, W) ⟶ (Z, W)) =
  F.map ((f, 𝟙 W) : (X, W) ⟶ (Y, W)) ≫ F.map ((g, 𝟙 W) : (Y, W) ⟶ (Z, W)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

@[simp, reassoc]
lemma map_id_comp' (F : (C × D) ⥤ E) (W : C) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((𝟙 W, f) : (W, X) ⟶ (W, Y)) ≫ F.map ((𝟙 W, g) : (W, Y) ⟶ (W, Z)) =
  F.map ((𝟙 W, f ≫ g) : (W, X) ⟶ (W, Z)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

@[simp, reassoc]
lemma map_comp_id' (F : (C × D) ⥤ E) (X Y Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map ((f, 𝟙 W) : (X, W) ⟶ (Y, W)) ≫ F.map ((g, 𝟙 W) : (Y, W) ⟶ (Z, W)) =
  F.map ((f ≫ g, 𝟙 W) : (X, W) ⟶ (Z, W)) :=
by rw [←functor.map_comp,prod_comp,category.comp_id]

@[simp] lemma diagonal (F : (C × D) ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
  F.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ F.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) =
  F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
by rw [←functor.map_comp, prod_comp, category.id_comp, category.comp_id]

@[simp] lemma diagonal' (F : (C × D) ⥤ E) (X X' : C) (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') :
  F.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ F.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
  F.map ((f, g) : (X, Y) ⟶ (X', Y')) :=
by rw [←functor.map_comp, prod_comp, category.id_comp, category.comp_id]

def left (F : (C × D) ⥤ E) (d : D) : C ⥤ E :=
{ obj := λ c : C, F.obj (c,d),
  map := λ X Y f, F.map (f,𝟙 _) }

@[simp]
lemma left_obj  (F : (C × D) ⥤ E) (c : C) (d : D) : (left F d).obj c = F.obj (c, d) := rfl

@[simp]
lemma left_map  (F : (C × D) ⥤ E) (c₀ c₁ : C) (d : D) (f : c₀ ⟶ c₁) : (left F d).map f = F.map (f, 𝟙 d) := rfl

def right (F : (C × D) ⥤ E) (c : C) : D ⥤ E :=
{ obj := λ d : D, F.obj (c,d),
  map := λ X Y f, F.map (𝟙 _,f) }

@[simp]
lemma right_obj  (F : (C × D) ⥤ E) (c : C) (d : D) : (right F c).obj d = F.obj (c, d) := rfl

@[simp]
lemma right_map  (F : (C × D) ⥤ E) (c : C) (d₀ d₁ : D) (f : d₀ ⟶ d₁) : (right F c).map f = F.map (𝟙 c, f) := rfl

end category_theory.bifunctor
