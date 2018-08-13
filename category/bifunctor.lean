/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Functors with two arguments
-/

import data.sum
       category.basic category.functor
       tactic.basic

universes u₀ u₁ u₂ v₀ v₁ v₂

class bifunctor (F : Type u₀ → Type u₁ → Type u₂) :=
(bimap : Π {α α' β β'}, (α → α') → (β → β') → F α β → F α' β')
export bifunctor ( bimap )

class is_lawful_bifunctor (F : Type u₀ → Type u₁ → Type u₂) [bifunctor F] :=
(id_bimap : Π {α β} (x : F α β), bimap id id x = x)
(comp_bimap : Π {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ → α₁) (f' : α₁ → α₂)
  (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
  bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x)
  -- `comp_bimap` constrasts with `comp_map` from lawful functors but
  -- this form is more easily usable in a set of rewrite rules.
export is_lawful_bifunctor (id_bimap comp_bimap)

attribute [higher_order bimap_id_id] id_bimap
attribute [higher_order bimap_comp_bimap] comp_bimap

export is_lawful_bifunctor (bimap_id_id bimap_comp_bimap)
variables {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F]

namespace bifunctor

@[reducible]
def first {α α' β} (f : α → α') : F α β → F α' β :=
bimap f id

@[reducible]
def second {α β β'} (f : β → β') : F α β → F α β' :=
bimap id f

variable [is_lawful_bifunctor F]

@[higher_order first_id]
lemma id_first : Π {α β} (x : F α β), first id x = x :=
@id_bimap _ _ _

@[higher_order second_id]
lemma id_second : Π {α β} (x : F α β), second id x = x :=
@id_bimap _ _ _

@[higher_order first_comp_first]
lemma comp_first {α₀ α₁ α₂ β}
  (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) :
  first f' (first f x) = first (f' ∘ f)  x :=
by simp [first,comp_bimap]

@[higher_order first_comp_second]
lemma first_second {α₀ α₁ β₀ β₁}
  (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
  first f (second f' x) = bimap f f' x :=
by simp [first,comp_bimap]

@[higher_order second_comp_first]
lemma second_first {α₀ α₁ β₀ β₁}
  (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) :
  second f' (first f x) = bimap f f' x :=
by simp [second,comp_bimap]

@[higher_order second_comp_second]
lemma comp_second {α β₀ β₁ β₂}
  (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) :
  second g' (second g x) = second (g' ∘ g) x :=
by simp [second,comp_bimap]

attribute [functor_norm] comp_bimap comp_second comp_first
  second_comp_second second_comp_first first_comp_second first_comp_first bimap_comp_bimap
  bimap_id_id first_id second_id

def bicompl (F : Type* → Type* → Type*) (G : Type* → Type*) (H : Type* → Type*) (α β) :=
F (G α) (H β)

def bicompr (F : Type* → Type*) (G : Type* → Type* → Type*) (α β) :=
F (G α β)

end bifunctor
open functor
instance : bifunctor prod :=
{ bimap := @prod.map }

instance : is_lawful_bifunctor prod :=
by refine { .. }; intros; cases x; refl

instance bifunctor.const : bifunctor const :=
{ bimap := (λ α α' β β f _, f) }

instance is_lawful_bifunctor.const : is_lawful_bifunctor const  :=
by refine { .. }; intros; refl

instance bifunctor.flip : bifunctor (flip F) :=
{ bimap := (λ α α' β β' f f' x, (bimap f' f x : F β' α')) }

instance is_lawful_bifunctor.flip [is_lawful_bifunctor F] : is_lawful_bifunctor (flip F)  :=
by refine { .. }; intros; simp [bimap] with functor_norm

instance : bifunctor sum :=
{ bimap := @sum.map }

instance : is_lawful_bifunctor sum :=
by refine { .. }; intros; cases x; refl

open bifunctor functor

@[priority 0]
instance bifunctor.functor {α} : functor (F α) :=
{ map := λ _ _, second }

@[priority 0]
instance bifunctor.is_lawful_functor [is_lawful_bifunctor F] {α} : is_lawful_functor (F α) :=
by refine {..}; intros; simp [functor.map] with functor_norm

section bicompl

variables (G : Type* → Type u₀) (H : Type* → Type u₁) [functor G] [functor H]

instance : bifunctor (bicompl F G H) :=
{ bimap := λ α α' β β' f f' x, (bimap (map f) (map f') x : F (G α') (H β')) }

instance [is_lawful_functor G]  [is_lawful_functor H] [is_lawful_bifunctor F] :
  is_lawful_bifunctor (bicompl F G H) :=
by constructor; intros; simp [bimap,map_id,map_comp_map] with functor_norm

end bicompl
section bicompr

variables (G : Type u₂ → Type*) [functor G]

instance : bifunctor (bicompr G F) :=
{ bimap := λ α α' β β' f f' x, (map (bimap f f') x : G (F α' β')) }

instance [is_lawful_functor G] [is_lawful_bifunctor F] :
  is_lawful_bifunctor (bicompr G F) :=
by constructor; intros; simp [bimap] with functor_norm

end bicompr
