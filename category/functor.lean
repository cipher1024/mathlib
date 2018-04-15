/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Standard identity and composition functors
-/

import category.basic

universe variables u v w u' v' w'

section functor

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F] [is_lawful_functor F]

lemma functor.id_map' : functor.map id = (id : F α → F α) :=
by { apply funext, apply id_map }

lemma functor.comp_map' (f : α → β) (g : β → γ) :
  functor.map (g ∘ f) = (functor.map g ∘ functor.map f : F α → F γ) :=
by { apply funext, intro, apply comp_map }

@[norm]
lemma functor.map_map (f : α → β) (g : β → γ) (x : F α) :
  g <$> f <$> x = (g ∘ f) <$> x :=
by rw ← comp_map

end functor

structure identity (α : Type u) : Type u :=
  (run_identity : α)

structure compose (f : Type u → Type u') (g : Type v → Type u) (α : Type v) : Type u' :=
  (run : f $ g α)

namespace identity

open function

variables {α : Type u} {β : Type v} {γ : Type u'}

def map (f : α → β) : identity α → identity β
  | ⟨ x ⟩ := ⟨ f x ⟩

local infixr <$> := map

lemma id_map : ∀ (x : identity α), map id x = x
 | ⟨ x ⟩ := rfl

lemma comp_map (f : α → β) (g : β → γ) :
  ∀ (x : identity α), map (g ∘ f) x = g <$> f <$> x
 | ⟨ x ⟩ := rfl

end identity

instance identity_functor : functor identity :=
{ map := @identity.map }
instance identity_lawful_functor : is_lawful_functor identity :=
{ id_map := @identity.id_map,
  comp_map := @identity.comp_map }

namespace compose

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [functor f] [functor g]

def map {α β : Type v} (h : α → β) : compose f g α → compose f g β
  | ⟨ x ⟩ := ⟨ functor.map h <$> x ⟩

variables [is_lawful_functor f] [is_lawful_functor g]
variables {α β γ : Type v}

local infix ` <$> ` := map

lemma id_map : ∀ (x : compose f g α), map id x = x
  | ⟨ x ⟩ :=
by simp [map,functor.id_map']

protected lemma comp_map (g_1 : α → β) (h : β → γ) : ∀ (x : compose f g α),
           map (h ∘ g_1) x = map h (map g_1 x)
  | ⟨ x ⟩ :=
by simp [map,functor.comp_map' g_1 h] with norm

end compose

instance functor_compose {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g] :
  functor (compose f g) :=
{ map := @compose.map f g _ _ }

instance lawful_functor_compose {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g]
  [is_lawful_functor f] [is_lawful_functor g] :
  is_lawful_functor (compose f g) :=
{ id_map := @compose.id_map f g _ _ _ _,
  comp_map := @compose.comp_map f g _ _ _ _ }

@[norm]
lemma compose.map_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α)) :
  h <$> compose.mk x = compose.mk (functor.map h <$> x) := rfl

namespace ulift

instance : functor ulift :=
{ map := λ α β f, up ∘ f ∘ down }

end ulift
