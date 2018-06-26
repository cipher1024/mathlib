/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Transferring `traversable` instances using isomorphisms.
-/
import data.equiv data.traversable.basic

universes u

namespace equiv

section functor
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [functor t]

open functor

protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
eqv β $ map f ((eqv α).symm x)

protected def functor : functor t' :=
{ map := @equiv.map _ }

variables [is_lawful_functor t]

protected lemma id_map {α : Type u} (x : t' α) :
  equiv.map id x = x :=
by simp [equiv.map,id_map]

protected lemma comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
  equiv.map (h ∘ g) x = equiv.map h (equiv.map g x) :=
by dsimp [equiv.map]; simp; apply comp_map

protected def is_lawful_functor : @is_lawful_functor _ equiv.functor :=
{ id_map := @equiv.id_map _ _,
  comp_map := @equiv.comp_map _ _ }

end functor

section traversable
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [traversable t]
variables {m : Type u → Type u} [applicative m]
variables {α β : Type u}

protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
eqv β <$> traverse f ((eqv α).symm x)

protected def traversable : traversable t' :=
{ to_functor := equiv.functor eqv,
  traverse := @equiv.traverse _ }

end traversable

section equiv
parameters {t t' : Type u → Type u}
parameters (eqv : Π α, t α ≃ t' α)
variables [traversable t]
variables [is_lawful_traversable t]
variables {G H : Type u → Type u}
          [applicative G] [applicative H]
          [is_lawful_applicative G]
          [is_lawful_applicative H]
variables (eta : applicative_morphism G H)
variables {α β γ : Type u}

open is_lawful_traversable

protected lemma id_traverse (x : t' α) :
  equiv.traverse eqv identity.mk x = x :=
by simp! [equiv.traverse,id_traverse,functor.map] with norm

protected lemma map_traverse (g : α → G β) (f : β → γ) (x : t' α) :
  equiv.map eqv f <$> equiv.traverse eqv g x = equiv.traverse eqv (functor.map f ∘ g) x :=
by simp [equiv.traverse] with norm; rw ← map_traverse; simp [equiv.map] with norm;
   congr' 1; ext; simp [equiv.map]

protected lemma traverse_comp (g : α → G β) (h : β → H γ) (x : t' α) :
  equiv.traverse eqv (compose.mk ∘ functor.map h ∘ g) x =
  ⟨ equiv.traverse eqv h <$> equiv.traverse eqv g x ⟩ :=
by simp [equiv.traverse,traverse_comp] with norm; congr; ext; simp

protected lemma morphism  (f : α → G β) (x : t' α) :
  eta (equiv.traverse eqv f x) = equiv.traverse eqv (@eta _ ∘ f) x :=
by simp [equiv.traverse] with norm

protected def is_lawful_traversable :
  @is_lawful_traversable t' (equiv.traversable eqv) :=
{ to_is_lawful_functor := @equiv.is_lawful_functor _ _ eqv _ _,
  map_traverse := @equiv.map_traverse _ _,
  id_traverse := @equiv.id_traverse _ _,
  traverse_comp := @equiv.traverse_comp _ _,
  morphism := @equiv.morphism _ _ }

end equiv
end equiv
