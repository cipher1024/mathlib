/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections

This is a work-in-progress
-/

import .basic
import category.basic
import category.applicative

universe variables w u v w' u' v'

open function

section identity

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

def identity.traverse {α β : Type u} (g : α → f β) : identity α → f (identity β)
 | ⟨ x ⟩ := (λ x : β, ⟨ x ⟩) <$> g x


instance : has_traverse identity :=
⟨ @identity.traverse ⟩

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma identity.traverse_mk (g : α → f β) (x : α) :
  identity.traverse g ⟨ x ⟩ = identity.mk <$> (g x) :=
rfl

lemma identity.traverse_mk' (g : α → f β) :
  identity.traverse g ∘ identity.mk = map identity.mk ∘ g :=
rfl

lemma identity.id_traverse (x : identity α) :
  identity.traverse identity.mk x = identity.mk x :=
by { cases x, unfold identity.traverse, refl }

lemma identity.traverse_comp (g : α → f β) (h : β → f' γ) :
  ∀ (x : identity α),
        identity.traverse (compose.mk ∘ map h ∘ g) x =
        compose.mk (identity.traverse h <$> identity.traverse g x)
  | ⟨ x ⟩ :=
by simp! with norm; refl

lemma identity.map_traverse
   (g : α → f' β) (f : β → γ)
   (x : identity α) :
  map f <$> identity.traverse g x = identity.traverse (map f ∘ g) x :=
by cases x with x; simp! with norm; refl

variable (eta : applicative_morphism f f')

lemma identity.morphism {α β : Type u}
  (F : α → f β) (x : identity α) :
  eta (identity.traverse F x) = identity.traverse (@eta _ ∘ F) x :=
by cases x with x; simp! with norm

end identity

instance : traversable identity :=
{ to_functor := (identity_functor : functor identity),
  traverse := @identity.traverse,
  id_traverse := λ α x, @identity.id_traverse α x,
  traverse_comp := @identity.traverse_comp,
  map_traverse := @identity.map_traverse,
  morphism := @identity.morphism }

section option

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

def option.traverse {α β : Type u} (g : α → f β) : option α → f (option β)
 | none := pure none
 | (some x) := some <$> g x

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma option.traverse_mk (g : α → f β) (x : α) :
  option.traverse g (some x) = some <$> (g x) :=
rfl

lemma option.traverse_mk' (g : α → f β) :
  option.traverse g ∘ some = map some ∘ g :=
rfl

lemma option.id_traverse (x : option α) :
  option.traverse identity.mk x = ⟨ x ⟩ :=
by { cases x ; unfold option.traverse ; refl }

lemma option.traverse_comp (g : α → f β) (h : β → f' γ) :
  ∀ (x : option α),
        option.traverse (compose.mk ∘ map h ∘ g) x =
        compose.mk (option.traverse h <$> option.traverse g x) :=
by intro x ; cases x ; simp! with norm ; refl

lemma option.map_traverse (g : α -> f' β) (f : β → γ)
  (x : option α) :
  map f <$> option.traverse g x = option.traverse (map f ∘ g) x :=
by cases x ; simp! with norm ; refl

variable (eta : applicative_morphism f f')

lemma option.morphism {α β : Type u} (g : α → f β) (x : option α) :
  eta (option.traverse g x) = option.traverse (@eta _ ∘ g) x :=
by cases x with x ; simp! [*] with norm

end option

instance : traversable option :=
{ to_functor := _,
  traverse := @option.traverse,
  id_traverse := @option.id_traverse,
  traverse_comp := @option.traverse_comp,
  map_traverse := @option.map_traverse,
  morphism := @option.morphism }

section list

variables {f : Type u → Type v}
variables [applicative f]
variables {α β : Type u}

open applicative functor
open list (cons)

def list.traverse (g : α → f β) : list α → f (list β)
 | [] := pure []
 | (x :: xs) := cons <$> g x <*> list.traverse xs

end list

section list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

open applicative functor
open list (cons)

lemma list.id_traverse (xs : list α) :
  list.traverse identity.mk xs = ⟨ xs ⟩ :=
by induction xs ; simp! [*] with norm ; refl

lemma list.traverse_comp (g : α → f β) (h : β → f' γ) (x : list α) :
  list.traverse (compose.mk ∘ map h ∘ g) x =
  compose.mk (list.traverse h <$> list.traverse g x) :=
by induction x ; simp! [*] with norm ; refl

lemma list.map_traverse {α β γ : Type u} (g : α → f' β) (f : β → γ)
  (x : list α) :
  map f <$> list.traverse g x = list.traverse (map f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih ;
  simp! [*] with norm ; refl
end

variable (eta : applicative_morphism f f')

lemma list.morphism {α β : Type u} (g : α → f β) (x : list α) :
  eta (list.traverse g x) = list.traverse (@eta _ ∘ g) x :=
by induction x ; simp! [*] with norm

end list

instance : has_traverse list :=
{ traverse := @list.traverse }

instance : traversable list :=
{ to_functor := _,
  traverse := @list.traverse,
  id_traverse := @list.id_traverse,
  traverse_comp := @list.traverse_comp,
  map_traverse := @list.map_traverse,
  morphism := @list.morphism }
