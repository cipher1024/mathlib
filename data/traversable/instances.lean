/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections
-/

import .basic
import category.basic
import category.functor
import category.applicative

universe variables w u v w' u' v'

open function

section identity

open function functor

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

def identity.traverse {α β : Type u} (g : α → f β) : id α → f (id β) := g

instance : traversable id :=
⟨ @identity.traverse ⟩

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma identity.id_traverse (x : id α) :
  identity.traverse identity.mk x = identity.mk x :=
by refl
lemma identity.traverse_comp (g : α → f β) (h : β → f' γ) (x : id α) :
  identity.traverse (compose.mk ∘ map h ∘ g) x =
  compose.mk (identity.traverse h <$> identity.traverse g x) :=
by simp! [identity.traverse,functor.id_map'] with norm

lemma identity.map_traverse
   (g : α → f' β) (f : β → γ)
   (x : id α) :
  map f <$> identity.traverse g x = identity.traverse (map f ∘ g) x :=
by simp [map,identity.traverse,id_map] with norm

variable (eta : applicative_morphism f f')

lemma identity.morphism {α β : Type u}
  (F : α → f β) (x : id α) :
  eta (identity.traverse F x) = identity.traverse (@eta _ ∘ F) x :=
by simp! [identity.traverse] with norm; refl

end identity

instance : is_lawful_traversable id :=
{ id_traverse := λ α x, @identity.id_traverse α x,
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

instance : traversable option :=
{ traverse := @option.traverse }

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β γ : Type u}

lemma option.id_traverse (x : option α) :
  option.traverse identity.mk x = x :=
by cases x; unfold option.traverse; refl

lemma option.traverse_comp (g : α → f β) (h : β → f' γ) :
  ∀ (x : option α),
        option.traverse (compose.mk ∘ map h ∘ g) x =
        compose.mk (option.traverse h <$> option.traverse g x) :=
by intro x; cases x; simp! with norm; refl

lemma option.map_traverse (g : α -> f' β) (f : β → γ)
  (x : option α) :
  map f <$> option.traverse g x = option.traverse (map f ∘ g) x :=
by cases x; simp! with norm; refl

variable (eta : applicative_morphism f f')

lemma option.morphism {α β : Type u} (g : α → f β) (x : option α) :
  eta (option.traverse g x) = option.traverse (@eta _ ∘ g) x :=
by cases x with x; simp! [*] with norm

end option

instance : is_lawful_traversable option :=
{ id_traverse := @option.id_traverse,
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
  list.traverse identity.mk xs = xs :=
by induction xs; simp! [*] with norm; refl

lemma list.traverse_comp (g : α → f β) (h : β → f' γ) (x : list α) :
  list.traverse (compose.mk ∘ map h ∘ g) x =
  compose.mk (list.traverse h <$> list.traverse g x) :=
by induction x; simp! [*] with norm; refl

lemma list.map_traverse {α β γ : Type u} (g : α → f' β) (f : β → γ)
  (x : list α) :
  map f <$> list.traverse g x = list.traverse (map f ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih;
  simp! [*] with norm; refl
end

variable (eta : applicative_morphism f f')

lemma list.morphism {α β : Type u} (g : α → f β) (x : list α) :
  eta (list.traverse g x) = list.traverse (@eta _ ∘ g) x :=
by induction x; simp! [*] with norm
open nat

end list

instance : traversable list :=
{ traverse := @list.traverse }

instance : is_lawful_traversable list :=
{ id_traverse := @list.id_traverse,
  traverse_comp := @list.traverse_comp,
  map_traverse := @list.map_traverse,
  morphism := @list.morphism }

namespace sum

section traverse
variables {γ : Type u}
variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']

open applicative functor
open list (cons)

protected def traverse {α β : Type u} (g : α → f β) : γ ⊕ α → f (γ ⊕ β)
| (sum.inl x) := pure (sum.inl x)
| (sum.inr x) := sum.inr <$> g x

variables [is_lawful_applicative f] [is_lawful_applicative f']
variables {α β η : Type u}

protected lemma id_traverse (x : γ ⊕ α) :
  sum.traverse identity.mk x = identity.mk x :=
by cases x; refl

protected lemma traverse_comp (g : α → f β) (h : β → f' η) (x : γ ⊕ α) :
        sum.traverse (compose.mk ∘ map h ∘ g) x =
        compose.mk (sum.traverse h <$> sum.traverse g x) :=
by casesm _ ⊕ _; simp! [sum.traverse,id_map'] with norm; refl

protected lemma map_traverse
   (g : α → f' β) (f : β → η)
   (x : γ ⊕ α) :
  map f <$> sum.traverse g x = sum.traverse (map f ∘ g) x :=
by casesm _ ⊕ _; simp [map,sum.map,sum.traverse,id_map] with norm; congr

variable (eta : applicative_morphism f f')

protected lemma morphism {α β : Type u}
  (F : α → f β) (x : γ ⊕ α) :
  eta (sum.traverse F x) = sum.traverse (@eta _ ∘ F) x :=
by cases x; simp! [sum.traverse] with norm; refl

end traverse

instance {γ : Type u} : traversable.{u} (sum γ) :=
{ traverse := @sum.traverse.{u} γ }

instance {γ : Type u} : is_lawful_traversable.{u} (sum γ) :=
{ id_traverse := @sum.id_traverse γ,
  traverse_comp := @sum.traverse_comp γ,
  map_traverse := @sum.map_traverse γ,
  morphism := @sum.morphism γ }

end sum
