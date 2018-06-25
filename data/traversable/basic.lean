/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections

This is a work-in-progress
-/

import category.applicative

open function

universe variables w u v w' u' v'

section applicative_morphism

variables (f : Type u → Type v) [applicative f] [is_lawful_applicative f]
variables (g : Type u → Type w) [applicative g] [is_lawful_applicative g]

structure applicative_morphism : Type (max (u+1) v w) :=
(F : ∀ {α : Type u}, f α → g α)
(preserves_pure' : ∀ {α : Type u} (x : α), F (pure x) = pure x)
(preserves_seq' : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

instance : has_coe_to_fun (applicative_morphism f g) :=
{ F := λ _, ∀ {α}, f α → g α,
  coe := λ m, m.F }

variables {f g}
variables (F : applicative_morphism f g)

@[norm]
lemma applicative_morphism.preserves_pure :
  ∀ {α : Type u} (x : α), F (pure x) = pure x :=
by apply applicative_morphism.preserves_pure'
@[norm]
lemma applicative_morphism.preserves_seq :
  ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y :=
by apply applicative_morphism.preserves_seq'

@[norm]
lemma applicative_morphism.preserves_map {α β : Type u} (x : α → β)  (y : f α) :
  F (x <$> y) = x <$> F y :=
by rw [← pure_seq_eq_map,F.preserves_seq]; simp with norm

open applicative_morphism

end applicative_morphism

class traversable (t : Type u → Type u)
extends functor t :=
(traverse : Π {m : Type u → Type u} [applicative m]
   {α β : Type u},
   (α → m β) → t α → m (t β))

open functor

export traversable (traverse)

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}


variables {f : Type u → Type u} [applicative f]

def sequence [traversable t] :
  t (f α) → f (t α) :=
traverse id

end functions

class is_lawful_traversable (t : Type u → Type u) [traversable t]
extends is_lawful_functor t :
  Type (u+1) :=
(id_traverse : ∀ {α : Type u} (x : t α), traverse identity.mk x = x )
(traverse_comp : ∀ {G H : Type u → Type u}
               [applicative G] [applicative H]
               [is_lawful_applicative G] [is_lawful_applicative H]
               {α β γ : Type u}
               (g : α → G β) (h : β → H γ) (x : t α),
   traverse (compose.mk ∘ functor.map h ∘ g) x =
   ⟨ traverse h <$> traverse g x ⟩)
(map_traverse : ∀ {G : Type u → Type u}
               [applicative G] [is_lawful_applicative G]
               {α β γ : Type u}
               (g : α → G β) (h : β → γ)
               (x : t α),
               functor.map h <$> traverse g x =
               traverse (functor.map h ∘ g) x)
(morphism : ∀ {G H : Type u → Type u}
              [applicative G] [applicative H]
              [is_lawful_applicative G] [is_lawful_applicative H]
              (eta : applicative_morphism G H),
              ∀ {α β : Type u} (f : α → G β) (x : t α),
              eta (traverse f x) = traverse (@eta _ ∘ f) x)

open is_lawful_traversable

lemma map_identity_mk {α β : Type u}
  (f : α → β) :
  map f ∘ @identity.mk α = @identity.mk β ∘ f :=
rfl

attribute [norm] is_lawful_traversable.morphism

section traversable

variable {t : Type u → Type u}
variables [traversable t] [is_lawful_traversable t]
variables {G H : Type u → Type u}
variables [applicative G] [is_lawful_applicative G]
variables [applicative H] [is_lawful_applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ


lemma traverse_eq_map_ident {x : t β} :
  traverse (identity.mk ∘ f) x = map f <$> x :=
calc
      traverse (identity.mk ∘ f) x
    = traverse (map f ∘ identity.mk) x : by simp [map_identity_mk]
... = map f <$> traverse identity.mk x : by rw [← map_traverse]
... = map f <$> identity.mk x          : by simp [id_traverse]; refl
... = map f <$> x                      : by refl

variable {eta : applicative_morphism G H}


end traversable
