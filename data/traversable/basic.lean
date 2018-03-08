/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections

This is a work-in-progress
-/

import control.applicative

open function

universe variables w u v w' u' v'

section applicative_morphism

variables (f : Type u → Type v) [applicative f]
variables (g : Type u → Type w) [applicative g]

structure applicative_morphism : Type (max (u+1) v w) :=
  (F : ∀ {α : Type u}, f α → g α)
  (preserves_pure' : ∀ {α : Type u} (x : α), F (pure x) = pure x)
  (preserves_seq' : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

instance : has_coe_to_fun (applicative_morphism f g) :=
{ F := λ _, ∀ {α}, f α → g α,
  coe := λ m, m.F }

variables {F : applicative_morphism f g}

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
by { rw [← applicative.pure_seq_eq_map],
     simp! [*] with norm,
     rw applicative.pure_seq_eq_map }

open applicative_morphism

end applicative_morphism

class has_traverse (t : Type u → Type u) :=
(traverse : Π {m : Type u → Type u} [applicative m]
   {α β : Type u},
   (α → m β) → t α → m (t β))

open has_map

export has_traverse (traverse)

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}


variables {f : Type u → Type u} [applicative f]

def sequence [has_traverse t] :
  t (f α) → f (t α) :=
traverse id

end functions

class traversable (t : Type u → Type u)
extends has_traverse t, functor t :
  Type (u+1) :=
(id_traverse : ∀ {α : Type u} (x : t α), traverse (identity.mk) x = ⟨ x ⟩ )
(traverse_comp : ∀ {G H : Type u → Type u}
               [applicative G] [applicative H]
               {α β γ : Type u}
               (g : α → G β) (h : β → H γ) (x : t α),
   traverse (compose.mk ∘ has_map.map h ∘ g) x =
   ⟨ traverse h <$> traverse g x ⟩)
(map_traverse : ∀ {G : Type u → Type u}
               [applicative G]
               {α β γ : Type u}
               (g : α → G β) (h : β → γ)
               (x : t α),
               has_map.map h <$> traverse g x =
               traverse (has_map.map h ∘ g) x)
(morphism : ∀ {G H : Type u → Type u}
              [applicative G] [applicative H]
              (eta : applicative_morphism G H),
              ∀ {α β : Type u} (f : α → G β) (x : t α),
              eta (traverse f x) = traverse (@eta _ ∘ f) x)

export traversable


lemma map_identity_mk {α β : Type u}
  (f : α → β) :
  map f ∘ @identity.mk α = @identity.mk β ∘ f :=
rfl

attribute [norm] traversable.morphism

section traversable

variable {t : Type u → Type u}
variable [traversable t]
variables {G H : Type u → Type u}
variables [applicative G] [applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ


lemma traverse_eq_map_ident {x : t β} :
  traverse (identity.mk ∘ f) x = ⟨ f <$> x ⟩ :=
calc
      traverse (identity.mk ∘ f) x
    = traverse (map f ∘ identity.mk) x : by simp [map_identity_mk]
... = map f <$> traverse identity.mk x : by rw [← map_traverse]
... = map f <$> identity.mk x          : by simp [id_traverse]
... = ⟨ f <$> x ⟩                       : by refl

variable {eta : applicative_morphism G H}


end traversable
