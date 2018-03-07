/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections

This is a work-in-progress
-/

-- import util.control.applicative
-- import util.control.monad
import control.applicative
-- import util.data.ulift_t

open function

universe variables w u v w' u' v'

section applicative_morphism

variables {f : Type u → Type v} [applicative f]
variables {g : Type u → Type w} [applicative g]
variables (F : ∀ {α : Type u}, f α → g α)

structure applicative_morphism : Prop :=
  (preserves_pure : ∀ {α : Type u} (x : α), F (pure x) = pure x)
  (preserves_seq : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

variables {F}
variables morph : applicative_morphism @F
include morph

lemma applicative_morphism.preserves_map {α β : Type u} (x : α → β)  (y : f α)
: F (x <$> y) = x <$> F y :=
by rw [← applicative.pure_seq_eq_map
      ,morph.preserves_seq
      ,morph.preserves_pure
      ,applicative.pure_seq_eq_map]

end applicative_morphism

class has_traverse (t : Type u → Type v) :=
(traverse' : Π {m : Type (max u v) → Type w} [applicative m]
   {α β : Type u},
   (α → m (ulift β)) → t α → m (ulift.{u} (t β)))

open ulift (up down up_down) has_map

export has_traverse (traverse')

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}

def traverse [has_traverse.{v} t]
  (f : α → m β)
: t α → m (t β) :=
map down ∘ traverse'.{v} (λ x : α, up <$> (f x))

variables {f : Type u → Type u} [applicative f]

def sequence [has_traverse.{u u u} t]
: t (f α) → f (t α) :=
traverse id

end functions

set_option pp.universes true

class traversable (t : Type u → Type v)
extends has_traverse.{max u v} t, functor t
: Type (max v u+1) :=
(id_traverse : ∀ {α : Type u} (x : t α), traverse' (identity.mk ∘ up) x = ⟨ up x ⟩ )
(traverse_comp : ∀ {G H : Type (max u v) → Type (max u v)}
               [applicative G] [applicative H]
               {α β γ : Type u}
               (g : α → G (ulift.{v} β)) (h : β → H (ulift.{v} γ)) (x : t α),
   traverse' (compose.mk ∘ has_map.map (h ∘ down) ∘ g) x =
   ⟨ (traverse' h ∘ down) <$> traverse' g x ⟩)
(map_traverse : ∀ {G : Type (max u v) → Type (max u v)}
               [applicative G]
               {α β γ : Type u}
               (g : α → G (ulift.{v} β)) (h : β → γ)
               (x : t α),
               has_map.map (has_map.map h) <$> traverse' g x =
               traverse' (has_map.map (has_map.map h) ∘ g) x)
(morphism : ∀ {G H : Type (max u v) → Type (max u v)}
              [applicative G] [applicative H]
              {eta : ∀ {α}, G α → H α},
              applicative_morphism @eta →
              ∀ {α β : Type u} (f : α → G (ulift β)) (x : t α),
              eta (traverse' f x) = traverse' (eta ∘ f) x)

lemma down_map {α β : Type u}
  (f : α → β)
: down.{v} ∘ map f = f ∘ down.{v} :=
by { apply funext, intro, cases x, refl }

lemma map_identity_mk {α β : Type u}
  (f : α → β)
: map f ∘ @identity.mk α = @identity.mk β ∘ f :=
rfl

section traversable

variable {t : Type u → Type u}
variable [traversable t]
variables {G H : Type u → Type u}
variables [applicative G] [applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ

lemma id_traverse {x : t α}
: traverse identity.mk x = ⟨ x ⟩ :=
by simp [traverse,function.comp,map,identity.map,traversable.id_traverse x]

lemma functor.map_comp_rev {f : Type u → Type v} [functor f]
  (F : α → β) (G : β → γ) (x : f α)
: G <$> F <$> x = (G ∘ F) <$> x :=
by rw @functor.map_comp f _ _ _ _ F G x

lemma traverse_comp {x : t α}
: traverse (compose.mk ∘ map h ∘ g) x = ⟨ traverse h <$> traverse g x ⟩ :=
begin
  have H := traversable.traverse_comp (map up.{u u} ∘ g) (map up.{u u} ∘ h) x,
  simp [function.comp,functor.map_comp_rev] at *,
  simp [traverse],
  simp [function.comp,map,compose.map,functor.map_comp_rev,H],
end

lemma map_traverse {x : t α}
: map f <$> traverse g x = traverse (map f ∘ g) x :=
begin
  unfold traverse function.comp,
  simp [functor.map_comp_rev],
  have H := @traversable.map_traverse t _ G _ α β γ (map up ∘ g) f x,
  rw [← down_map,functor.map_comp],
  simp [H],
  apply congr_arg,
  apply congr_fun,
  apply  funext, intro,
  simp [function.comp, functor.map_comp_rev,map],
end

lemma traverse_eq_map_ident {x : t β}
: traverse (identity.mk ∘ f) x = ⟨ f <$> x ⟩ :=
calc
      traverse (identity.mk ∘ f) x
    = traverse (map f ∘ identity.mk) x : by simp [map_identity_mk]
... = map f <$> traverse identity.mk x : by rw [← map_traverse]
... = map f <$> identity.mk x          : by simp [id_traverse]
... = ⟨ f <$> x ⟩                      : by refl

variable {eta : Π {α}, G α → H α}
variable (morph : applicative_morphism @eta)

include morph

lemma traverse_morphism (x : t α) (h : α → G β)
: eta (traverse h x) = traverse (eta ∘ h) x :=
calc
       eta (traverse h x)
     = eta (down <$> traverse'.{u u} (λ (x : α), up <$> h x) x) : rfl
 ... = down <$> eta (traverse'.{u u u} (map up ∘ h) x) : by simp [morph.preserves_map]
 ... = down <$> traverse' (eta ∘ (map up ∘ h)) x     : by simp [traversable.morphism.{u u} morph]
 ... = down <$> traverse' (map up ∘ eta ∘ h) x       : by simp [comp,morph.preserves_map]
 ... = traverse (eta ∘ h) x                          : rfl

end traversable
