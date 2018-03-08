/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/

import data.functor

universe variables u v w u' v' w'

section lemmas

open function applicative

variables {α β γ : Type u}
variables {f : Type u → Type v}
variables [applicative f]
variables (g : β → γ)

lemma applicative.map_seq_assoc
  (x : f (α → β)) (y : f α)
: @has_map.map f _ _ _ g (x <*> y) = comp g <$> x <*> y :=
by rw [← applicative.pure_seq_eq_map
      ,seq_assoc
      ,map_pure
      ,applicative.pure_seq_eq_map]

lemma applicative.seq_map_comm
  (x : f (γ → α)) (y : f β)
: x <*> g <$> y = flip comp g <$> x <*> y :=
begin
  rw [← pure_seq_eq_map _ y,seq_assoc,seq_pure,← functor.map_comp],
  refl,
end

end lemmas

namespace identity

open function

variables {α : Type u} {β : Type v} {γ : Type u'}

def pure : α → identity α := identity.mk

def seq : identity (α → β) → identity α → identity β
  | ⟨ f ⟩ ⟨ x ⟩ := ⟨ f x ⟩

local infix <$> := map
local infix <*> := seq

lemma pure_seq_eq_map (g : α → β) : ∀ (x : identity α), pure g <*> x = g <$> x
  | ⟨ x ⟩ := rfl

lemma map_pure (g : α → β) (x : α)
: g <$> pure x = pure (g x) :=
rfl

lemma seq_pure : ∀ (g : identity (α → β)) (x : α),
  g <*> pure x = (λ g : α → β, g x) <$> g
  | ⟨ g ⟩ x := rfl

lemma seq_assoc : ∀ (x : identity α) (g : identity (α → β)) (h : identity (β → γ)),
  h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x
| ⟨ x ⟩ ⟨ g ⟩ ⟨ h ⟩ := rfl

end identity

instance applicative_identity : applicative identity :=
{ map := @identity.map
, id_map := @identity.id_map
, pure := @identity.pure
, seq := @identity.seq
, pure_seq_eq_map := @identity.pure_seq_eq_map
, map_pure := @identity.map_pure
, seq_pure := @identity.seq_pure
, seq_assoc := @identity.seq_assoc }

@[norm]
lemma identity.mk_eq_pure {α : Type v} (x : α)
: identity.mk x = pure x := rfl

namespace compose

open function

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [applicative f] [applicative g]
variables {α β γ : Type v}

def seq : compose f g (α → β) → compose f g α → compose f g β
  | ⟨ h ⟩ ⟨ x ⟩ := ⟨ has_seq.seq <$> h <*> x ⟩

instance : has_pure (compose f g) :=
⟨ λ _ x, ⟨ pure $ pure x ⟩ ⟩

local infix ` <$> ` := map
local infix ` <*> ` := seq

lemma map_pure (h : α → β) (x : α) : (h <$> pure x : compose f g β) = pure (h x) :=
begin
  unfold has_pure.pure comp compose.map,
  apply congr_arg,
  rw [applicative.map_pure,applicative.map_pure],
end

lemma seq_pure (h : compose f g (α → β)) (x : α)
: h <*> pure x = (λ g : α → β, g x) <$> h :=
begin
  cases h with h,
  unfold compose.map has_pure.pure compose.seq comp,
  apply congr_arg,
  rw [applicative.seq_pure,← functor.map_comp],
  apply congr_fun, apply congr_arg,
  apply funext, intro y,
  unfold comp,
  apply applicative.seq_pure
end

lemma seq_assoc : ∀ (x : compose f g α) (h₀ : compose f g (α → β)) (h₁ : compose f g (β → γ)),
   h₁ <*> (h₀ <*> x) = (@comp α β γ <$> h₁) <*> h₀ <*> x
| ⟨ x ⟩ ⟨ h₀ ⟩ ⟨ h₁ ⟩ :=
begin
  unfold compose.seq compose.map,
  apply congr_arg,
  repeat { rw [applicative.seq_assoc] },
  apply congr_fun,
  apply congr_arg,
  rw [← functor.map_comp],
  rw [← functor.map_comp],
  rw [← applicative.pure_seq_eq_map has_seq.seq
     ,applicative.seq_assoc
     ,applicative.seq_pure _ has_seq.seq],
  repeat { rw [← functor.map_comp] },
  rw [applicative.map_seq_assoc has_seq.seq,← functor.map_comp],
  apply congr_fun,
  apply congr_arg,
  apply congr_fun,
  apply congr_arg,
  { apply funext, intro i,
    unfold comp,
    apply funext, intro j,
    apply funext, intro k,
    rw [applicative.seq_assoc] },
end

lemma pure_seq_eq_map (h : α → β) : ∀ (x : compose f g α), pure h <*> x = h <$> x
  | ⟨ x ⟩ :=
begin
  unfold has_pure.pure compose.seq compose.map comp,
  apply congr_arg,
  rw [applicative.map_pure,applicative.pure_seq_eq_map],
  apply congr_fun,
  apply congr_arg,
  apply funext, clear x, intro x,
  apply applicative.pure_seq_eq_map
end

instance applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
: applicative (compose f g) :=
{ map := @compose.map f g _ _
, id_map := @compose.id_map f g _ _
, map_comp := @compose.map_comp f g _ _
, seq := @compose.seq f g _ _
, pure_seq_eq_map := @compose.pure_seq_eq_map f g _ _
, map_pure := @compose.map_pure f g _ _
, seq_pure := @compose.seq_pure f g _ _
, seq_assoc := @compose.seq_assoc f g _ _
, ..compose.has_pure }

end compose

@[norm]
lemma compose.seq_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α))
: compose.mk h <*> compose.mk x = compose.mk (has_seq.seq <$> h <*> x) := rfl
