/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/

import category.functor

universe variables u v w u' v' w'

section lemmas

open function applicative

variables {α β γ : Type u}
variables {f : Type u → Type v}
variables [applicative f] [is_lawful_applicative f]
variables (g : β → γ)

lemma pure_seq_pure {α β : Type u} (g : α → β) (x : α) :
  pure g <*> (pure x : f α) = pure (g x) :=
by simp

open function

lemma applicative.map_seq {β γ σ : Type u} (h : γ → σ) (x : f (β → γ)) (y : f β) :
  h <$> (x <*> y) = (comp h <$> x) <*> y :=
by rw [← pure_seq_eq_map,← pure_seq_eq_map,
       seq_assoc,map_pure]

lemma applicative.seq_map {β γ σ : Type u} (h : σ → β) (x : f (β → γ)) (y : f σ) :
  x <*> (h <$> y) = (flip comp h) <$> x <*> y :=
begin
  rw [← pure_seq_eq_map,← pure_seq_eq_map,
      seq_assoc,
      seq_pure,
      pure_seq_eq_map,
      ← comp_map] ,
  refl
end

open applicative functor

attribute [norm] seq_assoc pure_seq_eq_map map_pure seq_map map_seq

lemma applicative.map_seq_map {α β γ σ : Type u} (g : α → β → γ) (h : σ → β) (x : f α) (y : f σ) :
  (g <$> x) <*> (h <$> y) = (flip comp h ∘ g) <$> x <*> y :=
by simp with norm

lemma applicative.map_seq_assoc
  (x : f (α → β)) (y : f α) :
  @functor.map f _ _ _ g (x <*> y) = comp g <$> x <*> y :=
by rw [← pure_seq_eq_map,
       seq_assoc, map_pure,
       pure_seq_eq_map]

lemma applicative.seq_map_comm
  (x : f (γ → α)) (y : f β) :
  x <*> g <$> y = flip comp g <$> x <*> y :=
begin
  rw [← pure_seq_eq_map _ y, seq_assoc, seq_pure, ← comp_map],
  refl,
end

end lemmas

instance applicative_id : applicative id :=
{ pure := @id,
  seq := λ α β f, f }
instance lawful_applicative_id : is_lawful_applicative id :=
by refine { .. } ; intros ; refl

namespace compose

open function

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [applicative f] [applicative g]

def seq  {α β : Type v} : compose f g (α → β) → compose f g α → compose f g β
  | ⟨ h ⟩ ⟨ x ⟩ := ⟨ has_seq.seq <$> h <*> x ⟩

instance : has_pure (compose f g) :=
⟨ λ _ x, ⟨ pure $ pure x ⟩ ⟩

local infix ` <$> ` := compose.map
local infix ` <*> ` := seq

variables [is_lawful_applicative f] [is_lawful_applicative g]
variables {α β γ : Type v}

lemma map_pure (h : α → β) (x : α) : (h <$> pure x : compose f g β) = pure (h x) :=
begin
  unfold has_pure.pure comp compose.map,
  apply congr_arg,
  rw [map_pure, map_pure],
end

lemma seq_pure (h : compose f g (α → β)) (x : α) :
  h <*> pure x = (λ g : α → β, g x) <$> h :=
begin
  cases h with h,
  unfold compose.map has_pure.pure compose.seq comp,
  apply congr_arg,
  rw [seq_pure, ← comp_map],
  apply congr_fun, apply congr_arg,
  apply funext, intro y,
  unfold comp,
  apply seq_pure
end

lemma seq_assoc : ∀ (x : compose f g α) (h₀ : compose f g (α → β)) (h₁ : compose f g (β → γ)),
   h₁ <*> (h₀ <*> x) = (@comp α β γ <$> h₁) <*> h₀ <*> x
| ⟨ x ⟩ ⟨ h₀ ⟩ ⟨ h₁ ⟩ :=
by simp! [(∘),flip] with norm

lemma pure_seq_eq_map (h : α → β) : ∀ (x : compose f g α), pure h <*> x = h <$> x
  | ⟨ x ⟩ :=
begin
  simp! with norm,
  congr, funext, simp with norm,
end

instance applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g] :
  applicative (compose f g) :=
{ map := @compose.map f g _ _,
  seq := @compose.seq f g _ _,
  ..compose.has_pure }

instance lawful_applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
  [is_lawful_applicative f] [is_lawful_applicative g] :
  is_lawful_applicative (compose f g) :=
{ pure_seq_eq_map := @compose.pure_seq_eq_map f g _ _ _ _,
  map_pure := @compose.map_pure f g _ _ _ _,
  seq_pure := @compose.seq_pure f g _ _ _ _,
  seq_assoc := @compose.seq_assoc f g _ _ _ _,
  ..lawful_functor_compose }

end compose

@[norm]
lemma compose.seq_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α)) :
  compose.mk h <*> compose.mk x = compose.mk (has_seq.seq <$> h <*> x) := rfl
