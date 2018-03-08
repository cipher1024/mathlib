
import .basic
import category.basic
import control.applicative
import data.ulift

universe variables w u v w' u' v'

open ulift function

section identity

open function has_map

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def identity.traverse (g : α → f (ulift.{u} β)) : identity α → f (ulift.{u} (identity β))
 | ⟨ x ⟩ := (λ x : ulift.{u} β, up ⟨ down x ⟩) <$> g x

instance : has_traverse.{v} identity :=
⟨ @identity.traverse ⟩

lemma identity.traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: identity.traverse g ⟨ x ⟩ = (up ∘ identity.mk ∘ down) <$> (g x) :=
rfl

lemma identity.traverse_mk' (g : α → f (ulift.{u} β))
: identity.traverse g ∘ identity.mk = map (up ∘ identity.mk ∘ down) ∘ g :=
rfl

lemma identity.id_traverse (x : identity α)
: identity.traverse (identity.mk ∘ up) x = identity.mk (up.{u} x) :=
by { cases x, unfold identity.traverse, refl }

lemma identity.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : identity α),
        identity.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((identity.traverse h ∘ down) <$> identity.traverse g x)
  | ⟨ x ⟩ :=
begin
  unfold identity.traverse comp,
  rw [compose.map_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp],
  refl,
end

lemma identity.map_traverse
   (g : α → f' (ulift.{u} β)) (f : β → γ)
   (x : identity α)
: map (map f) <$> identity.traverse g x = identity.traverse (map (map f) ∘ g) x :=
by cases x with x; simp! with norm; refl

variable (eta : applicative_morphism f f')

lemma identity.morphism {α β : Type u}
  (F : α → f (ulift.{u} β)) (x : identity α)
: eta (identity.traverse F x) = identity.traverse (@eta _ ∘ F) x :=
by cases x with x; simp! with norm

end identity

instance : traversable identity :=
{ to_functor := (identity_functor : functor identity)
, traverse' := @identity.traverse
, id_traverse := λ α x, @identity.id_traverse α x
, traverse_comp := @identity.traverse_comp
, map_traverse := @identity.map_traverse
, morphism := @identity.morphism }

section option

open function has_map

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def option.traverse (g : α → f (ulift.{u} β)) : option α → f (ulift.{u} (option β))
 | none := pure (up none)
 | (some x) := map some <$> g x

lemma option.traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: option.traverse g (some x) = map some <$> (g x) :=
rfl

lemma option.traverse_mk' (g : α → f (ulift.{u} β))
: option.traverse g ∘ some = map (map some) ∘ g :=
rfl

lemma option.id_traverse (x : option α)
: option.traverse (identity.mk ∘ up) x = ⟨ up x ⟩ :=
by { cases x ; unfold option.traverse ; refl }

lemma option.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : option α),
        option.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((option.traverse h ∘ down) <$> option.traverse g x) :=
by intro x; cases x ; simp! with norm ; refl

lemma option.map_traverse (g : α -> f' (ulift.{u} β)) (f : β → γ)
  (x : option α)
: map (map f) <$> option.traverse g x = option.traverse (map (map f) ∘ g) x :=
by cases x ; simp! with norm ; refl

variable (eta : applicative_morphism f f')

lemma option.morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : option α)
: eta (option.traverse g x) = option.traverse (@eta _ ∘ g) x :=
by cases x with x ; simp! [*] with norm

end option

instance : traversable option :=
{ to_functor := _
, traverse' := @option.traverse
, id_traverse := @option.id_traverse
, traverse_comp := @option.traverse_comp
, map_traverse := @option.map_traverse
, morphism := @option.morphism }

section list

variables {f : Type u → Type v}
variables [applicative f]
variables {α β : Type u}

open applicative has_map
open list (cons)

def list.traverse (g : α → f (ulift.{u} β)) : list α → f (ulift.{u} (list β))
 | [] := pure $ up []
 | (x :: xs) := lift₂ cons <$> g x <*> list.traverse xs

end list

section list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

open applicative has_map
open list (cons)

lemma list.id_traverse (xs : list α)
: list.traverse (identity.mk ∘ up) xs = ⟨ up xs ⟩ :=
by induction xs ; simp! [*] with norm ; refl

lemma list.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : list α),
        list.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((list.traverse h ∘ down) <$> list.traverse g x) :=
begin
  intro x, induction x ;
  simp! [*] with norm ; refl,
end

lemma list.map_traverse {α β γ : Type u} (g : α → f' (ulift.{u} β)) (f : β → γ)
  (x : list α)
: map (map f) <$> list.traverse g x = list.traverse (map (map f) ∘ g) x :=
begin
  symmetry,
  induction x with x xs ih ;
  simp! [*] with norm ; refl
end

variable (eta : applicative_morphism f f')

lemma list.morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : list α)
: eta (list.traverse g x) = list.traverse (@eta _ ∘ g) x :=
by induction x ; simp! [*] with norm

end list

instance : has_traverse.{v} list :=
{ traverse' := @list.traverse }

instance : traversable list :=
{ to_functor := _
, traverse' := @list.traverse
, id_traverse := @list.id_traverse
, traverse_comp := @list.traverse_comp
, map_traverse := @list.map_traverse
, morphism := @list.morphism }
