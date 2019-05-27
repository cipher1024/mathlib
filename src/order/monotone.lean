/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon

Bundled monotone functions
-/

import order.basic

section is_monotone_def

variables {α : Type*} {β : Type*} {γ : Type*} {ω : Type*}

variables [preorder α] [preorder β] [preorder γ] [preorder ω]

class is_monotone (f : α → β) : Prop :=
(mono' : monotone f)

lemma is_monotone.mono {f : α → β} (hf : is_monotone f) : monotone f :=
is_monotone.mono' f

end is_monotone_def

namespace is_monotone

open function

variables {α : Type*} {β : Type*} {γ : Type*} {ω : Type*}

variables [preorder α] [preorder β] [preorder γ] [preorder ω]

variables (f : α → β → γ)

@[instance]
lemma monotone_uncurry
  [h₀ : is_monotone f] [h₁ : monotone $ flip f] :
  is_monotone (uncurry f) :=
⟨ λ ⟨a,a'⟩ ⟨b,b'⟩ h,
  show f a a' ≤ f b b', from
    le_trans
      (show f a a' ≤ f b a', from is_monotone.mono h₀ h.1 _ )
      (show f b a' ≤ f b b', from h₁ h.2 _)
⟩
variables {f} [hf : is_monotone (uncurry f)]

-- @[instance]
-- lemma monotone_uncurry_comp {g : ω → α}
--   [hg : is_monotone g] :
--   is_monotone (uncurry (f ∘ g)) :=
-- ⟨ λ ⟨a,a'⟩ ⟨b,b'⟩ h, @is_monotone.mono _ _ _ _ _ hf (g a, a') (g b, b') ⟨is_monotone.mono hg h.1,h.2⟩ ⟩

-- @[instance]
-- lemma monotone_uncurry_comp' {g : α → ω → β}
--   [hg : is_monotone (uncurry g)] :
--   is_monotone (uncurry (λ x, f x ∘ g x)) :=
-- λ ⟨a,a'⟩ ⟨b,b'⟩ h, @hf (_, _) (_, _) ⟨h.1,@hg (a,a') (b,b') h⟩

-- @[instance]
-- lemma monotone_of_monotone_uncurry : is_monotone f :=
-- λ a b h x, @hf (a,x) (b,x) ⟨h,le_refl _⟩

-- @[instance]
-- lemma monotone_of_monotone_uncurry' : ∀ x, is_monotone (f x) :=
-- λ x a b h, @hf (x,a) (x,b) ⟨le_refl _,h⟩

-- @[instance]
-- lemma monotone_flip_of_monotone_uncurry : is_monotone (flip f) :=
-- λ a b h x, @hf (x,a) (x,b) ⟨le_refl _,h⟩

-- @[instance]
-- lemma monotone_flip_of_monotone_uncurry' : ∀ x, is_monotone (flip f x) :=
-- λ x a b h, @hf (a,x) (b,x) ⟨h,le_refl _⟩

instance id : is_monotone $ @id α :=
⟨ monotone_id ⟩

instance const (x : α) : is_monotone $ @const α β x :=
⟨ monotone_const x ⟩

instance val {p : α → Prop} : is_monotone $ @subtype.val α p :=
⟨ subtype.monotone_val ⟩

instance fst : is_monotone $ @prod.fst α β :=
⟨ prod.monotone_fst ⟩

instance snd : is_monotone $ @prod.snd α β :=
⟨ prod.monotone_snd ⟩

end is_monotone

section Mono_def

variables {α : Type*} {β : Type*} {γ : Type*} {ω : Type*}

variables [preorder α] [preorder β] [preorder γ] [preorder ω]

variables (α β)
-- variables (α : Type*) (β : Type*) (γ : Type*) [preorder α] [preorder β] [preorder γ]

structure Mono :=
mk' :: (F : α → β)
       [mono' : is_monotone F]

infixr ` →ₘ `:25 := Mono
-- infixr ` →𝔪 `:25 := Mono

instance : has_coe_to_fun (α →ₘ β) :=
{ F := λ _, α → β,
  coe := Mono.F }

instance is_monotone.coe (f : α →ₘ β) : is_monotone f :=
f.mono'

end Mono_def

namespace Mono

variables {α : Type*} {β : Type*} {γ : Type*} {ω : Type*}

variables [preorder α] [preorder β] [preorder γ] [preorder ω]

variables {α β γ}

def mk (f : α → β) (hf : monotone f) := @Mono.mk' α β _ _ f ⟨hf⟩

def mono (f : α →ₘ β) : monotone f := f.mono'.mono

def val (p : α → Prop) : subtype p →ₘ α := ⟨subtype.val⟩

lemma ext' : Π {x y : α →ₘ β} (h : x.F = y.F), x = y
| (@Mono.mk' _ _ _ _  x _) (@Mono.mk' _ _ _ _  y _) :=

assume h : x = y, by congr; exact h

instance : preorder (α →ₘ β) :=
{ le := λ x y, x.F ≤ y.F,
  le_refl := λ x, le_refl x,
  le_trans := λ x y z, le_trans }

instance {α β} [partial_order α] [partial_order β] : partial_order (α →ₘ β) :=
{ le_antisymm := λ a b h h', ext' (le_antisymm h h'),
  .. Mono.preorder }

def comp (f : β →ₘ γ) (g : α →ₘ β) : α →ₘ γ :=
{ F := f ∘ g, mono' := ⟨ monotone_comp g.mono f.mono ⟩ }

infixr ∘ := comp

section

variables (α β)
def FF : (α →ₘ β) →ₘ (α → β) :=
Mono.mk Mono.F $ λ x y h, h

end

def id : α →ₘ α :=
Mono.mk' id

def const (x : α) : β →ₘ α :=
Mono.mk' (function.const _ x)

def split (f : α × α →ₘ β) : α →ₘ β :=
mk (λ x, f (x, x)) $ λ a b h, f.mono ⟨h,h⟩

def flip (f : α × β →ₘ γ) : β × α →ₘ γ :=
mk (λ x, f x.swap) (λ a b h, f.mono ⟨h.2,h.1⟩)

def fst (f : α × β →ₘ γ) : β → α →ₘ γ :=
λ x, mk (λ y, f (y,x)) (λ a b h, f.mono ⟨h,le_refl _⟩)

def fst' (f : α × β →ₘ γ) : α →ₘ β → γ :=
mk (λ x y, f (x,y)) (λ a b h z, f.mono ⟨h,le_refl _⟩)

def snd (f : α × β →ₘ γ) : α → β →ₘ γ :=
λ x, mk (λ y, f (x,y)) (λ a b h, f.mono ⟨le_refl _,h⟩)

def snd' (f : α × β →ₘ γ) : β →ₘ α → γ :=
mk (λ x y, f (y,x)) (λ a b h z, f.mono ⟨le_refl _, h⟩)

def first (f : α →ₘ γ) : α × β →ₘ γ × β :=
mk (prod.map f _root_.id) (λ ⟨a,a'⟩ ⟨b,b'⟩ h, ⟨f.mono h.1,h.2⟩)

def ite (p : Prop) [decidable p] (f g : α →ₘ β) : α →ₘ β :=
mk (λ x, if p then f x else g x)
   (λ a b h, by split_ifs; [exact f.mono h, exact g.mono h])

instance fst.is_monotone (f : α × β →ₘ γ) : is_monotone f.fst :=
⟨ λ x y h a, f.mono ⟨le_refl _, h⟩ ⟩

instance snd.is_monotone (f : α × β →ₘ γ) : is_monotone f.snd :=
⟨ λ x y h a, f.mono ⟨h, le_refl _⟩ ⟩

variables {f : α →ₘ β} {g : β →ₘ γ}

@[simp]
lemma split_def (f : α × α →ₘ β) (x : α) : split f x = f (x, x) := rfl

@[simp]
lemma fst_flip (f : α × β →ₘ γ) (x : α) : f.flip.fst x = f.snd x := rfl

@[simp]
lemma fst_flip' (f : α × β →ₘ γ) : f.flip.fst' = f.snd' := rfl

@[simp]
lemma snd_flip (f : α × β →ₘ γ) (x : β) : f.flip.snd x = f.fst x := rfl

@[simp]
lemma snd_flip' (f : α × β →ₘ γ) : f.flip.snd' = f.fst' := rfl

@[simp]
lemma comp_def (x : α) : (g ∘ f : α →ₘ γ) x = g (f x) := rfl

@[simp]
lemma mk_coe_to_fun (f : α →ₘ β) : (mk' f : α →ₘ β) = f :=
by cases f; refl

@[simp]
lemma coe_to_fun_mk_def' (f : α → β) [is_monotone f] (x : α) : (mk' f : α →ₘ β) x = f x := rfl

@[simp]
lemma coe_to_fun_mk_def (f : α → β) (hf : monotone f) (x : α) : (mk f hf) x = f x := rfl

section coe_to_fun_proj

variables {f' : α × β →ₘ γ} {x : α} {y : β}

lemma coe_to_fun_fst :  f'.fst y x  = f' (x, y) := rfl

lemma coe_to_fun_fst' : f'.fst' x y = f' (x, y) := rfl

lemma coe_to_fun_snd :  f'.snd x y  = f' (x, y) := rfl

lemma coe_to_fun_snd' : f'.snd' y x = f' (x, y) := rfl

lemma coe_to_fun_fst_swap : f'.fst y x = f'.fst' x y := rfl

lemma coe_to_fun_snd_swap : f'.snd x y = f'.snd' y x := rfl

lemma coe_to_fun_fst_eq_snd : f'.fst y x = f'.snd x y := rfl

lemma coe_to_fun_fst_eq_snd' : f'.fst' x y = f'.snd' y x := rfl

end coe_to_fun_proj

@[extensionality]
lemma ext {g : α →ₘ β} (h : ∀ x, f x = g x) : f = g :=
by { casesm* _ →ₘ _, suffices : f_F = g_F, subst this, ext, apply h }

namespace subtype

-- def val

end subtype


end Mono

namespace Mono

variables {α : Type*} {β : α → Type*} (γ : Π a, β a → Type*)
variables [Π a b, preorder $ γ a b]

def curry : (Π a : sigma β, γ a.1 a.2) →ₘ (Π a b, γ a b) := Mono.mk function.curry' (monotone_curry' _ _ _)
def uncurry : (Π a b, γ a b) →ₘ (Π a : sigma β, γ a.1 a.2) := Mono.mk function.uncurry' (monotone_uncurry' _ _ _)
open function (curry' uncurry')

@[simp] lemma coe_to_fun_curry (f : Π a : sigma β, γ a.1 a.2) : curry γ f = curry' f := rfl
@[simp] lemma coe_to_fun_uncurry (f : Π a b, γ a b) : uncurry γ f = uncurry' f := rfl

end Mono
