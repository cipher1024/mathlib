/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete lattices.
-/
import order.bounded_lattice data.set.basic tactic.pi_instances

set_option old_structure_cmd true
open set

namespace lattice
universes u v w w₂
variables {α : Type u} {β : Type v} {ι : Sort w} {ι₂ : Sort w₂}

/-- class for the `Sup` operator -/
class has_Sup (α : Type u) := (Sup : set α → α)
/-- class for the `Inf` operator -/
class has_Inf (α : Type u) := (Inf : set α → α)
/-- Supremum of a set -/
def Sup [has_Sup α] : set α → α := has_Sup.Sup
/-- Infimum of a set -/
def Inf [has_Inf α] : set α → α := has_Inf.Inf
/-- Indexed supremum -/
def supr [has_Sup α] (s : ι → α) : α := Sup (range s)
/-- Indexed infimum -/
def infi [has_Inf α] (s : ι → α) : α := Inf (range s)

lemma has_Inf_to_nonempty (α) [has_Inf α] : nonempty α := ⟨Inf ∅⟩
lemma has_Sup_to_nonempty (α) [has_Sup α] : nonempty α := ⟨Sup ∅⟩

notation `⨆` binders `, ` r:(scoped f, supr f) := r
notation `⨅` binders `, ` r:(scoped f, infi f) := r

meta def prove_default_bounds : tactic unit :=
`[ intro, apply Sup_le, exact λ b, false.elim ] <|>
`[ intro, apply le_Sup, exact  (mem_univ _) ] <|>
`[ intro, apply Inf_le, exact  (mem_univ _) ] <|>
`[ intro, apply le_Inf, exact  λ b, false.elim ]

class complete_semilattice_sup (α : Type u)
extends semilattice_sup α, semilattice_sup_bot α, semilattice_sup_top α, has_Sup α :=
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
-- (to_semilattice_sup_bot := _)
(bot := Sup ∅)
(top := Sup univ)
-- (bot_le : _ . prove_default_bounds)
-- (le_top := λ a, Sup_le _ _ (λ b, false.elim))

-- section complete_semilattice_sup
-- open complete_semilattice_sup
-- variables [𝓛 : complete_semilattice_sup α]

-- @[priority 0]
-- instance : semilattice_sup_bot α :=
-- { bot := Sup ∅,
--   bot_le := λ a, Sup_le _ _ $ λ b, false.elim,
--   .. 𝓛 }

-- @[priority 0]
-- instance : semilattice_sup_top α :=
-- { top := Sup univ,
--   le_top := λ a, le_Sup _ _ (mem_univ _),
--   .. 𝓛 }

-- end complete_semilattice_sup

class complete_semilattice_inf (α : Type u)
extends semilattice_inf α, semilattice_inf_bot α, semilattice_inf_top α, has_Inf α :=
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)
(bot := Inf univ)
(top := Inf ∅)
-- (bot_le := λ a, Inf_le _ _ (mem_univ _))
-- (le_top := λ a, le_Inf _ _ $ λ b, false.elim)

-- section complete_semilattice_inf
-- open complete_semilattice_inf
-- variables [𝓛 : complete_semilattice_inf α]

-- @[priority 0]
-- instance : semilattice_inf_bot α :=
-- { bot := Inf univ,
--   bot_le := λ a, Inf_le _ _ (mem_univ _),
--   .. 𝓛 }

-- @[priority 0]
-- instance : semilattice_inf_top α :=
-- { top := Inf ∅,
--   le_top := λ a, le_Inf _ _ $ λ b, false.elim,
--   .. 𝓛 }

-- end complete_semilattice_inf

/-- A complete lattice is a bounded lattice which
  has suprema and infima for every subset. -/
class complete_lattice (α : Type u)
extends complete_semilattice_inf α, complete_semilattice_sup α, bounded_lattice α
-- extends bounded_lattice α, has_Sup α, has_Inf α :=
--  (le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
--  (Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
--  (Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
--  (le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)

-- instance [𝓛 : complete_lattice α] : bounded_lattice α :=
-- { bot := Inf univ,
--   top := Sup univ,
--   bot_le := λ a, complete_lattice.Inf_le _ _ trivial,
--   le_top := λ a, complete_lattice.le_Sup _ _ trivial,
--   .. 𝓛 }

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class complete_linear_order (α : Type u) extends complete_lattice α, decidable_linear_order α

section
variables [complete_semilattice_sup α] {s t : set α} {a b : α}

@[ematch] theorem le_Sup : a ∈ s → a ≤ Sup s := complete_semilattice_sup.le_Sup s a

theorem Sup_le : (∀b∈s, b ≤ a) → Sup s ≤ a := complete_semilattice_sup.Sup_le s a

theorem le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_Sup hb)

theorem Sup_le_Sup (h : s ⊆ t) : Sup s ≤ Sup t :=
Sup_le (assume a, assume ha : a ∈ s, le_Sup $ h ha)

@[simp] theorem Sup_le_iff : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
⟨assume : Sup s ≤ a, assume b, assume : b ∈ s,
  le_trans (le_Sup ‹b ∈ s›) ‹Sup s ≤ a›,
  Sup_le⟩

-- TODO: it is weird that we have to add union_def
theorem Sup_union {s t : set α} : Sup (s ∪ t) = Sup s ⊔ Sup t :=
le_antisymm
  (Sup_le $ assume a h, or.rec_on h (le_sup_left_of_le ∘ le_Sup) (le_sup_right_of_le ∘ le_Sup))
  (sup_le (Sup_le_Sup $ subset_union_left _ _) (Sup_le_Sup $ subset_union_right _ _))

/- old proof:
le_antisymm
  (Sup_le $ assume a h, or.rec_on h (le_sup_left_of_le ∘ le_Sup) (le_sup_right_of_le ∘ le_Sup))
  (sup_le (Sup_le_Sup $ subset_union_left _ _) (Sup_le_Sup $ subset_union_right _ _))
-/

@[simp] theorem Sup_empty : Sup ∅ = (⊥ : α) :=
le_antisymm (by finish) (by finish)
-- le_antisymm (Sup_le (assume _, false.elim)) bot_le

@[simp] theorem Sup_univ : Sup univ = (⊤ : α) :=
le_antisymm (by finish) (le_Sup ⟨⟩) -- finish fails because ⊤ ≤ a simplifies to a = ⊤
--le_antisymm le_top (le_Sup ⟨⟩)

-- TODO(Jeremy): get this automatically
@[simp] theorem Sup_insert {a : α} {s : set α} : Sup (insert a s) = a ⊔ Sup s :=
have Sup {b | b = a} = a,
  from le_antisymm (Sup_le $ assume b b_eq, b_eq ▸ le_refl _) (le_Sup rfl),
calc Sup (insert a s) = Sup {b | b = a} ⊔ Sup s : Sup_union
                  ... = a ⊔ Sup s : by rw [this]

@[simp] theorem Sup_singleton {a : α} : Sup {a} = a :=
by finish [singleton_def]
--eq.trans Sup_insert $ by simp

@[simp] theorem Sup_eq_bot : Sup s = ⊥ ↔ (∀a∈s, a = ⊥) :=
iff.intro
  (assume h a ha, bot_unique $ h ▸ le_Sup ha)
  (assume h, bot_unique $ Sup_le $ assume a ha, le_bot_iff.2 $ h a ha)

end

section
variables [complete_semilattice_inf α] {s t : set α} {a b : α}

@[ematch] theorem Inf_le : a ∈ s → Inf s ≤ a := complete_semilattice_inf.Inf_le s a

theorem le_Inf : (∀b∈s, a ≤ b) → a ≤ Inf s := complete_semilattice_inf.le_Inf s a

theorem Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (Inf_le hb) h

theorem Inf_le_Inf (h : s ⊆ t) : Inf t ≤ Inf s :=
le_Inf (assume a, assume ha : a ∈ s, Inf_le $ h ha)

@[simp]
theorem le_Inf_iff : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
⟨assume : a ≤ Inf s, assume b, assume : b ∈ s,
  le_trans ‹a ≤ Inf s› (Inf_le ‹b ∈ s›),
  le_Inf⟩

theorem Inf_union {s t : set α} : Inf (s ∪ t) = Inf s ⊓ Inf t :=
le_antisymm
  (le_inf (Inf_le_Inf $ subset_union_left _ _) (Inf_le_Inf $ subset_union_right _ _))
  (le_Inf $ assume a h, or.rec_on h (inf_le_left_of_le ∘ Inf_le) (inf_le_right_of_le ∘ Inf_le))

/- old proof:
le_antisymm
  (le_inf (Inf_le_Inf $ subset_union_left _ _) (Inf_le_Inf $ subset_union_right _ _))
  (le_Inf $ assume a h, or.rec_on h (inf_le_left_of_le ∘ Inf_le) (inf_le_right_of_le ∘ Inf_le))
-/

@[simp] theorem Inf_empty : Inf ∅ = (⊤ : α) :=
le_antisymm (by finish) (by finish)
--le_antisymm le_top (le_Inf (assume _, false.elim))

@[simp] theorem Inf_univ : Inf univ = (⊥ : α) :=
le_antisymm (Inf_le ⟨⟩) bot_le

@[simp] theorem Inf_insert {a : α} {s : set α} : Inf (insert a s) = a ⊓ Inf s :=
have Inf {b | b = a} = a,
  from le_antisymm (Inf_le rfl) (le_Inf $ assume b b_eq, b_eq ▸ le_refl _),
calc Inf (insert a s) = Inf {b | b = a} ⊓ Inf s : Inf_union
                  ... = a ⊓ Inf s : by rw [this]

@[simp] theorem Inf_singleton {a : α} : Inf {a} = a :=
by finish [singleton_def]
--eq.trans Inf_insert $ by simp

@[simp] theorem Inf_eq_top : Inf s = ⊤ ↔ (∀a∈s, a = ⊤) :=
iff.intro
  (assume h a ha, top_unique $ h ▸ Inf_le ha)
  (assume h, top_unique $ le_Inf $ assume a ha, top_le_iff.2 $ h a ha)

end

section

variables [complete_lattice α] {s t : set α} {a b : α}

theorem Sup_inter_le {s t : set α} : Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
by finish
/-
  Sup_le (assume a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/

-- how to state this? instead a parameter `a`, use `∃a, a ∈ s` or `s ≠ ∅`?
theorem Inf_le_Sup (h : a ∈ s) : Inf s ≤ Sup s :=
by have := le_Sup h; finish
--Inf_le_of_le h (le_Sup h)

theorem le_Inf_inter {s t : set α} : Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
by finish
/-
le_Inf (assume a ⟨a_s, a_t⟩, sup_le (Inf_le a_s) (Inf_le a_t))
-/

end

section complete_linear_order
variables [complete_linear_order α] {s t : set α} {a b : α}

lemma Inf_lt_iff : Inf s < b ↔ (∃a∈s, a < b) :=
iff.intro
  (assume : Inf s < b, classical.by_contradiction $ assume : ¬ (∃a∈s, a < b),
    have b ≤ Inf s,
      from le_Inf $ assume a ha, le_of_not_gt $ assume h, this ⟨a, ha, h⟩,
    lt_irrefl b (lt_of_le_of_lt ‹b ≤ Inf s› ‹Inf s < b›))
  (assume ⟨a, ha, h⟩, lt_of_le_of_lt (Inf_le ha) h)

lemma lt_Sup_iff : b < Sup s ↔ (∃a∈s, b < a) :=
iff.intro
  (assume : b < Sup s, classical.by_contradiction $ assume : ¬ (∃a∈s, b < a),
    have Sup s ≤ b,
      from Sup_le $ assume a ha, le_of_not_gt $ assume h, this ⟨a, ha, h⟩,
    lt_irrefl b (lt_of_lt_of_le ‹b < Sup s› ‹Sup s ≤ b›))
  (assume ⟨a, ha, h⟩, lt_of_lt_of_le h $ le_Sup ha)

lemma Sup_eq_top : Sup s = ⊤ ↔ (∀b<⊤, ∃a∈s, b < a) :=
iff.intro
  (assume (h : Sup s = ⊤) b hb, by rwa [←h, lt_Sup_iff] at hb)
  (assume h, top_unique $ le_of_not_gt $ assume h',
    let ⟨a, ha, h⟩ := h _ h' in
    lt_irrefl a $ lt_of_le_of_lt (le_Sup ha) h)

lemma Inf_eq_bot : Inf s = ⊥ ↔ (∀b>⊥, ∃a∈s, a < b) :=
iff.intro
  (assume (h : Inf s = ⊥) b (hb : ⊥ < b), by rwa [←h, Inf_lt_iff] at hb)
  (assume h, bot_unique $ le_of_not_gt $ assume h',
    let ⟨a, ha, h⟩ := h _ h' in
    lt_irrefl a $ lt_of_lt_of_le h (Inf_le ha))

lemma lt_supr_iff {ι : Sort*} {f : ι → α} : a < supr f ↔ (∃i, a < f i) :=
iff.trans lt_Sup_iff $ iff.intro
  (assume ⟨a', ⟨i, rfl⟩, ha⟩, ⟨i, ha⟩)
  (assume ⟨i, hi⟩, ⟨f i, ⟨i, rfl⟩, hi⟩)

lemma infi_lt_iff {ι : Sort*} {f : ι → α} : infi f < a ↔ (∃i, f i < a) :=
iff.trans Inf_lt_iff $ iff.intro
  (assume ⟨a', ⟨i, rfl⟩, ha⟩, ⟨i, ha⟩)
  (assume ⟨i, hi⟩, ⟨f i, ⟨i, rfl⟩, hi⟩)

end complete_linear_order

/- supr & infi -/

section
variables [complete_lattice α] {s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supr (s : ι → α) (i : ι) : s i ≤ supr s :=
le_Sup ⟨i, rfl⟩

@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i ≤ supr s :) :=
le_Sup ⟨i, rfl⟩

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i :) ≤ (: supr s :) :=
le_Sup ⟨i, rfl⟩
-/

theorem le_supr_of_le (i : ι) (h : a ≤ s i) : a ≤ supr s :=
le_trans h (le_supr _ i)

theorem supr_le (h : ∀i, s i ≤ a) : supr s ≤ a :=
Sup_le $ assume b ⟨i, eq⟩, eq ▸ h i

theorem supr_le_supr (h : ∀i, s i ≤ t i) : supr s ≤ supr t :=
supr_le $ assume i, le_supr_of_le i (h i)

theorem supr_le_supr2 {t : ι₂ → α} (h : ∀i, ∃j, s i ≤ t j) : supr s ≤ supr t :=
supr_le $ assume j, exists.elim (h j) le_supr_of_le

theorem supr_le_supr_const (h : ι → ι₂) : (⨆ i:ι, a) ≤ (⨆ j:ι₂, a) :=
supr_le $ le_supr _ ∘ h

@[simp] theorem supr_le_iff : supr s ≤ a ↔ (∀i, s i ≤ a) :=
⟨assume : supr s ≤ a, assume i, le_trans (le_supr _ _) this, supr_le⟩

-- TODO: finish doesn't do well here.
@[congr] theorem supr_congr_Prop {α : Type u} [has_Sup α] {p q : Prop} {f₁ : p → α} {f₂ : q → α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : supr f₁ = supr f₂ :=
begin
  unfold supr,
  apply congr_arg,
  ext,
  simp,
  split,
  exact λ⟨h, W⟩, ⟨pq.1 h, eq.trans (f (pq.1 h)).symm W⟩,
  exact λ⟨h, W⟩, ⟨pq.2 h, eq.trans (f h) W⟩
end

theorem infi_le (s : ι → α) (i : ι) : infi s ≤ s i :=
Inf_le ⟨i, rfl⟩

@[ematch] theorem infi_le' (s : ι → α) (i : ι) : (: infi s ≤ s i :) :=
Inf_le ⟨i, rfl⟩

/- I wanted to see if this would help for infi_comm; it doesn't.
@[ematch] theorem infi_le₂' (s : ι → ι₂ → α) (i : ι) (j : ι₂) : (: ⨅ i j, s i j :) ≤ (: s i j :) :=
begin
  transitivity,
  apply (infi_le (λ i, ⨅ j, s i j) i),
  apply infi_le
end
-/

theorem infi_le_of_le (i : ι) (h : s i ≤ a) : infi s ≤ a :=
le_trans (infi_le _ i) h

theorem le_infi (h : ∀i, a ≤ s i) : a ≤ infi s :=
le_Inf $ assume b ⟨i, eq⟩, eq ▸ h i

theorem infi_le_infi (h : ∀i, s i ≤ t i) : infi s ≤ infi t :=
le_infi $ assume i, infi_le_of_le i (h i)

theorem infi_le_infi2 {t : ι₂ → α} (h : ∀j, ∃i, s i ≤ t j) : infi s ≤ infi t :=
le_infi $ assume j, exists.elim (h j) infi_le_of_le

theorem infi_le_infi_const (h : ι₂ → ι) : (⨅ i:ι, a) ≤ (⨅ j:ι₂, a) :=
le_infi $ infi_le _ ∘ h

@[simp] theorem le_infi_iff : a ≤ infi s ↔ (∀i, a ≤ s i) :=
⟨assume : a ≤ infi s, assume i, le_trans this (infi_le _ _), le_infi⟩

@[congr] theorem infi_congr_Prop {α : Type u} [has_Inf α] {p q : Prop} {f₁ : p → α} {f₂ : q → α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : infi f₁ = infi f₂ :=
begin
  unfold infi,
  apply congr_arg,
  ext,
  simp,
  split,
  exact λ⟨h, W⟩, ⟨pq.1 h, eq.trans (f (pq.1 h)).symm W⟩,
  exact λ⟨h, W⟩, ⟨pq.2 h, eq.trans (f h) W⟩
end

@[simp] theorem infi_const {a : α} : ∀[nonempty ι], (⨅ b:ι, a) = a
| ⟨i⟩ := le_antisymm (Inf_le ⟨i, rfl⟩) (by finish)

@[simp] theorem supr_const {a : α} : ∀[nonempty ι], (⨆ b:ι, a) = a
| ⟨i⟩ := le_antisymm (by finish) (le_Sup ⟨i, rfl⟩)

@[simp] lemma infi_top : (⨅i:ι, ⊤ : α) = ⊤ :=
top_unique $ le_infi $ assume i, le_refl _

@[simp] lemma supr_bot : (⨆i:ι, ⊥ : α) = ⊥ :=
bot_unique $ supr_le $ assume i, le_refl _

@[simp] lemma infi_eq_top : infi s = ⊤ ↔ (∀i, s i = ⊤) :=
iff.intro
  (assume eq i, top_unique $ eq ▸ infi_le _ _)
  (assume h, top_unique $ le_infi $ assume i, top_le_iff.2 $ h i)

@[simp] lemma supr_eq_bot : supr s = ⊥ ↔ (∀i, s i = ⊥) :=
iff.intro
  (assume eq i, bot_unique $ eq ▸ le_supr _ _)
  (assume h, bot_unique $ supr_le $ assume i, le_bot_iff.2 $ h i)

@[simp] lemma infi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
le_antisymm (infi_le _ _) (le_infi $ assume h, le_refl _)

@[simp] lemma infi_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨅ h : p, f h) = ⊤ :=
le_antisymm le_top $ le_infi $ assume h, (hp h).elim

@[simp] lemma supr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
le_antisymm (supr_le $ assume h, le_refl _) (le_supr _ _)

@[simp] lemma supr_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨆ h : p, f h) = ⊥ :=
le_antisymm (supr_le $ assume h, (hp h).elim) bot_le

lemma supr_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨆h:p, a h) = (if h : p then a h else ⊥) :=
by by_cases p; simp [h]

lemma supr_eq_if {p : Prop} [decidable p] (a : α) :
  (⨆h:p, a) = (if p then a else ⊥) :=
by rw [supr_eq_dif, dif_eq_if]

lemma infi_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨅h:p, a h) = (if h : p then a h else ⊤) :=
by by_cases p; simp [h]

lemma infi_eq_if {p : Prop} [decidable p] (a : α) :
  (⨅h:p, a) = (if p then a else ⊤) :=
by rw [infi_eq_dif, dif_eq_if]

-- TODO: should this be @[simp]?
theorem infi_comm {f : ι → ι₂ → α} : (⨅i, ⨅j, f i j) = (⨅j, ⨅i, f i j) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le_of_le j $ infi_le _ i)
  (le_infi $ assume j, le_infi $ assume i, infi_le_of_le i $ infi_le _ j)

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/

-- TODO: should this be @[simp]?
theorem supr_comm {f : ι → ι₂ → α} : (⨆i, ⨆j, f i j) = (⨆j, ⨆i, f i j) :=
le_antisymm
  (supr_le $ assume i, supr_le $ assume j, le_supr_of_le j $ le_supr _ i)
  (supr_le $ assume j, supr_le $ assume i, le_supr_of_le i $ le_supr _ j)

@[simp] theorem infi_infi_eq_left {b : β} {f : Πx:β, x = b → α} : (⨅x, ⨅h:x = b, f x h) = f b rfl :=
le_antisymm
  (infi_le_of_le b $ infi_le _ rfl)
  (le_infi $ assume b', le_infi $ assume eq, match b', eq with ._, rfl := le_refl _ end)

@[simp] theorem infi_infi_eq_right {b : β} {f : Πx:β, b = x → α} : (⨅x, ⨅h:b = x, f x h) = f b rfl :=
le_antisymm
  (infi_le_of_le b $ infi_le _ rfl)
  (le_infi $ assume b', le_infi $ assume eq, match b', eq with ._, rfl := le_refl _ end)

@[simp] theorem supr_supr_eq_left {b : β} {f : Πx:β, x = b → α} : (⨆x, ⨆h : x = b, f x h) = f b rfl :=
le_antisymm
  (supr_le $ assume b', supr_le $ assume eq, match b', eq with ._, rfl := le_refl _ end)
  (le_supr_of_le b $ le_supr _ rfl)

@[simp] theorem supr_supr_eq_right {b : β} {f : Πx:β, b = x → α} : (⨆x, ⨆h : b = x, f x h) = f b rfl :=
le_antisymm
  (supr_le $ assume b', supr_le $ assume eq, match b', eq with ._, rfl := le_refl _ end)
  (le_supr_of_le b $ le_supr _ rfl)

attribute [ematch] le_refl

theorem infi_inf_eq {f g : ι → α} : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ (⨅ x, g x) :=
le_antisymm
  (le_inf
    (le_infi $ assume i, infi_le_of_le i inf_le_left)
    (le_infi $ assume i, infi_le_of_le i inf_le_right))
  (le_infi $ assume i, le_inf
    (inf_le_left_of_le $ infi_le _ _)
    (inf_le_right_of_le $ infi_le _ _))

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/

lemma infi_inf {f : ι → α} {a : α} (i : ι) : (⨅x, f x) ⊓ a = (⨅ x, f x ⊓ a) :=
le_antisymm
  (le_infi $ assume i, le_inf (inf_le_left_of_le $ infi_le _ _) inf_le_right)
  (le_inf (infi_le_infi $ assume i, inf_le_left) (infi_le_of_le i inf_le_right))

lemma inf_infi {f : ι → α} {a : α} (i : ι) : a ⊓ (⨅x, f x) = (⨅ x, a ⊓ f x) :=
by rw [inf_comm, infi_inf i]; simp [inf_comm]

lemma binfi_inf {ι : Sort*} {p : ι → Prop}
  {f : Πi, p i → α} {a : α} {i : ι} (hi : p i) :
  (⨅i (h : p i), f i h) ⊓ a = (⨅ i (h : p i), f i h ⊓ a) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi,
    le_inf (inf_le_left_of_le $ infi_le_of_le i $ infi_le _ _) inf_le_right)
  (le_inf (infi_le_infi $ assume i, infi_le_infi $ assume hi, inf_le_left)
     (infi_le_of_le i $ infi_le_of_le hi $ inf_le_right))

theorem supr_sup_eq {f g : β → α} : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ (⨆ x, g x) :=
le_antisymm
  (supr_le $ assume i, sup_le
    (le_sup_left_of_le $ le_supr _ _)
    (le_sup_right_of_le $ le_supr _ _))
  (sup_le
    (supr_le $ assume i, le_supr_of_le i le_sup_left)
    (supr_le $ assume i, le_supr_of_le i le_sup_right))

/- supr and infi under Prop -/

@[simp] theorem infi_false {s : false → α} : infi s = ⊤ :=
le_antisymm le_top (le_infi $ assume i, false.elim i)

@[simp] theorem supr_false {s : false → α} : supr s = ⊥ :=
le_antisymm (supr_le $ assume i, false.elim i) bot_le

@[simp] theorem infi_true {s : true → α} : infi s = s trivial :=
le_antisymm (infi_le _ _) (le_infi $ assume ⟨⟩, le_refl _)

@[simp] theorem supr_true {s : true → α} : supr s = s trivial :=
le_antisymm (supr_le $ assume ⟨⟩, le_refl _) (le_supr _ _)

@[simp] theorem infi_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = (⨅ i, ⨅ h:p i, f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

@[simp] theorem supr_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = (⨆ i, ⨆ h:p i, f ⟨i, h⟩) :=
le_antisymm
  (supr_le $ assume ⟨i, h⟩, le_supr_of_le i $ le_supr (λh:p i, f ⟨i, h⟩) _)
  (supr_le $ assume i, supr_le $ assume : p i, le_supr _ _)

theorem infi_and {p q : Prop} {s : p ∧ q → α} : infi s = (⨅ h₁ h₂, s ⟨h₁, h₂⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

theorem supr_and {p q : Prop} {s : p ∧ q → α} : supr s = (⨆ h₁ h₂, s ⟨h₁, h₂⟩) :=
le_antisymm
  (supr_le $ assume ⟨i, h⟩, le_supr_of_le i $ le_supr (λj, s ⟨i, j⟩) _)
  (supr_le $ assume i, supr_le $ assume j, le_supr _ _)

theorem infi_or {p q : Prop} {s : p ∨ q → α} :
  infi s = (⨅ h : p, s (or.inl h)) ⊓ (⨅ h : q, s (or.inr h)) :=
le_antisymm
  (le_inf
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩)
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩))
  (le_infi $ assume i, match i with
  | or.inl i := inf_le_left_of_le $ infi_le _ _
  | or.inr j := inf_le_right_of_le $ infi_le _ _
  end)

theorem supr_or {p q : Prop} {s : p ∨ q → α} :
  (⨆ x, s x) = (⨆ i, s (or.inl i)) ⊔ (⨆ j, s (or.inr j)) :=
le_antisymm
  (supr_le $ assume s, match s with
  | or.inl i := le_sup_left_of_le $ le_supr _ i
  | or.inr j := le_sup_right_of_le $ le_supr _ j
  end)
  (sup_le
    (supr_le_supr2 $ assume i, ⟨or.inl i, le_refl _⟩)
    (supr_le_supr2 $ assume j, ⟨or.inr j, le_refl _⟩))

theorem Inf_eq_infi {s : set α} : Inf s = (⨅a ∈ s, a) :=
le_antisymm
  (le_infi $ assume b, le_infi $ assume h, Inf_le h)
  (le_Inf $ assume b h, infi_le_of_le b $ infi_le _ h)

theorem Sup_eq_supr {s : set α} : Sup s = (⨆a ∈ s, a) :=
le_antisymm
  (Sup_le $ assume b h, le_supr_of_le b $ le_supr _ h)
  (supr_le $ assume b, supr_le $ assume h, le_Sup h)

lemma Sup_range {α : Type u} [has_Sup α] {f : ι → α} : Sup (range f) = supr f := rfl

lemma Inf_range {α : Type u} [has_Inf α] {f : ι → α} : Inf (range f) = infi f := rfl

lemma supr_range {g : β → α} {f : ι → β} : (⨆b∈range f, g b) = (⨆i, g (f i)) :=
le_antisymm
  (supr_le $ assume b, supr_le $ assume ⟨i, (h : f i = b)⟩, h ▸ le_supr _ i)
  (supr_le $ assume i, le_supr_of_le (f i) $ le_supr (λp, g (f i)) (mem_range_self _))

lemma infi_range {g : β → α} {f : ι → β} : (⨅b∈range f, g b) = (⨅i, g (f i)) :=
le_antisymm
  (le_infi $ assume i, infi_le_of_le (f i) $ infi_le (λp, g (f i)) (mem_range_self _))
  (le_infi $ assume b, le_infi $ assume ⟨i, (h : f i = b)⟩, h ▸ infi_le _ i)

theorem Inf_image {s : set β} {f : β → α} : Inf (f '' s) = (⨅ a ∈ s, f a) :=
calc Inf (set.image f s) = (⨅a, ⨅h : ∃b, b ∈ s ∧ f b = a, a) : Inf_eq_infi
                     ... = (⨅a, ⨅b, ⨅h : f b = a ∧ b ∈ s, a) : by simp [and_comm]
                     ... = (⨅a, ⨅b, ⨅h : a = f b, ⨅h : b ∈ s, a) : by simp [infi_and, eq_comm]
                     ... = (⨅b, ⨅a, ⨅h : a = f b, ⨅h : b ∈ s, a) : by rw [infi_comm]
                     ... = (⨅a∈s, f a) : congr_arg infi $ by funext x; rw [infi_infi_eq_left]

theorem Sup_image {s : set β} {f : β → α} : Sup (f '' s) = (⨆ a ∈ s, f a) :=
calc Sup (set.image f s) = (⨆a, ⨆h : ∃b, b ∈ s ∧ f b = a, a) : Sup_eq_supr
                     ... = (⨆a, ⨆b, ⨆h : f b = a ∧ b ∈ s, a) : by simp [and_comm]
                     ... = (⨆a, ⨆b, ⨆h : a = f b, ⨆h : b ∈ s, a) : by simp [supr_and, eq_comm]
                     ... = (⨆b, ⨆a, ⨆h : a = f b, ⨆h : b ∈ s, a) : by rw [supr_comm]
                     ... = (⨆a∈s, f a) : congr_arg supr $ by funext x; rw [supr_supr_eq_left]

/- supr and infi under set constructions -/

/- should work using the simplifier! -/
@[simp] theorem infi_emptyset {f : β → α} : (⨅ x ∈ (∅ : set β), f x) = ⊤ :=
le_antisymm le_top (le_infi $ assume x, le_infi false.elim)

@[simp] theorem supr_emptyset {f : β → α} : (⨆ x ∈ (∅ : set β), f x) = ⊥ :=
le_antisymm (supr_le $ assume x, supr_le false.elim) bot_le

@[simp] theorem infi_univ {f : β → α} : (⨅ x ∈ (univ : set β), f x) = (⨅ x, f x) :=
show (⨅ (x : β) (H : true), f x) = ⨅ (x : β), f x,
  from congr_arg infi $ funext $ assume x, infi_const

@[simp] theorem supr_univ {f : β → α} : (⨆ x ∈ (univ : set β), f x) = (⨆ x, f x) :=
show (⨆ (x : β) (H : true), f x) = ⨆ (x : β), f x,
  from congr_arg supr $ funext $ assume x, supr_const

@[simp] theorem infi_union {f : β → α} {s t : set β} : (⨅ x ∈ s ∪ t, f x) = (⨅x∈s, f x) ⊓ (⨅x∈t, f x) :=
calc (⨅ x ∈ s ∪ t, f x) = (⨅ x, (⨅h : x∈s, f x) ⊓ (⨅h : x∈t, f x)) : congr_arg infi $ funext $ assume x, infi_or
                    ... = (⨅x∈s, f x) ⊓ (⨅x∈t, f x) : infi_inf_eq

theorem infi_le_infi_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨅ x ∈ t, f x) ≤ (⨅ x ∈ s, f x) :=
by rw [(union_eq_self_of_subset_left h).symm, infi_union]; exact inf_le_left

@[simp] theorem supr_union {f : β → α} {s t : set β} : (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
calc (⨆ x ∈ s ∪ t, f x) = (⨆ x, (⨆h : x∈s, f x) ⊔ (⨆h : x∈t, f x)) : congr_arg supr $ funext $ assume x, supr_or
                    ... = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) : supr_sup_eq

theorem supr_le_supr_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨆ x ∈ s, f x) ≤ (⨆ x ∈ t, f x) :=
by rw [(union_eq_self_of_subset_left h).symm, supr_union]; exact le_sup_left

@[simp] theorem insert_of_has_insert {α : Type*} (x : α) (a : set α) :
  has_insert.insert x a = insert x a := rfl

@[simp] theorem infi_insert {f : β → α} {s : set β} {b : β} : (⨅ x ∈ insert b s, f x) = f b ⊓ (⨅x∈s, f x) :=
eq.trans infi_union $ congr_arg (λx:α, x ⊓ (⨅x∈s, f x)) infi_infi_eq_left

@[simp] theorem supr_insert {f : β → α} {s : set β} {b : β} : (⨆ x ∈ insert b s, f x) = f b ⊔ (⨆x∈s, f x) :=
eq.trans supr_union $ congr_arg (λx:α, x ⊔ (⨆x∈s, f x)) supr_supr_eq_left

@[simp] theorem infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : set β), f x) = f b :=
show (⨅ x ∈ insert b (∅ : set β), f x) = f b,
  by simp

@[simp] theorem infi_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : set β), f x) = f a ⊓ f b :=
by { rw [show {a, b} = (insert b {a} : set β), from rfl, infi_insert, inf_comm], simp }

@[simp] theorem supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : set β), f x) = f b :=
show (⨆ x ∈ insert b (∅ : set β), f x) = f b,
  by simp

@[simp] theorem supr_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : set β), f x) = f a ⊔ f b :=
by { rw [show {a, b} = (insert b {a} : set β), from rfl, supr_insert, sup_comm], simp }

lemma infi_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨅ c ∈ f '' t, g c) = (⨅ b ∈ t, g (f b)) :=
le_antisymm
  (le_infi $ assume b, le_infi $ assume hbt,
    infi_le_of_le (f b) $ infi_le (λ_, g (f b)) (mem_image_of_mem f hbt))
  (le_infi $ assume c, le_infi $ assume ⟨b, hbt, eq⟩,
    eq ▸ infi_le_of_le b $ infi_le (λ_, g (f b)) hbt)

lemma supr_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨆ c ∈ f '' t, g c) = (⨆ b ∈ t, g (f b)) :=
le_antisymm
  (supr_le $ assume c, supr_le $ assume ⟨b, hbt, eq⟩,
    eq ▸ le_supr_of_le b $ le_supr (λ_, g (f b)) hbt)
  (supr_le $ assume b, supr_le $ assume hbt,
    le_supr_of_le (f b) $ le_supr (λ_, g (f b)) (mem_image_of_mem f hbt))

/- supr and infi under Type -/

@[simp] theorem infi_empty {s : empty → α} : infi s = ⊤ :=
le_antisymm le_top (le_infi $ assume i, empty.rec_on _ i)

@[simp] theorem supr_empty {s : empty → α} : supr s = ⊥ :=
le_antisymm (supr_le $ assume i, empty.rec_on _ i) bot_le

@[simp] theorem infi_unit {f : unit → α} : (⨅ x, f x) = f () :=
le_antisymm (infi_le _ _) (le_infi $ assume ⟨⟩, le_refl _)

@[simp] theorem supr_unit {f : unit → α} : (⨆ x, f x) = f () :=
le_antisymm (supr_le $ assume ⟨⟩, le_refl _) (le_supr _ _)

lemma supr_bool_eq {f : bool → α} : (⨆b:bool, f b) = f tt ⊔ f ff :=
le_antisymm
  (supr_le $ assume b, match b with tt := le_sup_left | ff := le_sup_right end)
  (sup_le (le_supr _ _) (le_supr _ _))

lemma infi_bool_eq {f : bool → α} : (⨅b:bool, f b) = f tt ⊓ f ff :=
le_antisymm
  (le_inf (infi_le _ _) (infi_le _ _))
  (le_infi $ assume b, match b with tt := inf_le_left | ff := inf_le_right end)

theorem infi_subtype {p : ι → Prop} {f : subtype p → α} : (⨅ x, f x) = (⨅ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

lemma infi_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
  (⨅ i (h : p i), f i h) = (⨅ x : subtype p, f x.val x.property) :=
(@infi_subtype _ _ _ p (λ x, f x.val x.property)).symm

theorem supr_subtype {p : ι → Prop} {f : subtype p → α} : (⨆ x, f x) = (⨆ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (supr_le $ assume ⟨i, h⟩, le_supr_of_le i $ le_supr (λh:p i, f ⟨i, h⟩) _)
  (supr_le $ assume i, supr_le $ assume : p i, le_supr _ _)

theorem infi_sigma {p : β → Type w} {f : sigma p → α} : (⨅ x, f x) = (⨅ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

theorem supr_sigma {p : β → Type w} {f : sigma p → α} : (⨆ x, f x) = (⨆ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (supr_le $ assume ⟨i, h⟩, le_supr_of_le i $ le_supr (λh:p i, f ⟨i, h⟩) _)
  (supr_le $ assume i, supr_le $ assume : p i, le_supr _ _)

theorem infi_prod {γ : Type w} {f : β × γ → α} : (⨅ x, f x) = (⨅ i j, f (i, j)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

theorem supr_prod {γ : Type w} {f : β × γ → α} : (⨆ x, f x) = (⨆ i j, f (i, j)) :=
le_antisymm
  (supr_le $ assume ⟨i, h⟩, le_supr_of_le i $ le_supr (λj, f ⟨i, j⟩) _)
  (supr_le $ assume i, supr_le $ assume j, le_supr _ _)

theorem infi_sum {γ : Type w} {f : β ⊕ γ → α} :
  (⨅ x, f x) = (⨅ i, f (sum.inl i)) ⊓ (⨅ j, f (sum.inr j)) :=
le_antisymm
  (le_inf
    (infi_le_infi2 $ assume i, ⟨_, le_refl _⟩)
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩))
  (le_infi $ assume s, match s with
  | sum.inl i := inf_le_left_of_le $ infi_le _ _
  | sum.inr j := inf_le_right_of_le $ infi_le _ _
  end)

theorem supr_sum {γ : Type w} {f : β ⊕ γ → α} :
  (⨆ x, f x) = (⨆ i, f (sum.inl i)) ⊔ (⨆ j, f (sum.inr j)) :=
le_antisymm
  (supr_le $ assume s, match s with
  | sum.inl i := le_sup_left_of_le $ le_supr _ i
  | sum.inr j := le_sup_right_of_le $ le_supr _ j
  end)
  (sup_le
    (supr_le_supr2 $ assume i, ⟨sum.inl i, le_refl _⟩)
    (supr_le_supr2 $ assume j, ⟨sum.inr j, le_refl _⟩))

end

section complete_linear_order
variables [complete_linear_order α]

lemma supr_eq_top (f : ι → α) : supr f = ⊤ ↔ (∀b<⊤, ∃i, b < f i) :=
by rw [← Sup_range, Sup_eq_top];
from forall_congr (assume b, forall_congr (assume hb, set.exists_range_iff))

lemma infi_eq_bot (f : ι → α) : infi f = ⊥ ↔ (∀b>⊥, ∃i, b > f i) :=
by rw [← Inf_range, Inf_eq_bot];
from forall_congr (assume b, forall_congr (assume hb, set.exists_range_iff))

end complete_linear_order

/- Instances -/

instance complete_lattice_Prop : complete_lattice Prop :=
{ Sup    := λs, ∃a∈s, a,
  le_Sup := assume s a h p, ⟨a, h, p⟩,
  Sup_le := assume s a h ⟨b, h', p⟩, h b h' p,
  Inf    := λs, ∀a:Prop, a∈s → a,
  Inf_le := assume s a h p, p a h,
  le_Inf := assume s a h p b hb, h b hb p,
  ..lattice.bounded_lattice_Prop }

lemma Inf_Prop_eq {s : set Prop} : Inf s = (∀p ∈ s, p) := rfl

lemma Sup_Prop_eq {s : set Prop} : Sup s = (∃p ∈ s, p) := rfl

lemma infi_Prop_eq {ι : Sort*} {p : ι → Prop} : (⨅i, p i) = (∀i, p i) :=
le_antisymm (assume h i, h _ ⟨i, rfl⟩ ) (assume h p ⟨i, eq⟩, eq ▸ h i)

lemma supr_Prop_eq {ι : Sort*} {p : ι → Prop} : (⨆i, p i) = (∃i, p i) :=
le_antisymm (assume ⟨q, ⟨i, (eq : p i = q)⟩, hq⟩, ⟨i, eq.symm ▸ hq⟩) (assume ⟨i, hi⟩, ⟨p i, ⟨i, rfl⟩, hi⟩)

instance pi.complete_lattice {α : Type u} {β : α → Type v} [∀ i, complete_lattice (β i)] :
  complete_lattice (Π i, β i) :=
by { pi_instance;
     { intros, intro,
       apply_field, intros,
       simp at H, rcases H with ⟨ x, H₀, H₁ ⟩,
       subst b, apply a_1 _ H₀ i, } }

lemma Inf_apply
  {α : Type u} {β : α → Type v} [∀ i, complete_lattice (β i)] {s : set (Πa, β a)} {a : α} :
  (Inf s) a = (⨅f∈s, (f : Πa, β a) a) :=
by rw [← Inf_image]; refl

lemma infi_apply {α : Type u} {β : α → Type v} {ι : Sort*} [∀ i, complete_lattice (β i)]
  {f : ι → Πa, β a} {a : α} : (⨅i, f i) a = (⨅i, f i a) :=
by erw [← Inf_range, Inf_apply, infi_range]

lemma Sup_apply
  {α : Type u} {β : α → Type v} [∀ i, complete_lattice (β i)] {s : set (Πa, β a)} {a : α} :
  (Sup s) a = (⨆f∈s, (f : Πa, β a) a) :=
by rw [← Sup_image]; refl

lemma supr_apply {α : Type u} {β : α → Type v} {ι : Sort*} [∀ i, complete_lattice (β i)]
  {f : ι → Πa, β a} {a : α} : (⨆i, f i) a = (⨆i, f i a) :=
by erw [← Sup_range, Sup_apply, supr_range]

section complete_lattice
variables [preorder α] [complete_lattice β]

theorem monotone_Sup_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Sup s) :=
assume x y h, Sup_le $ assume x' ⟨f, f_in, fx_eq⟩, le_Sup_of_le ⟨f, f_in, rfl⟩ $ fx_eq ▸ m_s _ f_in h

theorem monotone_Inf_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Inf s) :=
assume x y h, le_Inf $ assume x' ⟨f, f_in, fx_eq⟩, Inf_le_of_le ⟨f, f_in, rfl⟩ $ fx_eq ▸ m_s _ f_in h

end complete_lattice

section ord_continuous
open lattice
variables [complete_lattice α] [complete_lattice β]

/-- A function `f` between complete lattices is order-continuous
  if it preserves all suprema. -/
def ord_continuous (f : α → β) := ∀s : set α, f (Sup s) = (⨆i∈s, f i)

lemma ord_continuous_sup {f : α → β} {a₁ a₂ : α} (hf : ord_continuous f) : f (a₁ ⊔ a₂) = f a₁ ⊔ f a₂ :=
have h : f (Sup {a₁, a₂}) = (⨆i∈({a₁, a₂} : set α), f i), from hf _,
have h₁ : {a₁, a₂} = (insert a₂ {a₁} : set α), from rfl,
begin
  rw [h₁, Sup_insert, Sup_singleton, sup_comm] at h,
  rw [h, supr_insert, supr_singleton, sup_comm]
end

lemma ord_continuous_mono {f : α → β} (hf : ord_continuous f) : monotone f :=
assume a₁ a₂ h,
calc f a₁ ≤ f a₁ ⊔ f a₂ : le_sup_left
  ... = f (a₁ ⊔ a₂) : (ord_continuous_sup hf).symm
  ... = _ : by rw [sup_of_le_right h]

end ord_continuous
end lattice

namespace order_dual
open lattice
variable (α : Type*)

instance [has_Inf α] : has_Sup (order_dual α) := ⟨(Inf : set α → α)⟩
instance [has_Sup α] : has_Inf (order_dual α) := ⟨(Sup : set α → α)⟩

instance [complete_semilattice_sup α] : complete_semilattice_inf (order_dual α) :=
{ Inf_le := @complete_semilattice_sup.le_Sup α _,
  le_Inf := @complete_semilattice_sup.Sup_le α _,
  bot_le := by lattice.prove_default_bounds,
  le_top := by lattice.prove_default_bounds,
  .. order_dual.lattice.semilattice_inf _,
  .. order_dual.lattice.has_Inf _ }

instance [complete_semilattice_inf α] : complete_semilattice_sup (order_dual α) :=
{ le_Sup := @complete_semilattice_inf.Inf_le α _,
  Sup_le := @complete_semilattice_inf.le_Inf α _,
  bot_le := by lattice.prove_default_bounds,
  le_top := by lattice.prove_default_bounds,
  .. order_dual.lattice.semilattice_sup _,
  .. order_dual.lattice.has_Sup _ }

instance [complete_lattice α] : complete_lattice (order_dual α) :=
{ .. order_dual.lattice.complete_semilattice_sup α,
  .. order_dual.lattice.complete_semilattice_inf α,
  .. order_dual.lattice.bounded_lattice α }

instance [complete_linear_order α] : complete_linear_order (order_dual α) :=
{ .. order_dual.lattice.complete_lattice α, .. order_dual.decidable_linear_order α }

end order_dual

namespace prod
open lattice
variables (α : Type*) (β : Type*)

instance [has_Inf α] [has_Inf β] : has_Inf (α × β) :=
⟨λs, (Inf (prod.fst '' s), Inf (prod.snd '' s))⟩

instance [has_Sup α] [has_Sup β] : has_Sup (α × β) :=
⟨λs, (Sup (prod.fst '' s), Sup (prod.snd '' s))⟩

instance [complete_semilattice_sup α] [complete_semilattice_sup β] : complete_semilattice_sup (α × β) :=
{ le_Sup := assume s p hab, ⟨complete_semilattice_sup.le_Sup _ _ $ mem_image_of_mem prod.fst hab,
                             complete_semilattice_sup.le_Sup _ _ $ mem_image_of_mem prod.snd hab⟩,
  Sup_le := assume s p h,
    ⟨ complete_semilattice_sup.Sup_le _ _ $ ball_image_of_ball $ assume p hp, (h p hp).1,
      complete_semilattice_sup.Sup_le _ _ $ ball_image_of_ball $ assume p hp, (h p hp).2⟩,
  bot_le := λ a, ⟨bot_le,bot_le⟩,
  le_top := λ a, ⟨le_top,le_top⟩,
  .. prod.lattice.has_bot α β,
  .. prod.lattice.has_top α β,
  .. prod.lattice.has_Sup α β,
  .. prod.lattice.semilattice_sup α β,
  }

instance [complete_semilattice_inf α] [complete_semilattice_inf β] : complete_semilattice_inf (α × β) :=
{ Inf_le := assume s p hab, ⟨complete_semilattice_inf.Inf_le _ _ $ mem_image_of_mem prod.fst hab,
                             complete_semilattice_inf.Inf_le _ _ $ mem_image_of_mem prod.snd hab⟩,
  le_Inf := assume s p h,
    ⟨ complete_semilattice_inf.le_Inf _ _ $ ball_image_of_ball $ assume p hp, (h p hp).1,
      complete_semilattice_inf.le_Inf _ _ $ ball_image_of_ball $ assume p hp, (h p hp).2⟩,
  bot_le := λ a, ⟨bot_le,bot_le⟩,
  le_top := λ a, ⟨le_top,le_top⟩,
  .. prod.lattice.has_bot α β,
  .. prod.lattice.has_top α β,
  .. prod.lattice.semilattice_inf α β,
  .. prod.lattice.has_Inf α β }

instance [complete_lattice α] [complete_lattice β] : complete_lattice (α × β) :=
{ .. prod.lattice.complete_semilattice_inf α β,
  .. prod.lattice.complete_semilattice_sup α β,
  .. prod.lattice.bounded_lattice α β }

end prod
