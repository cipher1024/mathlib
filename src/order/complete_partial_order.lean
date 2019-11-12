/- complete partial orders
Helpful for a small-scale domain theory, see
  http://home.in.tum.de/~hoelzl/documents/lochbihler2014recursive.pdf
-/

import data.pfun
import data.seq.seq
import data.seq.wseq
import data.stream.basic
import tactic.wlog
import order.monotone
import tactic.equations
import tactic

universes u v

local attribute [instance, priority 0] classical.prop_decidable

/- Chains (monotonically increasing sequences) -/

structure chain (α : Type u) [preorder α] :=
(elems : stream α)
(mono : monotone elems)

namespace stream

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

variables {f : α → β} (hf : monotone f)
          {s : stream α} (hs : monotone s)

lemma monotone_map : monotone (s.map f) :=
λ i j h, hf (hs h)

end stream

namespace chain

variables {α : Type u} {β : Type v} {γ : Type*}
variables [preorder α] [preorder β] [preorder γ]

instance : has_mem α (chain α) :=
⟨λa c, a ∈ c.elems⟩

@[simp] lemma mem_mk (x : α) (s : stream α) (h) : x ∈ chain.mk s h ↔ x ∈ s := iff.refl _

def nth (i : ℕ) (c : chain α) : α := c.elems.nth i

def const (x : α) : chain α := ⟨stream.const x, λ i j h, le_refl _⟩

@[simp] lemma nth_mk (i : ℕ) (s : stream α) (h) : (chain.mk s h).nth i = s.nth i := rfl

@[simp] lemma mem_const (x y : α) : x ∈ const y ↔ x = y :=
⟨λ ⟨i,h⟩, h, λ h, ⟨0, h⟩⟩

variables (c c' : chain α)
  (f : α →ₘ β) (g : β →ₘ γ)

instance : preorder (chain α) :=
{ le := λ x y, ∀ a, a ∈ x → ∃ b ∈ y, a ≤ b,
  le_trans := λ a b c h₀ h₁ x hx,
    Exists.rec_on (h₀ _ hx) $ λ w hw,
    Exists.rec_on (h₁ _ hw.fst) $ λ y hy,
    ⟨_,hy.fst,le_trans hw.snd hy.snd⟩,
  le_refl := λ a x hx, ⟨_,hx,le_refl _⟩ }

@[ext]
lemma ext (h : ∀ i, c.nth i = c'.nth i) : c = c' :=
by cases c; cases c'; congr; ext; apply h

def map : chain β :=
⟨c.elems.map f, stream.monotone_map f.mono c.mono ⟩

def attach (c : chain α) : chain { x // x ∈ c } :=
⟨λ i, ⟨c.elems i,i,rfl⟩, λ a b h, c.mono h⟩

-- variables {f}

lemma mem_def (x : α) (c : chain α) : x ∈ c ↔ ∃ i, x = c.nth i := iff.refl _

@[simp] lemma map_const (x : α) : (const x).map f = const (f x) := rfl

@[simp] lemma elems_map (c : chain α) : (c.map f).elems = c.elems.map f := rfl

lemma mem_map (x : α) : x ∈ c → f x ∈ chain.map c f :=
stream.mem_map _

lemma map_const' (x : β) : c.map (Mono.const x) = const x := rfl

lemma map_eq_attach_map : c.map f = c.attach.map (f ∘ ⟨subtype.val⟩) :=
by cases c; refl

lemma exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
stream.exists_of_mem_map

lemma mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
⟨ exists_of_mem_map _ _, λ h, by { rcases h with ⟨w,h,h'⟩, subst b, apply mem_map c f _ h, } ⟩

lemma const_le_of_mem (x : α) (c : chain α) (hx : x ∈ c) : const x ≤ c :=
λ a ha, ⟨_,hx,le_of_eq $ (mem_const _ _).mp ha⟩

lemma chain_map_le (c' : chain β) (h : ∀ a, a ∈ c → f a ∈ c') : chain.map c f ≤ c' :=
begin
  intros b hb,
  rcases exists_of_mem_map _ f hb with ⟨a,h₀,h₁⟩,
  subst b, existsi [f a,h _ h₀], refl
end

lemma le_chain_map (c' : chain β) (h : ∀ b, b ∈ c' → ∃ a, b ≤ f a ∧ a ∈ c) : c' ≤ chain.map c f :=
begin
  intros b hb,
  replace h := h _ hb, rcases h with ⟨a,h₀,h₁⟩,
  exact ⟨f a,mem_map _ f _ h₁,h₀⟩
end

lemma map_le_map_of_exists (g : α →ₘ β) (h : ∀ a ∈ c, ∃ b ∈ c, f a ≤ g b) : c.map f ≤ c.map g :=
begin
  intros a ha,
  replace ha := exists_of_mem_map _ _ ha,
  rcases ha with ⟨a',ha₀,ha₁⟩,
  specialize h _ ha₀, rcases h with ⟨b,ha,hb⟩,
  existsi [g b, mem_map _ g _ ha],
  refine ha₁ ▸ hb,
end

lemma map_le_map (g : α →ₘ β) (h : ∀ a ∈ c, f a ≤ g a) : c.map f ≤ c.map g :=
map_le_map_of_exists _ _ _ $ λ a ha, ⟨a,ha,h _ ha⟩

@[simp] lemma nth_map (i : ℕ) : nth i (c.map f) = f (nth i c) := rfl
open Mono

@[simp] lemma nth_mem (i : ℕ) : nth i c ∈ c := ⟨i,rfl⟩

open Mono

lemma map_id : c.map id = c :=
by cases c; refl

lemma map_comp : (c.map f).map g = c.map (g ∘ f) := rfl

lemma le_total_of_mem_of_mem {x y : α} (h : x ∈ c) (h' : y ∈ c) : x ≤ y ∨ y ≤ x :=
begin
  cases c, simp [stream.mem_def] at h h',
  cases h with i h, cases h' with j h',
  wlog : i ≤ j := le_total i j using [x y i j,y x j i],
  subst h, subst h', left, apply c_mono case,
end

end chain

section monotone

variables {α : Type u} {β : Type v} {γ : Type*} {ω : Type*}

variables [preorder α] [preorder β] [preorder γ] [preorder ω]

open function

instance monotone_map_of_monotone (c : chain β) (f : α → β →ₘ γ) [hf : is_monotone f] :
  is_monotone (λ x, c.map (f x)) :=
⟨ λ a b h, chain.map_le_map  _ _ _ $ λ x hx, hf.mono h x ⟩

-- lemma monotone_map_map_of_monotone {g : α → γ → ω} (hg : monotone (uncurry g)) (c : chain β) :
--   monotone (λ x, (c.map (f x) (monotone_of_monotone_uncurry' hf _)).map (g x) (monotone_of_monotone_uncurry' hg _)) :=
-- by simp only [chain.map_comp]; exact monotone_map_of_monotone (monotone_uncurry_comp' hg hf) c

end monotone

/- CPOs (complete partial orders) -/
class complete_partial_order (α : Type*) extends partial_order α :=
(Sup     : chain α → α)
(le_Sup'  : ∀(c:chain α), ∀i, c.nth i ≤ Sup c)
(Sup_le'  : ∀(c:chain α) x, (∀i, c.nth i ≤ x) → Sup c ≤ x)

namespace complete_partial_order

variables {α : Type u} {β : Type v} {γ : Type*} {ω : Type*}
variables [complete_partial_order α]

export lattice.order_bot (bot_le)

lemma le_Sup (c : chain α) : ∀ (x ∈ c), x ≤ Sup c | x ⟨i,h⟩ := h.symm ▸ le_Sup' c i

lemma Sup_le (c : chain α) (x : α) (h : ∀y∈c, y ≤ x) : Sup c ≤ x :=
Sup_le' c _ $ λ i, h _ ⟨i,rfl⟩

lemma le_Sup_of_le {c : chain α} {x : α} (y : α) (h : x ≤ y) (hy : y ∈ c) : x ≤ Sup c :=
le_trans h (le_Sup c y hy)

lemma Sup_total {c : chain α} {x : α} (h : ∀y∈c, y ≤ x ∨ x ≤ y) : Sup c ≤ x ∨ x ≤ Sup c :=
classical.by_cases
  (assume : ∀y ∈ c, y ≤ x, or.inl (Sup_le _ _ this))
  (assume : ¬ ∀y ∈ c, y ≤ x,
    have ∃y∈c, ¬ y ≤ x,
      by simp only [not_forall] at this ⊢; assumption,
    let ⟨y, hy, hyx⟩ := this in
    have x ≤ y, from (h y hy).resolve_left hyx,
    or.inr $ le_Sup_of_le _ this hy)

lemma Sup_le_Sup_of_le {c₀ c₁ : chain α} (h : c₀ ≤ c₁) : Sup c₀ ≤ Sup c₁ :=
Sup_le _ _ $
λ y hy, Exists.rec_on (h y hy) $
λ x ⟨hx,hxy⟩, le_trans hxy $ le_Sup _ _ hx

lemma Sup_le_iff (c : chain α) (x : α) : Sup c ≤ x ↔ (∀ y ∈ c, y ≤ x) :=
begin
  split; intros,
  { transitivity Sup c,
    apply le_Sup _ _ H, exact a },
  apply Sup_le _ _ a,
end

@[simp] lemma Sup_const (x : α) : Sup (chain.const x) = x :=
le_antisymm
  (Sup_le _ _ $ by simp)
  (le_Sup _ _ $ by simp)

/--
Note: The reverse, `f (Sup c) ≤ Sup (c.map _ hf)` would imply the continuity of `f`
-/
lemma Sup_le_map_of_monotone [complete_partial_order β] (f : α →ₘ β) (c : chain α) :
  Sup (c.map f) ≤ f (Sup c) :=
begin
  apply Sup_le, intros y hy,
  rcases chain.exists_of_mem_map _ _ hy with ⟨w,h₀,h₁⟩,
  rw ← h₁, apply f.mono, apply le_Sup _ _ h₀,
end

section monotone

variables [preorder β]

lemma monotone_Sup (f : β → chain α) (hf : monotone f) : monotone (λ x, Sup (f x)) :=
λ a b h, Sup_le_Sup_of_le (hf h)

instance (f : β → chain α) [hf : is_monotone f] : is_monotone (λ x, Sup (f x)) :=
⟨ monotone_Sup _ hf.mono ⟩

end monotone

section continuity
open chain

variables [complete_partial_order β]
          [complete_partial_order γ]
  (g : β →ₘ γ)
  (f : α →ₘ β)

def continuous :=
∀ C : chain α, f (Sup C) = Sup (C.map f)

def continuous' (f : α → β) := ∃ h, continuous (Mono.mk f h)

lemma continuous_comp (hgc : continuous g) (hfc : continuous f) :
  continuous (g ∘ f) :=
begin
  dsimp [continuous] at *, intro,
  rw [hfc,hgc,chain.map_comp]
end

@[simp]
lemma continuous_id : continuous (@Mono.id α _) :=
λ c, show Sup _ = Sup _, from congr_arg _ (map_id c).symm

-- lemma continuous_comp' (hg : continuous' g) (hf : continuous' f) : continuous' (g ∘ f) :=
-- ⟨_, continuous_comp _ _ _ _ hg.snd hf.snd⟩

end continuity

end complete_partial_order

-- namespace subtype

-- variables {α : Type*} {p : α → Prop}

-- instance : complete_partial_order (subtype p) := _

-- lemma subtype.continuous_val {p : α → Prop} : continuous (Mono.val p) := _

-- end subtype

namespace discrete

def partial_order (α) : partial_order α :=
{ le := eq,
  le_refl := @rfl _,
  le_trans := @eq.trans _,
  le_antisymm := λ x y h _, h }

local attribute [instance, priority 0] discrete.partial_order

def complete_partial_order (α : Type*) : complete_partial_order α :=
{ Sup := λ c, @chain.nth α _ 0 c,
  le_Sup' := λ c i, eq.symm $ c.mono $ zero_le _,
  Sup_le' := λ c x h, h _ }

open complete_partial_order

lemma monotone_of {α β} (f : α → β) : α →ₘ β :=
Mono.mk f $ λ a b h, congr_arg _ h

local attribute [instance, priority 0] discrete.complete_partial_order

lemma const_chain_rec {α} (β : chain α → Sort*) (h : Π x, β (chain.const x)) : Π c, β c :=
λ c, eq.mp
  (congr_arg _ $ chain.ext _ _ $
    λ i, show chain.nth i (chain.const (chain.nth 0 c)) = chain.nth i c, from
         suffices chain.nth 0 c = chain.nth i c, by simpa,
         c.mono (zero_le _))
  (h $ c.nth 0)

lemma continuous_of {α β} (f : α →ₘ β) : continuous f :=
const_chain_rec _ $ by simp

end discrete

namespace stream

variables {α : Type*} {β : Type*}

def attach (s : stream α) : stream { x : α // x ∈ s } :=
λ i, ⟨s i, i, rfl⟩

@[simp]
lemma val_nth_attach (s : stream α) (i : ℕ) : (s.attach.nth i).val = s.nth i :=
rfl

@[simp]
lemma map_attach (s : stream α) (f : α → β) : s.attach.map (λ x, f x.val) = s.map f :=
funext $ λ i, rfl

@[simp]
lemma mem_attach {s : stream α} : Π (x : { x : α // x ∈ s }), x ∈ s.attach
| ⟨x, i, h⟩ := ⟨i,by { dsimp [attach,nth], congr, exact h } ⟩

-- @[simp]
-- lemma mem_attach_iff {s : stream α} (x : { x : α // x ∈ s }) : x ∈ s.attach ↔ x.1 ∈ s :=
-- sorry

end stream


namespace option

variables {α : Type u} {β : Type v} {γ : Type*}
open lattice (has_bot order_bot)
open complete_partial_order
-- local attribute [instance, priority 0] discrete.partial_order

variables [complete_partial_order α]

-- lemma eq_of_chain {c : chain (with_bot α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
-- begin
--   have ha' := ha, have hb' := hb,
--   cases ha with i ha, replace ha := ha.symm,
--   cases hb with j hb, replace hb := hb.symm,
--   wlog h : i ≤ j := le_total i j using [a b i j,b a j i],
--   -- have H := c.mono h a,
--   rcases c.mono h a ha with ⟨a', H, H'⟩,
--   rw ← option.mem_def at hb,
--   have := mem_unique H hb,

-- apply mem_unique H,
-- end

lemma d {c : chain (with_bot α)} {h : ∃ (i : ℕ), ↥(is_some (chain.nth i c))}
  (x : { val : with_bot α // val ∈ stream.drop (classical.some h) (c.elems)}) :
  x.val.is_some :=
begin
  have ha := x.property,
  have hb := classical.some_spec h,
  rw is_some_iff_exists at hb ⊢,
  cases hb with a hb,
  rw stream.mem_def at ha,
  cases ha with i ha,
  have := c.mono (nat.le_add_left (classical.some h) i) _ hb,
  rcases this with ⟨b,hh,hh'⟩,
  existsi b, rw option.mem_def at hh,
  rw [← hh,ha], refl
end

lemma f (s : stream α) (i : ℕ) : s i = s.nth i := rfl

lemma le_of_some_le_some {x y : α} (h : ((≤) : with_bot α → with_bot α → Prop) (some x) (some y)) : x ≤ y :=
have _, from h _ rfl,
by { rcases this with ⟨b,h,h'⟩, cases h, exact h' }

lemma some_le_some {x y : α} (h : x ≤ y) : ((≤) : with_bot α → with_bot α → Prop) (some x) (some y) :=
λ a h', ⟨y, rfl, some.inj h' ▸ h⟩

lemma option.get_le_get (x y : with_bot α) (h : x.is_some) (h' : y.is_some) (hxy : x ≤ y) : get h ≤ get h' :=
by rw is_some_iff_exists at h h'; cases h with a h; cases h' with b h'; subst_vars; apply le_of_some_le_some hxy

section defn

variables (c : chain (with_bot α)) (h : ∃i, (c.nth i).is_some)

noncomputable def defn_chain : chain α :=
{ elems := (c.elems.drop $ classical.some h).attach.map $ λ x, option.get (d x),
  mono := λ i j h, by change stream.nth i (stream.map _ _) ≤ stream.nth j (stream.map _ _);
                      apply option.get_le_get;
                      simp  [stream.nth_map,stream.nth_drop];
                      apply c.mono; apply add_le_add_right h }

@[simp]
lemma mem_defn_chain (x : α) : x ∈ defn_chain c h ↔ x ∈ (c.elems.drop $ classical.some h).attach.map (λ x, option.get (d x)) :=
iff.refl _

end defn

protected noncomputable def Sup (c : chain (with_bot α)) : with_bot α :=
if h : ∃i, (c.nth i).is_some then some (Sup $ defn_chain c h) else none

-- @[reducible]
abbreviation with_option.has_mem : has_mem α (with_bot α) :=
option.has_mem

local attribute [instance] with_option.has_mem

lemma Sup_eq_some {c : chain (with_bot α)} {a : α} (h : some a ∈ c) : ∃ a', a ≤ a' ∧ option.Sup c = some a' :=
begin
  have h₀ : (∃ (i : ℕ), ↥(is_some (chain.nth i c))),
  { simp [is_some_iff_exists], rw chain.mem_def at h,
    apply exists_imp_exists _ h, intros i h, exact ⟨_,h.symm⟩ },
  simp [option.Sup,*], refine ⟨_,_,rfl⟩,
  cases (chain.mem_def _ _).mp h with i h',
  let j := classical.some h₀,
  cases le_total i j with hij hij,
  { apply le_of_some_le_some,
    apply @le_trans _ _ _ (chain.nth i c),
    { rw h', apply @le_refl (with_bot α) _, },
    apply @le_trans _ _ _ (chain.nth (classical.some h₀) c),
    { apply c.mono hij, },
    { have := classical.some_spec h₀, rw is_some_iff_exists at this,
      cases this with i this,
      erw [this], apply some_le_some,
      apply le_Sup, refine ⟨0,_⟩, apply some_inj.mp,
      simp only [defn_chain,stream.nth_map,stream.nth_drop,some_get],
      rw [← this], simp [stream.nth_drop], refl,
      } },
  { have : some a ∈ stream.drop (classical.some h₀) (c.elems),
    { simp [stream.mem_def,stream.nth_drop],
      replace h' : a ∈ c.nth i := h'.symm,
      existsi (i - j), rw nat.sub_add_cancel hij, exact (h'.symm : some _ = _) },
    apply le_Sup, simp [defn_chain,stream.mem_map_iff],
    refine ⟨_,this,_⟩, rw ← some_inj, simp },
end

lemma Sup_eq_none {c : chain (with_bot α)} {a : α} (h : a ∈ option.Sup c) :
  ∃ b : α, some b ∈ c ∧ b ≤ a :=
begin
  dsimp [option.Sup] at h, split_ifs at h with h'; [skip, cases h],
  rw [option.mem_def,some_inj] at h, rw ← h,
  have := classical.some_spec h',
  rw is_some_iff_exists at this,
  cases this with a' hh,
  refine ⟨a',⟨classical.some h',hh.symm⟩,_⟩,
  apply le_Sup, simp [defn_chain,stream.mem_map_iff],
  existsi [c.nth (classical.some h')],
  refine ⟨⟨0,_⟩,_⟩,
  simp [stream.nth_drop], refl,
  rw get_of_mem, rw hh, exact rfl
end

lemma Sup_eq_none' {c : chain (with_bot α)} {a : α} (h : a ∈ option.Sup c)  (k : α) (h' : ∀ b : α, some b ∈ c → b ≤ k) :
  a ≤ k :=
begin
  dsimp [option.Sup] at h, split_ifs at h with h''; [skip, cases h],
  rw [option.mem_def,some_inj] at h, rw ← h,
  apply Sup_le, intros y hh, apply h' y,
  simp [defn_chain,stream.mem_map_iff] at hh,
  rcases hh with ⟨a,ha,ha',ha''⟩,
  have ha := stream.mem_of_mem_drop ha,
  simp, exact ha
end

noncomputable instance complete_partial_order : complete_partial_order (with_bot α) :=
{ Sup    := option.Sup,
  le_Sup' := λ c i, by { intros a ha,
                         rw option.mem_def at ha,
                         replace ha := Sup_eq_some ⟨ i, ha.symm ⟩,
                         rcases ha with ⟨a',ha,ha'⟩, rw ← option.mem_def at ha',
                         exact ⟨a',ha',ha⟩, },
  Sup_le' := by { intros c x hx a ha, replace ha' := Sup_eq_none' ha,
                  replace ha := Sup_eq_none ha,
                  rcases ha with ⟨b,hb,hb'⟩, rw chain.mem_def at hb,
                  cases hb with i hb, have hx := hx i b hb.symm,
                  rcases hx with ⟨c',hc,hc'⟩, specialize ha' c' _,
                  exact ⟨_,hc,ha'⟩,
                  { clear_except hx hc, intros b hb, rw chain.mem_def at hb,
                    cases hb with i hb, specialize hx i b hb.symm,
                    rcases hx with ⟨a,ha,ha'⟩, cases option.mem_unique hc ha,
                    exact ha' } } }


lemma Sup_eq_none_iff {c : chain (with_bot α)} : Sup c = none ↔ ∀ i, c.nth i = none :=
sorry

end option


namespace roption

variables {α : Type u} {β : Type v} {γ : Type*}
open lattice (has_bot order_bot)
open complete_partial_order

lemma eq_of_chain {c : chain (roption α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b :=
begin
  cases ha with i ha, replace ha := ha.symm,
  cases hb with j hb, replace hb := hb.symm,
  wlog h : i ≤ j := le_total i j using [a b i j,b a j i],
  rw [eq_some_iff] at ha hb,
  have := c.mono h _ ha, apply mem_unique this hb
end

protected noncomputable def Sup (c : chain (roption α)) : roption α :=
if h : ∃a, some a ∈ c then some (classical.some h) else none

lemma Sup_eq_some {c : chain (roption α)} {a : α} (h : some a ∈ c) : roption.Sup c = some a :=
have ∃a, some a ∈ c, from ⟨a, h⟩,
have a' : some (classical.some this) ∈ c, from classical.some_spec this,
calc roption.Sup c = some (classical.some this) : dif_pos this
               ... = some a : congr_arg _ (eq_of_chain a' h)

lemma Sup_eq_none {c : chain (roption α)} (h : ¬∃a, some a ∈ c) : roption.Sup c = none :=
dif_neg h

lemma mem_chain_of_mem_Sup {c : chain (roption α)} {a : α} (h : a ∈ roption.Sup c) : some a ∈ c :=
begin
  simp [roption.Sup] at h, split_ifs at h,
  { have h' := classical.some_spec h_1,
    rw ← eq_some_iff at h, rw ← h, exact h' },
  { rcases h with ⟨ ⟨ ⟩ ⟩ }
end

noncomputable instance complete_partial_order : complete_partial_order (roption α) :=
{ Sup    := roption.Sup,
  le_Sup' := λ c i, by { intros a ha, rw ← eq_some_iff at ha,
                           rw Sup_eq_some _, apply mem_some, rw ← ha, exact ⟨i,rfl⟩, },
  Sup_le' := by { intros c x hx a ha, replace ha := mem_chain_of_mem_Sup ha,
                  cases ha with i ha, apply hx i, rw [← roption.eq_some_iff,ha], refl } }

lemma Sup_mem_self (c : chain (roption α)) : Sup c ∈ c :=
begin
  dsimp [Sup,roption.Sup], split_ifs, apply classical.some_spec h,
  simp [chain.mem_def] at h, existsi 0,
  have := roption.eq_none_or_eq_some (c.nth 0),
  rw or_iff_not_imp_right at this,
  symmetry, apply this, simp,
  intros x hx, apply h x 0 hx.symm,
end

section inst

lemma mem_Sup (x : α) (c : chain (roption α)) : x ∈ Sup c ↔ some x ∈ c :=
begin
  simp [Sup,roption.Sup],
  split,
  { split_ifs, swap, rintro ⟨⟨⟩⟩,
    intro h', have hh := classical.some_spec h,
    simp at h', subst x, exact hh },
  { intro h,
    have h' : ∃ (a : α), some a ∈ c := ⟨_,h⟩,
    rw dif_pos h', have hh := classical.some_spec h',
    rw eq_of_chain hh h, simp }
end

end inst

end roption

namespace pi

variables {α : Type*} {β : α → Type v} {γ : Type*} {φ : Type*}

section monotone

variables [∀a, preorder (β a)] [preorder γ] [preorder φ]

-- lemma monotone_apply (a : α) : monotone (λf:Πa, β a, f a) :=
-- assume f g hfg, hfg a

variables (β)

def apply (a : α) : (Πa, β a) →ₘ β a :=
Mono.mk _ $ assume f g hfg, hfg a

variables {β}

-- lemma monotone_lambda {γ : Type*} [partial_order γ] {m : γ → Πa, β a}
--   (hm : ∀a, monotone (λc, m c a)) : monotone m :=
-- assume f g h a, hm a h

def lambda (m : Πa, γ →ₘ β a) : γ →ₘ Πa, β a :=
Mono.mk (λ x y, m y x) (assume f g h a, (m a).mono h)

@[simp]

lemma lambda_def (m : Πa, γ →ₘ β a) (x : α) (y : γ) : lambda m y x = m x y := rfl

@[simp]
lemma apply_comp_lambda (m : Πa, γ →ₘ β a) (x : α) : (apply β x ∘ lambda m : γ →ₘ β x) = m x :=
Mono.ext $ λ x, _

@[simp]
lemma lambda_apply : lambda (apply β) = Mono.id := rfl

@[simp]
lemma coe_to_fun_apply (x : α) (f : Π (a : α), β a) : (apply β x) f = f x := rfl

@[simp]
lemma apply_comp_fst' [preorder α] (x : γ) (f : α × γ →ₘ φ) : (apply _ x ∘ f.fst' : α →ₘ φ) = f.fst x := rfl

@[simp]
lemma apply_comp_snd' [preorder α] (x : α) (f : α × γ →ₘ φ) : (apply _ x ∘ f.snd' : γ →ₘ φ) = f.snd x := rfl

end monotone

open complete_partial_order chain

variables  [∀a, complete_partial_order (β a)]
instance : complete_partial_order (Πa, β a) :=
{ Sup    := λc a, Sup (c.map (pi.apply β a)),
  Sup_le' := assume c f h a,
             Sup_le' (c.map (pi.apply β a)) (f a) (λ i, h i _),
  le_Sup' := assume c i a, le_Sup' (c.map (pi.apply β a)) i }

protected lemma Sup_eq (c : chain (Π x, β x)) (a : α) : Sup c a = Sup (c.map (pi.apply β a) ) := rfl

section continuity

variables [complete_partial_order γ]

lemma continuous_ext (f : Π a, γ →ₘ β a) (h : ∀ x, continuous (f x)) :
  continuous (pi.lambda f) :=
begin
  intro c, ext,
  simp only [pi.Sup_eq, map_comp, h x c, pi.lambda_def, pi.apply_comp_lambda]
end

lemma continuous_congr (f : Π a, γ →ₘ β a) (x : α)
  (h : continuous (lambda f)) :
  continuous (f x) :=
begin
  simp [continuous',continuous] at ⊢ h,
  intro C, apply congr_fun (h C) x,
end

lemma continuous_congr' (x : α) :
  continuous (apply β x) :=
continuous_congr (apply β) _ (by simp only [pi.lambda_apply, complete_partial_order.continuous_id])

end continuity

end pi

namespace seq
variables {α : Type*}

section
local attribute [priority 0] with_bot.preorder
variable [H : preorder α]

instance stream.preorder : preorder (stream α) :=
@pi.preorder _ _ (λ _, H)

instance : preorder (seq α) :=
@subtype.preorder _ (@stream.preorder _  (@with_bot.preorder _ H)) _

open complete_partial_order

protected noncomputable def Sup' [complete_partial_order α] (x : chain $ seq α) : stream (with_bot α) :=
let x : chain (@subtype (stream (with_bot α)) _) := x in
λ i, Sup (x.map $ pi.apply _ i ∘ ⟨subtype.val⟩)

protected noncomputable def Sup [complete_partial_order α] (x : chain $ seq α) : seq α :=
⟨ @seq.Sup' _ _ x,
 by { simp [seq.Sup',option.Sup_eq_none_iff], intros n hn i,
      apply (chain.nth i x).property (hn _), } ⟩

instance stream.partial_order [H : partial_order α] : partial_order (stream α) :=
@pi.partial_order _ _ (λ _, H)

protected def partial_order [H : partial_order α] : partial_order (seq α) :=
@subtype.partial_order _ (@stream.partial_order _  (@with_bot.partial_order _ H)) _

protected noncomputable def complete_partial_order [H : complete_partial_order α] : complete_partial_order (seq α) :=
{ Sup := @seq.Sup _ H,
  Sup_le' := λ c x H i, Sup_le' _ _ $ λ j, H _ _,
  le_Sup' := λ c i j,
    suffices (c.map $ pi.apply _ j ∘ ⟨@subtype.val (stream $ with_bot α) _⟩).nth i ≤ seq.Sup' c j,
      by { simp [chain.nth_map] at this, exact this },
    le_Sup' _ _,
  .. seq.partial_order }

end

end seq

namespace wseq
variables {α : Type*}

instance {α} [preorder α] : preorder (wseq α) :=
show preorder (seq (with_bot α)), from
seq.preorder

open complete_partial_order

noncomputable instance [complete_partial_order α] : complete_partial_order (wseq α) :=
show complete_partial_order (seq (with_bot α)), from
seq.complete_partial_order

end wseq

namespace prod

variables {α : Type*} {β : Type*}

variables [complete_partial_order α]
          [complete_partial_order β]
open complete_partial_order

instance : complete_partial_order (α × β) :=
{ Sup := λ c, (Sup $ c.map ⟨prod.fst⟩, Sup $ c.map ⟨prod.snd⟩),
  Sup_le' := λ c x h, ⟨Sup_le' _ _ $ λ i, (h i).left, Sup_le' _ _ $ λ i, (h i).right⟩,
  le_Sup' := λ c i, ⟨le_Sup' (c.map ⟨prod.fst⟩) _, le_Sup' (c.map ⟨prod.snd⟩) _⟩  }

lemma continuous_fst : continuous ⟨@prod.fst α β⟩ :=
λ c, rfl

lemma continuous_snd : continuous ⟨@prod.snd α β⟩ :=
λ c, rfl

end prod

namespace set
variables (α : Type u)

instance : partial_order (set α) :=
{ le          := (⊆),
  le_refl     := assume s x hx, hx,
  le_trans    := assume a b c hab hbc x hx, hbc $ hab $ hx,
  le_antisymm := assume a b hab hba, ext $ assume x, ⟨@hab x, @hba x⟩ }

instance : complete_partial_order (set α) :=
{ Sup     := λc, ⋃ i, c.elems i,
  Sup_le' := assume ⟨c, _⟩ s hs x hx, by { simp at hx, cases hx with i hx, exact hs i hx },
  le_Sup' := assume ⟨c, _⟩ s x hx, by { simp at hx ⊢, exact ⟨_, hx⟩ } }

end set

structure Cont
  (α : Type*) [complete_partial_order α]
  (β : Type*) [complete_partial_order β] :=
(F : α →ₘ β)
(cont : complete_partial_order.continuous F)

infixr ` →ₖ `:25 := Cont

namespace Cont

variables {α : Type*} [complete_partial_order α]
          {β : Type*} [complete_partial_order β]
          {γ : Type*} [complete_partial_order γ]

instance : has_coe_to_fun (α →ₖ β) :=
{ F := λ _, α → β,
  coe := λ x, Cont.F x }

def comp (f : β →ₖ γ) (g : α →ₖ β) : α →ₖ γ :=
{ F := f.F ∘ g.F,
  cont := complete_partial_order.continuous_comp _ _ f.cont g.cont }

infixr ∘ := comp

lemma ext : Π {x y : α →ₖ β} (h : x.F = y.F), x = y
| ⟨x,_⟩ ⟨y,_⟩ :=
assume h : x = y, by congr; exact h

instance : partial_order (α →ₖ β) :=
{ le := λ x y, x.F ≤ y.F,
  le_refl := λ x, le_refl x.F,
  le_antisymm := λ x y h₀ h₁, ext (le_antisymm h₀ h₁),
  le_trans := λ x y z, le_trans }

section

variables (α β)
def FF : (α →ₖ β) →ₘ (α →ₘ β) := sorry

end

open complete_partial_order

lemma continuous_FF (f : α →ₖ β) : continuous (FF α β f) := _

instance : complete_partial_order (α →ₘ β) :=
{ Sup := λ c, Mono.mk (Sup $ c.map $ Mono.FF α β) $
         λ x y h, Sup_le_Sup_of_le $ chain.map_le_map _ _ _ $
         λ f h', Exists.cases_on (chain.exists_of_mem_map _ _ h') $
         λ w ⟨h₀,h₁⟩, h₁ ▸ w.mono h,
  Sup_le' := λ c x h i, Sup_le' _ _ $ λ j,
             by simp [chain.nth_map];
                apply (@Mono.FF α β _ _).mono (h j),
  le_Sup' := λ c i x, by simp [Mono.mk,Sup,chain.map_comp]; apply le_Sup;
                         apply chain.mem_map _ (pi.apply (λ (a : α), β) x ∘ @Mono.FF α β _ _);
                         apply chain.nth_mem,
  .. Mono.partial_order }

lemma Mono.continuous_FF (f : α →ₘ β) : continuous (Mono.FF α β) := _

-- set_option pp.implicit true

instance : complete_partial_order (α →ₖ β) :=
{ Sup := λ c, Cont.mk (Sup $ c.map $ FF α β) $
         λ c', by { conv { to_lhs, },  dsimp [Sup],
                    generalize : (chain.map c (FF α β)) = k, simp,
                    generalize h : (chain.map k (Mono.FF α β)) = c₀,
                    conv { to_lhs, erw h },
                    conv { to_rhs, rw h },
                    erw h,  }, -- ; simp [chain.map_comp]; congr; refl,
  .. Cont.partial_order }

end Cont


namespace complete_partial_order

variables {α : Type*} [complete_partial_order α]
          {β : Type*} [complete_partial_order β]
          {γ : Type*} [complete_partial_order γ]

variables (c : chain α)

lemma cont_const {β} [complete_partial_order β] (f : β) (c : chain α) :
  Sup (c.map (Mono.const f)) = f :=
by rw [chain.map_const',Sup_const]

lemma cont_ite [complete_partial_order β] {p : Prop} {hp : decidable p} (c : chain α) (f g : α →ₘ β) :
  Sup (c.map (Mono.ite p f g)) = @ite p hp _ (Sup $ c.map f) (Sup $ c.map g) :=
by dsimp [Mono.ite]; split_ifs; refl

lemma bind_mono {β γ} (f : α → roption β)
                (g : α → β → roption γ)
  (hf : monotone f) (hg : monotone g) :
  monotone (λ x, f x >>= g x)  :=
begin
  intros x y h a, simp, intros b hb ha,
  refine ⟨b,hf h _ hb,hg h _ _ ha⟩,
end

instance bind.is_monotone
         {β γ} (f : α → roption β)
         (g : α → β → roption γ)
  [hf : is_monotone f] [hg : is_monotone g] :
  is_monotone (λ x, f x >>= g x) :=
⟨ bind_mono _ _ hf.mono hg.mono ⟩

lemma Sup_bind {β γ} (c : chain α) (f : α → roption β) [is_monotone f] (g : α → β → roption γ) [is_monotone g] :
  Sup (c.map ⟨λ x, f x >>= g x⟩) = Sup (c.map ⟨f⟩) >>= Sup (c.map ⟨g⟩) :=
begin
  apply eq_of_forall_ge_iff, intro x,
  simp [Sup_le_iff,roption.bind_le,-roption.bind_eq_bind,chain.mem_map_iff],
  split; intro h''',
  { intros b hb, apply Sup_le _ _ _,
    simp [-roption.bind_eq_bind,chain.mem_map_iff],
    intros y a z hz ha hy, subst a, subst y,
    { intros y hy, simp [roption.mem_Sup] at hb,
      replace h₀ := chain.exists_of_mem_map _ _ hb,
      rcases h₀ with ⟨k,h₂,h₃⟩,
      rw roption.eq_some_iff at h₃,
      cases chain.le_total_of_mem_of_mem _ hz h₂ with hh hh,
      { replace h''' := h''' _ k h₂ rfl,
        apply h''', simp, refine ⟨_,h₃,_⟩,
        have h'' := is_monotone.mono' g,
        apply h'' hh _ _ hy },
      { replace h''' := h''' _ z hz rfl,
        apply h''', simp, refine ⟨_,_,hy⟩,
        have h' := is_monotone.mono' f,
        apply h' hh _ h₃ } } },
  { intros y a ha hy, subst hy, intros b hb, simp at hb,
    rcases hb with ⟨b',hb₀,hb₁⟩,
    apply h''' b' _ b _, revert hb₀,
    apply le_Sup _ (f a) _, apply chain.mem_map _ ⟨f⟩ _ ha,
    apply le_Sup _ (g a b') _, exact hb₁, rw chain.map_comp,
    apply chain.mem_map _ (pi.apply (λ (a : β), roption γ) b' ∘ ⟨g⟩) _ ha },
end

lemma cont_bind {β γ} {f : α → roption β} [is_monotone f] {g : α → β → roption γ} [is_monotone g]
  (hf : continuous ⟨f⟩)
  (hg : continuous ⟨g⟩) :
  continuous ⟨λ x, f x >>= g x⟩ :=
λ c, by rw [Sup_bind,← hf,← hg]; refl

-- lemma cont_const' (f : β) :
--   continuous' (λ x : α, f) :=
-- by { split, intro c; rw cont_const }

lemma cont_id :
  continuous (@Mono.id α _) :=
by { intro c, erw chain.map_id, refl }

lemma cont_id' :
  continuous' (@id α) :=
by { split, intro c, erw chain.map_id, refl }

lemma cont_ite' {p : Prop} {hp : decidable p} (f g : α → β)
  (hf : continuous' f) (hg : continuous' g) :
  continuous' (λ x, @ite p hp _ (f x) (g x)) :=
by { haveI : is_monotone f := ⟨ hf.fst ⟩, haveI : is_monotone g := ⟨ hg.fst ⟩,
     split, intro c, change Mono.ite p ⟨f⟩ ⟨g⟩ (Sup c) = _,
     convert (cont_ite _ ⟨f⟩ ⟨g⟩).symm, dsimp [Mono.ite],
     erw [← hg.snd,← hf.snd], refl }

lemma Mono.to_continuous' (f : α → roption β) [H : is_monotone f]
  (h : continuous ⟨f⟩) : continuous' f :=
⟨ H.mono, h ⟩

def Mono.of_continuous' (f : α → β)
  (h : continuous' f) : α →ₘ β :=
Mono.mk f h.fst

lemma Mono.of_continuous'' (f : α → β)
  (h : continuous' f) : continuous (Mono.of_continuous' _ h) :=
h.snd

lemma cont_bind' {β γ} [complete_partial_order β] (f : α → roption β) (g : α → β → roption γ)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x >>= g x) :=
by {
  let hf := Mono.of_continuous'' _ hf,
  let hg := Mono.of_continuous'' _ hg,
  -- haveI : is_monotone f := ⟨hf.fst⟩, haveI : is_monotone g := ⟨hg.fst⟩,
  -- haveI := bind.is_monotone hf hg,
  have := cont_bind hf hg,
  let z := Mono.to_continuous' f, }

lemma cont_map' {β γ : Type*} (f : β → γ) (g : α → roption β)
  (hg : continuous' g) :
  continuous' (λ x, f <$> g x) :=
begin
--   simp [-roption.bind_eq_bind,-roption.map_eq_map,(bind_pure_comp_eq_map _ _ _).symm],
--   apply cont_bind' _ _ hg, apply cont_const'
end

lemma cont_seq' {β γ : Type*} (f : α → roption (β → γ)) (g : α → roption β)
  (hf : continuous' f)
  (hg : continuous' g) :
  continuous' (λ x, f x <*> g x) :=
begin
--   simp [-roption.bind_eq_bind,seq_eq_bind_map], apply cont_bind' _ _ hf,
--   apply pi.continuous_ext, intro x, apply cont_map' _ _ hg,
end

end complete_partial_order

namespace complete_partial_order

variables {α : Type*} {β : Type*} {γ : Type*}

open function (uncurry)

section monotone

def split (f : α → α → β) (x : α) : β := f x x
def dup (x : α) : α × α := (x, x)

variables [preorder α] [preorder β] [preorder γ]

lemma monotone_split {f : α → α → β} (hf : monotone f) (hf' : monotone $ flip f) :
  monotone (split f) :=
λ a b h, le_trans (hf h _) (hf' h _)

lemma monotone_split' {f : α → α → β} (hf : monotone $ uncurry f) :
  monotone (split f) :=
λ a b h, @hf (a,a) (b,b) ⟨h,h⟩

lemma monotone_dup :
  monotone (@dup α) :=
λ a b h, ⟨h,h⟩

section zip

variables  (f : α × β →ₘ γ) -- (hf : monotone $ uncurry f)
open function

variables (ca : chain α) (cb : chain β)

def zip : chain (α × β) :=
⟨ca.elems.zip prod.mk cb.elems,
 λ i j h, ⟨ca.mono h, cb.mono h⟩⟩

def zip_with : chain γ :=
⟨ca.elems.zip (curry f) cb.elems,
 λ i j h, f.mono ⟨ca.mono h,cb.mono h⟩⟩

lemma map_zip : (zip ca cb).map f = zip_with f ca cb := rfl

lemma map_fst (x : β) : ca.map (f.fst x) = zip_with f ca (chain.const x) := rfl

lemma map_snd (x : α) : cb.map (f.snd x) = zip_with f (chain.const x) cb := rfl

lemma map_fst_zip : (zip ca cb).map ⟨prod.fst⟩ = ca := chain.ext _ _ $ λ i, rfl

lemma map_snd_zip : (zip ca cb).map ⟨prod.snd⟩ = cb := chain.ext _ _ $ λ i, rfl

-- lemma map_fst' (c : chain α) : c.map f.fst' = zip_with f c (chain.const x) := rfl

-- lemma map_snd (c : chain β) : c.map f.snd' = zip_with f (chain.const x) c := rfl

variables (g : α × α →ₘ β)

lemma zip_with_self (c : chain α) : zip_with g c c = c.map g.split := rfl

lemma zip_with_const (x : α) (c : chain β) : zip_with f (chain.const x) c = c.map (f.snd x) := rfl

lemma zip_with_le_zip_with {ca ca' : chain α} {cb cb' : chain β} (ha : ca ≤ ca') (hb : cb ≤ cb') :
  zip_with f ca cb ≤ zip_with f ca' cb' :=
begin
  intros z hz, cases hz with i hz, simp [zip_with,stream.nth_zip] at hz,
  replace ha := ha _ ⟨i,rfl⟩, rcases ha with ⟨a, ⟨⟨j,ha⟩,ha'⟩⟩,
  replace hb := hb _ ⟨i,rfl⟩, rcases hb with ⟨b, ⟨⟨k,hb⟩,hb'⟩⟩,
  subst z, subst a, subst b,
  cases le_total j k with hh hh;
  [{ let p := k, replace ha' := le_trans ha' (ca'.mono hh) },
   { let p := j, replace hb' := le_trans hb' (cb'.mono hh) }],
  all_goals
  { existsi f.snd (stream.nth p (ca'.elems)) _,
    refine ⟨⟨p,rfl⟩,_⟩,
    change f (_,_) ≤ f (_,_),
    apply f.mono _, exact ⟨ha',hb'⟩ },
end

lemma exists_of_mem_zip_with (x : γ) {ca : chain α} {cb : chain β} (h : x ∈ zip_with f ca cb) :
  (∃ (a ∈ ca) (b ∈ cb), x = f (a, b)) :=
Exists.rec_on h $
λ i, assume h : _ = _,
⟨ca.nth i, ⟨_,rfl⟩, cb.nth i, ⟨_,rfl⟩, by cases ca; cases cb; exact h⟩

@[simp]
lemma nth_zip_with {ca : chain α} {cb : chain β} (i : ℕ) : (zip_with f ca cb).nth i = f (ca.nth i, cb.nth i) := rfl

lemma zip_with_eq_zip_with_attach {ca : chain α} {cb : chain β} :
  zip_with f ca cb =
  zip_with (f ∘ Mono.first ⟨subtype.val⟩) ca.attach cb :=
chain.ext _ _ $ λ i, rfl

lemma map_curry {c : chain (α × β)} :
  c.map f = zip_with f (c.map ⟨prod.fst⟩) (c.map ⟨prod.snd⟩) :=
by ext; simp only [chain.nth_map, nth_zip_with]; cases (chain.nth i c); refl

end zip

end monotone

section zip

variables [preorder α]
          [complete_partial_order β]
          [complete_partial_order γ]

lemma continuous_left (f : α × β →ₘ γ) (hc : continuous f.snd') : ∀ x, continuous (f.snd x) :=
λ x c, congr_fun (hc c) x

lemma continuous_left' (f : α × β →ₘ γ) (hc : ∀ x, continuous $ f.snd x) : continuous f.snd' :=
λ c, funext $ λ x, by rw [Mono.coe_to_fun_snd_swap.symm,hc,pi.Sup_eq,chain.map_comp,pi.apply_comp_snd']

lemma continuous_right (f : β × α →ₘ γ) (hc : continuous f.fst') : ∀ x, continuous (f.fst x) :=
λ x c, congr_fun (hc c) x

lemma continuous_right' (f : β × α →ₘ γ) (hc : ∀ x, continuous $ f.fst x) : continuous f.fst' :=
λ c, funext $ λ x, by rw [Mono.coe_to_fun_fst_swap.symm,hc,pi.Sup_eq,chain.map_comp,pi.apply_comp_fst']

end zip

section continuous

open complete_partial_order
variables [complete_partial_order α]
          [complete_partial_order β]
          [complete_partial_order γ]
variables {f : α × β →ₘ γ} (hf : continuous f)

lemma Sup_zip (ca : chain α) (cb : chain β) : Sup (zip ca cb) = (Sup ca, Sup cb) :=
by dsimp [Sup]; rw [map_fst_zip,map_snd_zip]

include hf

lemma Sup_zip_with (ca : chain α) (cb : chain β) : Sup (zip_with f ca cb) = f (Sup ca, Sup cb) :=
by rw [← map_zip,← hf,Sup_zip]

lemma continuous_fst' : continuous f.fst' :=
λ c, funext $ λ a, by { simp [Sup,chain.map_comp,map_fst,Sup_zip_with hf,Sup_const], refl }

lemma continuous_fst : ∀ x, continuous (f.fst x) :=
continuous_right _ (continuous_fst' hf)

lemma continuous_snd' : continuous f.snd' :=
λ c, funext $ λ a, by { simp [Sup,chain.map_comp,map_snd,Sup_zip_with hf,Sup_const], refl }

lemma continuous_snd : ∀ x, continuous (f.snd x) :=
continuous_left _ (continuous_snd' hf)

end continuous

section zip

variables [preorder α]
          [complete_partial_order β]
          [complete_partial_order γ]

variables  (f : α × β →ₘ γ)
           (ca : chain α) (cb : chain β)
           (hc : continuous f.snd')
include hc

lemma Sup_zip_with' : Sup (zip_with f ca cb) = Sup (ca.map $ f.fst (Sup cb) ) :=
begin
  apply le_antisymm,
  { apply Sup_le, intros y hy, replace hy := exists_of_mem_zip_with _ _ hy,
    rcases hy with ⟨a,ha,b,hb,hy⟩, rw hy,
    transitivity Sup (cb.map (f.snd a)),
    { apply le_Sup, apply chain.mem_map _ (Mono.snd f a) _ hb },
    { apply Sup_le,
      intros z hz, replace hz := chain.exists_of_mem_map _ _ hz,
      rcases hz with ⟨z',hz₀,hz₁⟩, rw ← hz₁,
      apply le_Sup_of_le (f.snd a $ Sup cb) _ _,
      { apply Mono.mono, apply le_Sup _ _ hz₀ },
      { rw chain.mem_map_iff, exact ⟨_,ha,rfl⟩ } } },
  { apply Sup_le, intros y hy,
    rcases chain.exists_of_mem_map _ _ hy with ⟨w,hw₀,hw₁⟩,
    replace hc := congr_fun (hc cb) w, dsimp [Sup,chain.map_comp,Mono.coe_to_fun_snd'] at hc,
    simp [Mono.coe_to_fun_fst] at hw₁,
    rw [← hw₁,hc,← zip_with_const],
    apply Sup_le_Sup_of_le, apply zip_with_le_zip_with _ _ (le_refl _),
    apply chain.const_le_of_mem _ _ hw₀ },
end

lemma Sup_zip' :
  Sup (zip_with f ca cb) =
  Sup (ca.map ⟨λ a, Sup $ cb.map (f.snd a)⟩) :=
have _, from λ x, (continuous_left _ hc x cb).symm,
by simp [Sup_zip_with' _ _ _ hc,this]; refl

omit hc

-- lemma monotone_uncurry_flip_iff : monotone (uncurry $ flip f) ↔ monotone (uncurry f) :=
-- by split; rintros hf ⟨x,x'⟩ ⟨y,y'⟩ h; exact @hf (x',x) (y',y) ⟨h.2,h.1⟩

lemma zip_with_flip :
  zip_with f.flip cb ca = zip_with f ca cb :=
by ext; refl

end zip

variables [complete_partial_order α]
          [complete_partial_order β]
          [complete_partial_order γ]


lemma Sup_Sup_swap (ca : chain α) (cb : chain β) (f : α × β →ₘ γ) (hc : continuous f) :
  Sup (ca.map ⟨λ a, Sup $ cb.map (f.snd a)⟩) =
  Sup (cb.map ⟨λ b, Sup $ ca.map (f.fst b)⟩) :=
by rw [← Sup_zip',← zip_with_flip,Sup_zip' f.flip];
   [ refl,
     exact continuous_fst' hc,
     exact continuous_snd' hc ]

lemma continuous_dup : continuous' $ @dup α :=
begin
  existsi monotone_dup,
  intro c, ext; dsimp [Sup,dup];
  rw [chain.map_comp],
  all_goals
  { transitivity Sup (c.map Mono.id); [rw chain.map_id, refl] },
end

lemma continuous_uncurry {f : α × β →ₘ γ}
  (h₀ : ∀ x, continuous $ f.fst x) (h₁ : ∀ x, continuous $ f.snd x) :
  continuous f :=
begin
  intro c,
  rw [map_curry,Sup_zip'],
  { simp [Sup], rw [← Mono.coe_to_fun_fst,h₀],
    congr, ext, rw [Mono.coe_to_fun_fst_eq_snd,h₁], refl },
  { apply continuous_left' _ h₁, }
end

lemma continuous_uncurry' {f : α × β →ₘ γ}
  (h₀ : continuous f.fst') (h₁ : continuous f.snd') :
  continuous f :=
continuous_uncurry
  (continuous_right _ h₀)
  (continuous_left _ h₁)

lemma continuous_split (f : α × α →ₘ β)
  (h₀ : continuous f.fst') (h₁ : continuous f.snd') :
  continuous f.split :=
begin
  let sp : α →ₘ α × α := Mono.mk (λ x, (x,x)) (λ x y h, ⟨h,h⟩),
  suffices : continuous (f ∘ sp), exact this,
  apply continuous_comp _ _ (continuous_uncurry' h₀ h₁),
  intro, simp [Sup,chain.map_comp],
  have : Mono.mk' prod.fst ∘ sp = Mono.id, { ext, refl },
  have : Mono.mk' prod.snd ∘ sp = Mono.id, { ext, refl },
  simp [*,chain.map_id]
end

end complete_partial_order

namespace complete_partial_order

open function chain
variables (α : Type*) (β : α → Type*) (γ : Π a : α, β a → Type*)

instance is_monotone.curry [∀ a b, preorder $ γ a b] : is_monotone (@curry' α β γ) := ⟨ monotone_curry' α β γ ⟩
instance is_monotone.uncurry [∀ a b, preorder $ γ a b] : is_monotone (@uncurry' α β γ) := ⟨ monotone_uncurry' α β γ ⟩

variables [∀ a b, complete_partial_order $ γ a b]

lemma continuous_curry : continuous (Mono.curry γ) :=
λ c, by { ext x y, dsimp [curry,Sup], rw [map_comp,map_comp], refl }

lemma continuous_uncurry'' : continuous (Mono.uncurry γ) :=
λ c, by { ext x y, dsimp [uncurry,Sup], rw [map_comp], refl }

end complete_partial_order

namespace tactic

open complete_partial_order expr native

@[user_attribute]
meta def continuity_attr : user_attribute (rb_map name $ list name) :=
{ name := `continuity,
  descr := "proof rule for continuity in the sense of complete partial orders",
  cache_cfg := { mk_cache := λ (ls : list name),
                             do { let m := rb_map.mk name (list name),
                                  ls.mfoldl (λ m n,
                                  do { (_,t) ← mk_const n >>= infer_type >>= mk_local_pis,
                                       `(continuous' %%f) ← pure t <|> fail format!"{t}",
                                       let l := f.binding_body,
                                       pure $ m.insert_cons l.get_app_fn.const_name n }) m
                                   },
                 dependencies := [] } }

meta def continuity_ext : tactic (list expr) :=
do `(continuous' %%f) ← target,
   (args,_) ← infer_type f >>= mk_local_pis,
   let arity := args.length - 1,
   iterate_exactly' arity $
     applyc ``pi.continuous_ext >> intro1

meta def continuity_step : tactic unit :=
do continuity_ext,
   e@`(continuous' %%f) ← target,
   (lam n bi d b) ← pure f,
   m ← continuity_attr.get_cache,
   match b.get_app_fn with
   | (const n _) :=
     do ls ← m.find n <|> pure [``cont_const],
        ls.any_of applyc <|> fail format!"unsupported constant: {n}"
   | v@(var _) :=
     do let args := b.get_app_args,
        vs ← args.mmap $ infer_type >=> mk_local_def `v,
        let f' := lam n bi d $ v.mk_app vs,
        let e' := (e.app_fn f').pis vs,
        g ← mk_meta_var e',
        exact $ g.mk_app args,
        gs ← get_goals,
        set_goals $ g :: gs,
        vs ← intron' args.length,
        vs.reverse.mmap' $ λ v, refine ``(pi.continuous_congr _ %%v _),
        refine ``(cont_id)
   | t := do
     f ← pp f,
     fail format!"unsupported {f}"
   end

meta def my_unfold (n : name) : tactic unit :=
do ls ← get_eqn_lemmas_for ff n,
   ls ← ls.mmap mk_const,
   s ← simp_lemmas.mk.append ls,
   simp_target s

meta def show_continuity : tactic unit :=
focus1 $
do `(continuous' %%f) ← target,
   let n := f.get_app_fn.const_name,
   vs ← continuity_ext,
   e@`(continuous' %%f) ← target,
   cases_on_equations f,
   all_goals $ do
   { intros,
     target >>= instantiate_mvars >>= unsafe_change,
     my_unfold n,
     repeat continuity_step,
     done },
   skip

run_cmd add_interactive [``continuity_step,``continuity_ext,``show_continuity]
attribute [continuity] cont_const cont_id cont_ite cont_bind cont_map cont_seq'

end tactic


namespace state_t

open complete_partial_order

variables {α β γ σ : Type u} {m : Type u → Type*}

instance [preorder (m (β × α))] : preorder (state_t α m β) :=
{ le := λ x y, x.run ≤ y.run,
  le_trans := λ a b c, @le_trans _ _ a.run b.run c.run,
  le_refl := λ a, @le_refl _ _ a.run }

instance [partial_order (m (β × α))] : partial_order (state_t α m β) :=
{ le_antisymm := λ ⟨a⟩ ⟨b⟩ h h', congr_arg _ $ @le_antisymm _ _ a b h h', .. state_t.preorder }

lemma monotone_run [preorder (m (β × α))] : monotone (@run α m β) :=
λ x y h, h

lemma monotone_mk (α β : Type u) (m : Type u → Type*) [preorder (m (β × α))] : monotone (@mk α m β) :=
λ x y h, h

instance [complete_partial_order (m (β × α))] : complete_partial_order (state_t α m β) :=
{ Sup := λ c, ⟨ Sup $ c.map state_t.run monotone_run ⟩,
  Sup_le' := λ c x h, Sup_le' _ x.run $ by simp only [chain.nth_map]; exact h,
  le_Sup' := λ c i, show state_t.run _ ≤ _, by { transitivity' (chain.nth i $ c.map _ monotone_run),
                                                 refl', apply le_Sup' _ i } }

-- @[continuity]
lemma continuous_run [complete_partial_order (m (β × α))] : continuous' (@run α m β) :=
⟨ monotone_run, λ c, rfl ⟩

-- @[continuity]
lemma continuous_mk [complete_partial_order (m (β × α))] : continuous' (@mk α m β) :=
⟨ λ a b h, monotone_mk α β m h, λ c, ext $ λ st, rfl ⟩

@[continuity]
lemma continuous_mk' [complete_partial_order (m (β × α))]
  [complete_partial_order γ]
  (f : γ → α → m (β × α)) (hf : continuous' f) :
  continuous' (λ x : γ, @mk α m β $ f x) :=
continuous_comp' _ _ continuous_mk hf

variables [complete_partial_order α]
          [complete_partial_order (m $ β × σ)]
          [complete_partial_order (m $ γ × σ)]
          [monad m]

-- @[continuity]
-- lemma continuous_bind (f : α → state_t σ m β) (g : α → β → state_t σ m γ) :
--   continuous' f → continuous' g → continuous' (λ (x : α), f x >>= g x) :=
-- assume hf hg,
-- by { dsimp [(>>=),state_t.bind],
--      -- show_continuity,
--      continuity_step,
--      continuity_ext,
--      apply continuous_mk, }

-- @[continuity]
-- lemma continuous_and_then (f : α → state_t σ m β) (g : α → state_t σ m γ) :
--   continuous' f → continuous' g → continuous' (λ (x : α), f x >> g x) :=
-- λ hf hg, continuous_bind f _ hf $ pi.continuous_ext _ $ λ _, hg

end state_t
