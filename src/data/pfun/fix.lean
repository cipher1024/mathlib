import order.bounded_lattice
import order.complete_partial_order
import data.nat.up
import logic.basic
import data.stream.basic
import order.basic
import order.bounded_lattice

universes u v

local attribute [instance, priority 0] classical.prop_decidable
variables {α : Type*}

namespace fix

open lattice (has_bot order_bot) roption
open nat nat.up lattice.has_bot lattice.order_bot (bot_le)
open complete_partial_order (Sup)

variables {β : α → Type*}

section defn

variables (f : (Π a, roption $ β a) → (Π a, roption $ β a))

def succ' (i : α → ℕ) (x : α) : ℕ := (i x).succ

def approx : stream $ Π a, roption $ β a
| 0 := ⊥
| (nat.succ i) := f (approx i)

def fix_aux {p : ℕ → Prop} (i : nat.up p) (g : Π j : nat.up p, j < i → Π a, roption $ β a) : Π a, roption $ β a :=
f $ λ x : α,
assert (¬p (i.val)) $ λ h : ¬ p (i.val),
g (i.succ h) (nat.lt_succ_self _) x

def fix (x : α) : roption $ β x :=
assert (∃ i, (approx f i x).dom) $ λ h,
well_founded.fix.{1} (nat.up.wf h) (fix_aux f) nat.up.zero x

lemma fix_def {x : α} (h' : ∃ i, (approx f i x).dom) :
  fix f x = approx f (nat.succ $ nat.up.find h') x :=
begin
  let p := λ (i : ℕ), (approx f i x).dom,
  have : p (up.find h') := up.p_find h',
  generalize hk : find h' = k,
  replace hk : find h' = k + (@up.zero p).val := hk,
  rw hk at this,
  revert hk,
  dsimp [fix], rw assert_pos h', revert this,
  generalize : up.zero = z, intros,
  suffices : ∀ x', well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x' = approx f (succ k) x',
    from this _,
  induction k generalizing z; intro,
  { rw [approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1, rw assert_neg, refl,
    rw nat.zero_add at this,
    simp *, exact this },
  { rw [approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1,
    have hh : ¬(approx f (z.val) x).dom,
    { apply find_least_solution h' z.val,
      rw [hk,nat.succ_add,← nat.add_succ],
      apply nat.lt_of_succ_le,
      apply nat.le_add_left },
    rw succ_add_eq_succ_add at this hk,
    rw [assert_pos hh, k_ih (up.succ z hh) this hk] }
end

lemma fix_def' {x : α} (h' : ¬ ∃ i, (approx f i x).dom) :
  fix f x = none :=
by dsimp [fix]; rw assert_neg h'

end defn

variables (f : (Π a, roption $ β a) →ₘ (Π a, roption $ β a))
include f

lemma approx_mono' {i : ℕ} : approx f i ≤ approx f (succ i) :=
begin
  induction i, dsimp [approx], apply @bot_le _ _ (f ⊥),
  intro, apply f.mono, apply i_ih
end

lemma approx_mono {i j : ℕ} (hij : i ≤ j) : approx f i ≤ approx f j :=
begin
  induction j, cases hij, refine @le_refl _ _ _,
  cases hij, apply @le_refl _ _ _,
  apply @le_trans _ _ _ (approx f j_n) _ (j_ih hij_a),
  apply approx_mono' f
end

lemma mem_fix (a : α) (b : β a) : b ∈ fix f a ↔ ∃ i, b ∈ approx f i a :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i a).dom,
  { simp [fix_def f h₀],
    split; intro hh, exact ⟨_,hh⟩,
    have h₁ := p_find h₀,
    rw [dom_iff_mem] at h₁,
    cases h₁ with y h₁,
    replace h₁ := approx_mono' f _ _ h₁,
    suffices : y = b, subst this, exact h₁,
    cases hh with i hh,
    revert h₁, generalize : (succ (find h₀)) = j, intro,
    wlog : i ≤ j := le_total i j using [i j b y,j i y b],
    replace hh := approx_mono f case _ _ hh,
    apply roption.mem_unique h₁ hh },
  { simp [fix_def' f h₀],
    simp [dom_iff_mem] at h₀,
    intro, apply h₀ }
end

lemma max_fix (i : ℕ) : approx f i ≤ fix f :=
assume a b hh,
by { rw [mem_fix f], exact ⟨_,hh⟩ }

lemma min_fix (x : α) : ∃ i, fix f x ≤ approx f i x :=
begin
  by_cases hh : ∃ i b, b ∈ approx f i x,
  { rcases hh with ⟨i,b,hb⟩, existsi i,
    intros b' h',
    have hb' := max_fix f i _ _ hb,
    have hh := roption.mem_unique h' hb',
    subst hh, exact hb },
  { simp at hh, existsi 0,
    intros b' h', simp [mem_fix f] at h',
    cases h' with i h',
    cases hh _ _ h' }
end

lemma approx_eq {i j : ℕ} {a : α} (hi : (approx f i a).dom) (hj : (approx f j a).dom) :
  approx f i a = approx f j a :=
begin
  simp [dom_iff_mem] at hi hj,
  cases hi with b hi, cases hj with b' hj,
  have : b' = b,
  { wlog hij : i ≤ j := le_total i j using [i j b b',j i b' b],
    apply mem_unique hj, apply approx_mono f hij _ _ hi, },
  subst b',
  ext y, split; intro hy,
  rename hi hh, rename hj hi, rename hh hj,
  all_goals
  { have := mem_unique hy hj, subst this,
    exact hi }
end

noncomputable def approx_chain : chain (Π a, roption $ β a) :=
begin
  refine ⟨ approx f, _ ⟩,
  apply approx_mono,
end

lemma le_f_of_mem_approx {x} (hx : x ∈ approx_chain f) : x ≤ f x :=
begin
  revert hx, simp [approx_chain,stream.mem_def],
  intros i hx, subst x,
  apply approx_mono' f
end

lemma f_mem_approx_chain {x} (hx : x ∈ approx_chain f) : f x ∈ approx_chain f :=
begin
  revert hx, simp [approx_chain,stream.mem_def],
  intros i hx, subst hx, exact ⟨i.succ,rfl⟩
end

lemma approx_mem_approx_chain {i} : approx f i ∈ approx_chain f :=
stream.mem_of_nth_eq rfl

end fix

namespace pi

open fix

variables {α} {β : α → Type*}
open lattice (order_bot) complete_partial_order

variables (f : (Π a, roption $ β a) →ₘ (Π a, roption $ β a)) -- (hf : monotone f)

-- include hf

open roption (hiding Sup) nat
open nat.up complete_partial_order

lemma fix_eq_Sup : fix f = Sup (approx_chain f) :=
begin
  apply le_antisymm,
  { intro x, cases min_fix f x with i hx,
    transitivity' approx f i.succ x,
    { transitivity', apply hx, apply approx_mono' f },
    apply le_Sup _ _ _, dsimp [approx],
    rw chain.mem_map_iff,
    refine ⟨approx f i.succ,_,rfl⟩,
    apply approx_mem_approx_chain },
  { apply Sup_le _ _ _,
    simp [mem_map_iff,approx_chain,stream.mem_def],
    intros y x, revert y, simp, apply max_fix f },
end

lemma fix_le {X : Π a, roption $ β a} (hX : f X ≤ X) : fix f ≤ X :=
begin
  rw fix_eq_Sup f,
  apply Sup_le _ _ _,
  simp [approx_chain,stream.mem_def,stream.nth],
  intros y i, revert y, simp,
  induction i, apply bot_le _,
  transitivity' f X, apply f.mono i_ih,
  apply hX
end

variables {f} (hc : continuous f)
include hc

lemma fix_eq : fix f = f (fix f) :=
begin
  rw [fix_eq_Sup f,hc],
  apply le_antisymm,
  { apply Sup_le_Sup_of_le _,
    intros x hx, existsi [f x,chain.mem_map _ f _ hx],
    apply le_f_of_mem_approx _ hx },
  { apply Sup_le_Sup_of_le _,
    intros x hx, rw chain.mem_map_iff at hx,
    rcases hx with ⟨y,h₀,h₁⟩, refine ⟨x,_,le_refl _⟩,
    rw ← h₁, apply f_mem_approx_chain _ h₀ }
end

end pi

class has_fix (α : Type*) :=
(fix : (α → α) → α)

open has_fix complete_partial_order

class lawful_fix (α : Type*) -- {arg : out_param $ Type*} (res : out_param $ arg → Type*)
  [has_fix α] [complete_partial_order α] :=
(fix_eq : ∀ {f : α →ₘ α}, continuous f → fix f = f (fix f))

namespace roption

variables {m : Type u_1 → Type*} [has_fix (unit → m α)]

def to_unit (f : α → α) (x : unit → α) (_ : unit) : α := f (x ())

instance [preorder α] {f : α →ₘ α} : is_monotone (to_unit f) :=
⟨ λ x y h i, @Mono.mono α α _ _ f (x ()) (y ()) (h ()) ⟩

def to_unit' [preorder α] (f : α →ₘ α) : (unit → α) →ₘ (unit → α) := Mono.mk' (to_unit f)

lemma to_unit_to_mono [preorder α] (f : α →ₘ α) : to_unit f = to_unit' f := rfl

instance : has_fix (m α) :=
⟨ λ f, has_fix.fix (to_unit f) () ⟩

variables [complete_partial_order (m α)] [lawful_fix (unit → m α)]

def to_unit_mono (f : m α → m α) (hm : monotone f) : monotone (to_unit f) :=
λ x y h a, hm $ by exact h ()

def to_unit_cont (f : m α →ₘ m α) : Π hc : continuous f, continuous (to_unit' f)
| hc := by { intro c, ext : 1, dsimp [to_unit',to_unit,complete_partial_order.Sup], erw [hc _,chain.map_comp] }

instance : lawful_fix (m α) :=
⟨ λ f hc, by { dsimp [fix], have hc' := to_unit_cont f hc,
              conv { to_lhs, rw [to_unit_to_mono,lawful_fix.fix_eq hc'] }, refl } ⟩

end roption

namespace pi

instance roption.has_fix {β : α → Type*} : has_fix (Π x, roption $ β x) :=
⟨ fix.fix ⟩

noncomputable instance {β : α → Type*} : lawful_fix (Π x, roption $ β x) :=
⟨ λ f hc, by { dsimp [fix], conv { to_lhs, rw [fix_eq hc], } } ⟩

variables {β : α → Type*} {γ : Π a : α, β a → Type*}

open function
instance [has_fix (Π x : sigma β, γ x.1 x.2)] : has_fix (Π x (y : β x), γ x y) :=
⟨ λ f, curry' (fix $ uncurry' ∘ f ∘ curry') ⟩


section monotone

variables [∀ x y, preorder $ γ x y]
variables f : (Π x (y : β x), γ x y) →ₘ (Π x (y : β x), γ x y)

-- variables {f} (hm : monotone f)
-- include hm

-- lemma uncurry_mono : monotone $ uncurry' ∘ f ∘ curry' :=
-- monotone_comp (monotone_comp (monotone_curry' α β γ) hm)
--               (monotone_uncurry' α β γ)

end monotone

section continuous

variables [∀ x y, complete_partial_order $ γ x y]
variables f : (Π x (y : β x), γ x y) →ₘ (Π x (y : β x), γ x y)
variables (hc : continuous f)
include hc

lemma uncurry_cont : continuous (Mono.uncurry γ ∘ f ∘ Mono.curry γ) :=
continuous_comp _ _ continuous_curry (continuous_comp _ _ hc (continuous_uncurry'' _ _ _))

end continuous

variables [∀ x y, complete_partial_order $ γ x y]

instance pi.lawful_fix' [has_fix $ Π x : sigma β, γ x.1 x.2] [lawful_fix $ Π x : sigma β, γ x.1 x.2] : lawful_fix (Π x y, γ x y) :=
⟨ λ f hc, by {
  dsimp [fix], conv { to_lhs, rw [lawful_fix.fix_eq (uncurry_cont f hc) ] }, refl, } ⟩

end pi
