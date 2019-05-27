
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon

Monads with monotone and continuous operators
-/

import order.basic
import order.lifted
import order.complete_partial_order

-- set_option old_structure_cmd true

universes u v
open functor has_seq

variables (F : Type u → Type v)

-- /--

-- -/
-- class functor_monotone [functor F] [preorder1 F]
-- extends is_lawful_functor F :=
-- (monotone_map : ∀ {α β} [preorder α] [preorder β] (f : α → β), monotone f → monotone (map f : F α → F β))

def liftP [functor F] {α} (p : α → Prop) (x : F α) : Prop :=
∃ y : F (subtype p), x = subtype.val <$> y

section monotoneF

variables {F}

variables {α β : Type u} [preorder α] [preorder β]

def monotoneF [functor F] (x : F (α → β)) :=
∃ y : F (subtype $ @monotone α β _ _), x = subtype.val <$> y

lemma monotoneF_pure [applicative F] [is_lawful_applicative F] {x : α → β} (h : monotone x) :
  monotoneF (pure x : F _) :=
⟨pure $ subtype.mk x h, by rw map_pure⟩

end monotoneF

-- /--

-- -/
-- class applicative_monotone [applicative F] [preorder1 F]
-- extends is_lawful_applicative F :=
-- (monotone_pure' : ∀ {α} [preorder α], monotone (λ x, pure $ x : α → F α))
-- (monotone_seq_left : ∀ {α β : Type u} [preorder α] [preorder β], monotone (seq : F (α → β) → F α → F β))
-- (monotone_seq_right : ∀ {α β : Type u} [preorder α] [preorder β] (f : F $ α → β), monotoneF f → monotone (seq f))
-- -- (monotone_map := λ α β _ _ f hf x y h, by { rw [← pure_seq_eq_map,← pure_seq_eq_map],
-- --                                             apply monotone_seq_right _ _ h, apply monotoneF_pure hf,
-- --                                             apply_instance })


-- namespace applicative_monotone

-- variables [applicative F] [preorder1 F] [applicative_monotone F]

-- -- local attribute [instance] applicative_monotone.mono

-- instance to_functor_monotone : functor_monotone F :=
-- { -- to_is_lawful_functor := is_lawful_applicative.to_is_lawful_functor F,
--   monotone_map := by { introv hf, intros x y h, resetI,
--                        have := pure_seq_eq_map f x,
--                         rw [← pure_seq_eq_map f x,← pure_seq_eq_map f y],
--                        apply monotone_seq_right _ _, exact h, apply_instance,
--                        apply monotoneF_pure, exact hf },
--   .. is_lawful_applicative.to_is_lawful_functor F }

-- variables {α : Type*} {β : Type u} [preorder α] [preorder β]
-- variables {f : α → β}

-- -- local attribute [instance] functor_monotone.mono

-- lemma monotone_pure (hf : monotone f) :
--   monotone (λ x, pure (f x) : α → F β) :=
-- monotone_comp hf (monotone_pure' _)

-- end applicative_monotone

-- open applicative_monotone

-- -- namespace monad_monotone

-- -- variables [monad F] [is_lawful_monad F]
-- -- variables {α β γ : Type u} [preorder α] [preorder β] [preorder γ] [preorder (F α)] [preorder (F β)] [preorder (F γ)]
-- -- variables monotone_bind : ∀ (x : α → F β) (f : α → β → F γ),
-- --                monotone x →
-- --                monotone f →
-- --                (∀ x, monotone $ f x) →
-- --                monotone (λ a, x a >>= f a)

-- -- lemma monotone_map (f : α → β) : monotone f → monotone (map f : F α → F β) := _

-- -- end monad_monotone


-- /--

-- -/
-- class monad_monotone [monad F]
-- extends is_lawful_monad F, preorder1 F :=
-- -- (mono : ∀ α [preorder α], preorder (F α))
-- (monotone_pure' : ∀ {α} [preorder α], monotone (pure : α → F α))
-- -- (monotone_bind_left : ∀ {α β} [preorder α] [preorder β], monotone (bind : F α → (α → F β) → F β))
-- -- (monotone_bind_right : ∀ {α β} [preorder α] [preorder β] (x : F α), monotone (bind x : (α → F β) → F β))
-- -- (monotone_bind_left : ∀ {α β} [preorder α] [preorder β] (f : α → F β), monotone f → monotone (λ x : F α, x >>= f))
-- -- (monotone_bind_right : ∀ {α β} [preorder α] [preorder β] (x : F α), monotone (bind x : (α → F β) → F β))
-- (monotone_bind_left : ∀ {α β} [preorder α] [preorder β] (f : α → F β),
--                -- monotone x →
--                monotone f → -- (∀ x, monotone $ f x) →
--                monotone (λ x : F α, x >>= f))
-- (monotone_bind_right : ∀ {α β} [preorder α] [preorder β] (x : F α),
--                -- monotone x →
--                -- monotone f → -- (∀ x, monotone $ f x) →
--                monotone (λ f : α → F β, x >>= f))
-- -- (monotone_map := by { -- clear_except a monotone_bind monotone_pure,
-- --                       introv hf a' hab,
-- --                       -- letI := (@mono β _inst_2_1),
-- --                       simp only with monad_norm, apply monotone_bind _ _ _ _ _ hab,
-- --                       apply_instance, apply monotone_id, change monotone (λ _, (pure ∘ f : α → F β)),
-- --                       apply monotone_const _, intro, refine @monotone_pure F _ _ _ _ _ _ _ f _ , })
-- -- (monotone_seq_left := λ α β _ _ x y h b, by { simp with monad_norm, apply monotone_bind _ _ _ _ _ h,
-- --                                               apply_instance, apply monotone_id, apply monotone_const _, intro,
-- --                                               apply monotone_comp,  apply pi.monotone_lambda,
-- -- intros a b h, apply monotone_pure _ _ ,
-- --                                               apply monotone_bind_right b })
-- -- (monotone_seq_right := λ α β _ _ f h x y h',
-- --   by { cases h with f' h, rw ← h, simp only with monad_norm,
-- --        apply monotone_bind_right _, rintro ⟨f',hf'⟩,
-- --        dsimp, apply monotone_bind_left _ _ h', apply monotone_comp hf',
-- --        apply monotone_pure, apply subtype.preorder })

-- open complete_partial_order

-- namespace monad_monotone

-- variables [monad F] [monad_monotone F]

-- -- local attribute [instance] monad_monotone.mono

-- variables {α : Type*} {β γ : Type u} [preorder α] [preorder β] [preorder γ]
-- variables {f : α → β}

-- lemma monotone_pure (hf : monotone f) :
--   monotone (λ x, pure (f x) : α → F β) :=
-- monotone_comp hf (monotone_pure' _)

-- lemma monotone_bind {f : α → F β} {g : α → β → F γ}
--   (hf : monotone f) (hg : monotone g) (hg' : ∀ x, monotone $ g x) :
--   monotone (λ x, f x >>= g x) :=
-- begin
--   intros a b h, dsimp, transitivity' f a >>= g b,
--   { apply monotone_bind_right (f a), apply hg h },
--   { apply monotone_bind_left _ (hg' b) (hf h) }
-- end

-- instance : applicative_monotone F :=
-- { monotone_pure' := @monad_monotone.monotone_pure' F _ _,
--   monotone_seq_right := by { introv hf, intros x y h, cases hf, rw ← hf_h,
--                              resetI, simp with monad_norm,
--                              apply monotone_bind_right, intro a,
--                              apply monotone_bind_left _ _ h, apply monotone_pure _ a.property, },
--   monotone_seq_left := by { introv hf, intros x y h z,
--                             resetI, simp with monad_norm, apply monotone_bind_left _ _ h,
--                             intros a b h, apply monotone_bind_right _, intro c,
--                             dsimp, apply monotone_pure' _ (h c), apply_instance } }

-- instance : functor_monotone F :=
-- applicative_monotone.to_functor_monotone F

-- end monad_monotone

-- set_option old_structure_cmd true

open complete_partial_order

def adm {α} [complete_partial_order α] (P : α → Prop) :=
∀ c : chain α, (∀ x ∈ c, P x) → P (Sup c)

/--

-/
class functor_continuous [functor F]
extends complete_partial_order1 F,
        is_lawful_functor F :=
-- (admissible_liftP {α} [complete_partial_order α] (P : α → Prop) : adm (liftP F P))
(monotone_map {α β} [preorder α] [preorder β] (f : α → β) : monotone f → monotone (map f : F α → F β))
(continuous_map {α β} [complete_partial_order α] [complete_partial_order β]
                          -- [complete_partial_order $ F α] [complete_partial_order $ F β]
  (f : α → β) :
  continuous' f → continuous' (map f : F α → F β))

class liftP_Sup_preservation [functor F] [complete_partial_order1 F] :=
(admissible_liftP {α} [complete_partial_order α] (P : α → Prop) : adm P → adm (liftP F P))

section continuousF

-- variables {F}
variables (α β : Type u) [complete_partial_order α] [complete_partial_order β]

@[reducible]
def continuousF [functor F] : F (α → β) → Prop :=
liftP F (@continuous' α β _ _)
-- ∃ y : F (subtype $ @continuous' α β _ _), x = subtype.val <$> y

variables {α β}

lemma continuousF_pure [applicative F] [is_lawful_applicative F] {x : α → β} (h : continuous' x) :
  continuousF F _ _ (pure x : F _) :=
⟨pure $ subtype.mk x h,by rw map_pure⟩

end continuousF

namespace subtype

variables {α β : Type u} (P : α → Prop)

-- open complete_partial_order

-- variables [functor F] [preorder α] [preorder β] [preorder1 F]
-- -- set_option pp.implicit true

-- section

-- -- variables c :
-- --   @chain (@subtype (F (α → β)) (@continuousF F α β _inst_2 _inst_3 _inst_1))
-- --     (@partial_order.to_preorder (@subtype (F (α → β)) (@continuousF F α β _inst_2 _inst_3 _inst_1))
-- --        (@subtype.partial_order (F (α → β))
-- --           (@partial_order1.to_partial_order F (α → β)
-- --              (@to_partial_order (α → β) (@pi.complete_partial_order α (λ (a : α), β) (λ (a : α), _inst_3)))
-- --              (@complete_partial_order1.to_partial_order1 F _inst_4))
-- --           (@continuousF F α β _inst_2 _inst_3 _inst_1)))
-- -- include c
-- variables P : F (α → β) → Prop

-- def map_val (c : chain (subtype P)) : chain (F $ α → β) :=
-- c.map _ (monotone_val _)

-- -- begin
-- --   convert chain.map c subtype.val (monotone_val _), clear c,
-- -- rw complete_partial_order1.cpo_commutes,
-- -- rw partial_order1.poset_commutes,
-- -- rw complete_partial_order1.cpo_commutes,
-- -- end


-- end

variables [complete_partial_order α]
          [complete_partial_order β]
          -- [complete_partial_order1 F]


-- instance pi.partial_order' {ι : Prop} {α : ι → Type v} [∀i, partial_order (α i)] : partial_order (Πi, α i) :=
-- { le_antisymm := λf g h1 h2, funext (λb, le_antisymm (h1 b) (h2 b)),
--   ..pi.preorder' }

-- _inst_2 : complete_partial_order α,
-- _inst_3 : complete_partial_order β,
-- _inst_4 : complete_partial_order1 F,
-- c :
--   @chain (@subtype (F (α → β)) (@continuousF F α β _inst_2 _inst_3 _inst_1))
--     (@partial_order.to_preorder (@subtype (F (α → β)) (@continuousF F α β _inst_2 _inst_3 _inst_1))
--        (@subtype.partial_order (F (α → β))
--           (@partial_order1.to_partial_order F (α → β)
--              (@to_partial_order (α → β) (@pi.complete_partial_order α (λ (a : α), β) (λ (a : α), _inst_3)))
--              (@complete_partial_order1.to_partial_order1 F _inst_4))
--           (@continuousF F α β _inst_2 _inst_3 _inst_1)))
-- ⊢ @chain (F (α → β))
--     (@partial_order.to_preorder (F (α → β))
--        (@to_partial_order (F (α → β))
--           (@complete_partial_order1.to_complete_partial_order F (α → β)
--              (@pi.complete_partial_order α (λ (a : α), β) (λ (a : α), _inst_3))
--              _inst_4)))

-- set_option pp.implicit true

variables [functor F]
-- variables (c : chain { f : F (α → β) // continuousF f })

-- #check @chain.map

-- protected def Sup : F (α → β) :=
-- Sup $ @chain.map { f : F (α → β) // continuousF f } (F (α → β)) _ (@partial_order.to_preorder _ _) c
-- subtype.val (@monotone_val _ _ (@partial_order.to_preorder _ _))

-- lemma continuousF_Sup : continuousF (subtype.Sup F c) :=
-- ⟨_,_⟩

-- instance : complete_partial_order { f : F (α → β) // continuousF f } :=
-- { Sup     := λ c, ⟨subtype.Sup _ c, continuousF_Sup F c⟩,
--   Sup_le' := _,
--   le_Sup' := _ }

variables hP : adm P

protected def complete_partial_order_of_adm : complete_partial_order (subtype P) :=
{ Sup     := λ c, ⟨ Sup $ c.map _ monotone_val, hP _ $ λ x hc,
                   Exists.rec_on (chain.exists_of_mem_map c monotone_val hc) $
                   λ w ⟨h,h'⟩, h' ▸ w.property ⟩,
  Sup_le' := λ c h h', Sup_le' _ _ h',
  le_Sup' := λ c, le_Sup' (c.map _ monotone_val) }

#check zip_with_flip

lemma adm_continuous : adm $ @continuous' α β _ _ :=
assume c (hc : ∀ (x : α → β), x ∈ c → continuous' x),
-- by { dsimp [Sup], }
⟨λ a b (h : a ≤ b), Sup_le_Sup_of_le (chain.map_le_map _ _ _ $ λ f hf, (hc _ hf).fst h),
 λ c', by { dsimp [Sup],
            let app : α → (α → β) → β := λ x f, f x,
            let app' : {x // x ∈ c} → α → β := subtype.val,
            rw chain.map_eq_attach_map c, dsimp [(∘)],
            change Sup (chain.map c.attach (λ f, app' f (Sup c')) _) =
                   Sup (chain.map c' (λ (a : α), Sup (chain.map c (λ (f : α → β), app a f) _)) _),
            erw [← Sup_zip app' _ c.attach c',zip_with_flip app',Sup_zip' _ _ _ _ _]; dsimp [flip,app',app], refl,
            { rintros ⟨x,x'⟩ ⟨y,y'⟩ h, dsimp [function.uncurry],
              transitivity y' x, },
            { intros, apply pi.continuous_congr' } }⟩

instance : complete_partial_order { f : α → β // continuous' f } :=
subtype.complete_partial_order_of_adm _ $
adm_continuous

instance liftP.complete_partial_order [complete_partial_order1 F] [liftP_Sup_preservation F] : complete_partial_order { f : F (α → β) // continuousF F _ _ f } :=
subtype.complete_partial_order_of_adm _ $
liftP_Sup_preservation.admissible_liftP F _ adm_continuous

-- functor_continuous.admissible_liftP F _ x _

end subtype

-- set_option pp.implicit true
-- set_option old_structure_cmd true

/--

-/
class applicative_continuous [applicative F] -- [complete_partial_order1 F]
extends complete_partial_order1 F,
        is_lawful_applicative F,
        liftP_Sup_preservation F :=
-- [Sup_preservation : liftP_Sup_preservation F]
-- [cpo : ∀ α [complete_partial_order α], complete_partial_order (F α)]
(monotone_pure' {α} [preorder α] : monotone (λ x, pure $ x : α → F α))
(monotone_seq_left {α β : Type u} [preorder α] [preorder β] :
  monotone (seq : F (α → β) → F α → F β))
(monotone_seq_right {α β : Type u} [preorder α] [preorder β] (f : F $ α → β) :
  monotoneF f → monotone (seq f))
(continuous_pure' {α} [complete_partial_order α] :
  continuous' (pure : α → F α))
-- (continuous_seq_left : ∀ {α β : Type u} [complete_partial_order α] [complete_partial_order β],
--   continuous' (seq : F (α → β) → F α → F β))
(continuous_seq_left {α β : Type u}
  [complete_partial_order α] [complete_partial_order β] :
  -- [complete_partial_order $ F α] [complete_partial_order $ F β] :
  -- (f : ι → F (α → β)), (∀ i, continuousF $ f i) →
  continuous' (λ (x : { f // continuousF F α β f }), seq (subtype.val x)))
(continuous_seq_right {α β : Type u}
  [complete_partial_order α] [complete_partial_order β]
  -- [complete_partial_order (F α)] [complete_partial_order (F β)]
  (f : F $ α → β) :
  continuousF F _ _ f → continuous' (seq f))
-- (continuous_map := by { introv hf,
--                         suffices : continuous' (λ (x : F α), pure f <*> x),
--                         { revert this, apply iff.mp, congr', ext, simp only with functor_norm },
--                         apply continuous_seq_right, apply continuousF_pure hf, apply_instance })

-- #check @continuousF

namespace applicative_continuous

-- attribute [instance] applicative_continuous.cpo

variables [applicative F] [applicative_continuous F]
variables {α : Type u} {β : Type u}
          {f : α → β}

lemma monotone_map [preorder α] [preorder β] (f : α → β) :
    monotone f → monotone (map f : F α → F β) :=
by { introv hf, intros a b h, rw ← applicative.pure_seq_eq_map',
     apply monotone_seq_right _ _ h, apply monotoneF_pure hf,
     apply_instance }

variables [complete_partial_order α] [complete_partial_order β]
          (hf : continuous' f)

lemma continuous_pure : continuous' (λ x, pure (f x) : α → F β) :=
continuous_comp' _ _ (continuous_pure' _) hf

lemma continuous_map (f : α → β) :
    continuous' f → continuous' (map f : F α → F β) :=
by { introv hf, resetI,
     suffices : continuous' (λ (x : F α), pure f <*> x),
     { revert this, apply iff.mp, congr', ext, simp only with functor_norm },
     apply continuous_seq_right, apply continuousF_pure _ hf, apply_instance }

instance : functor_continuous F :=
{ to_complete_partial_order1 := applicative_continuous.to_complete_partial_order1 F,
  monotone_map := @monotone_map F _ _ ,
  continuous_map := @continuous_map F  _ _
 }

end applicative_continuous

set_option old_structure_cmd false

/--

-/
class monad_continuous [monad F]
extends is_lawful_monad F,
        complete_partial_order1 F,
        liftP_Sup_preservation F :=
(monotone_pure' : ∀ {α} [preorder α], monotone (pure : α → F α))
(monotone_bind_left : ∀ {α β} [preorder α] [preorder β] (f : α → F β),
               monotone f →
               monotone (λ x : F α, x >>= f))
(monotone_bind_right : ∀ {α β} [preorder α] [preorder β] (x : F α),
               monotone (λ f : α → F β, x >>= f))
(continuous_pure' : ∀ {α} [complete_partial_order α], continuous' (pure : α → F α))
(continuous_bind_left : ∀ {α β} [complete_partial_order α] [complete_partial_order β] (f : α → F β),
  continuous' f → continuous' (λ x : F α, x >>= f))
(continuous_bind_right : ∀ {α β} [complete_partial_order α] [complete_partial_order β] (x : F α),
  continuous' (bind x : (α → F β) → F β))
-- (continuous_bind' {α β}
--   [complete_partial_order α] [complete_partial_order β]
--   -- {f : F α}
--   {g : F α → α → F β}
--   -- (hf : continuous' f)
--   (hg : continuous' g) (hg' : ∀ x, continuous' $ g x) :
--   continuous' (λ x : F α, x >>= g x))
-- (continuous_map := by { clear_except a continuous_bind_left continuous_pure, introv hf,
--                         suffices : continuous' (λ x : F α, x >>= λ a, pure $ f a),
--                         { revert this, apply iff.mp, congr', ext, simp only with monad_norm },
--                         apply continuous_bind_left, refine continuous_comp' pure _ continuous_pure hf, })
-- (continuous_seq_left := by { intros, apply pi.continuous_ext, intro X,
--                              suffices : continuous' (λ (y : F $ α → β), y >>= λ f, X >>= λ a, pure $ f a),
--                              { revert this, apply iff.mp, congr', ext, simp with monad_norm },
--                              apply continuous_bind_left, apply continuous_comp' (bind X) (λ f, pure ∘ f),
--                              apply continuous_bind_right X, apply pi.continuous_ext, intro Y,
--                              apply continuous_comp', apply continuous_pure,
--                              apply pi.continuous_congr' })
-- (continuous_seq_right :=
--   by { clear_except _inst_2 continuous_bind_right, introv h,
--        suffices : continuous' (λ x, f >>= λ g, x >>= pure ∘ g),
--        { revert this, apply iff.mp, congr', ext, simp [seq_eq_bind_map] with monad_norm },
--        apply continuous_bind_right,
--        done,
--        cases h with f' h, rw ← h, simp only with monad_norm,
--        apply monotone_bind_right _, rintro ⟨f',hf'⟩,
--        dsimp, apply monotone_bind_left h', apply subtype.preorder })

namespace monad_continuous

-- attribute [instance] monad_continuous.cpo

variables [monad F] [monad_continuous F]
variables {α β γ : Type u}

section monotone

variables [preorder α] [preorder β] [preorder γ]

lemma monotone_bind {f : α → F β} {g : α → β → F γ}
  (hf : monotone f) (hg : monotone g) (hg' : ∀ x, monotone $ g x) :
  monotone (λ x, f x >>= g x) :=
begin
  intros a b h, dsimp,
  transitivity' f a >>= g b,
  apply monotone_bind_right _ (hg h),
  apply monotone_bind_left _ (hg' _) (hf h),
end

end monotone

variables [complete_partial_order α]
          [complete_partial_order β]
          [complete_partial_order γ]

lemma continuous_pure {f : α → β} (hf : continuous' f) :
  continuous' (λ x, pure (f x) : α → F β) :=
continuous_comp' _ _ (continuous_pure' _) hf

-- set_option pp.implicit true
open complete_partial_order

lemma continuous_bind {α} [complete_partial_order α] {f : α → F β} {g : α → β → F γ}
  (hf : continuous' f) (hg : continuous' g) (hg' : ∀ x, continuous' $ g x) :
  continuous' (λ x, f x >>= g x) :=
begin
  show continuous' (split (λ x y, f x >>= g y)),
  apply continuous_split,
  { apply pi.continuous_ext, intro a,
    show continuous' ((λ x : F β, x >>= g a) ∘ f),
    apply continuous_comp' _ _ _ hf,
    apply continuous_bind_left,
    apply hg' _ },
  { apply pi.continuous_ext, intro a, dsimp [flip],
    show continuous' ((λ x, f a >>= x) ∘ g),
    apply continuous_comp' _ _ _, apply hg,
    apply continuous_bind_right },
end

noncomputable def with_subtype (g : {f // continuousF F α β f}) : F (subtype $ @continuous' α β _ _) :=
classical.some g.property

lemma with_subtype_intro : ∀ g : {f // continuousF F α β f}, g.val = subtype.val <$> with_subtype _ g
| ⟨g,h⟩ := classical.some_spec h

instance : applicative_continuous F :=
{ -- cpo := monad_continuous.cpo F,
  monotone_pure' := @monotone_pure' F _ _,
  continuous_pure' := @continuous_pure' F _ _,
  continuous_seq_left := by { intros, apply pi.continuous_ext, intros,
                              -- have := @seq_eq_bind_map α β F _ _ x,
                              simp [with_subtype_intro] with monad_norm,
                              -- -- apply continuous_bind_left,
                              -- dsimp [continuousF] at a,
                              -- rw classical.skolem at a,
                              -- cases a with ff hh,
                              -- simp [hh] with monad_norm,

                              apply continuous_bind _ ,
                              -- { apply cont_const' },
                              -- { apply pi.continuous_ext, intro, apply continuous_pure,
                              --   split, intro, dsimp [Sup], refl },
                              -- { intro, apply continuous_pure, },
 },
  monotone_seq_right := _,
  monotone_seq_left := _,
  continuous_seq_right := _,
  continuous_seq_left := _  }

-- instance : functor_continuous F :=
-- applicative_continuous.functor_continuous F

end monad_continuous


namespace roption

-- instance : functor_monotone roption := _
-- instance : applicative_monotone roption := _
-- instance : monad_monotone roption := _

-- instance : functor_continuous roption := _
-- instance : applicative_continuous roption := _
instance : monad_continuous roption := _

end roption

namespace option



end option

namespace option_t



end option_t

namespace sum



end sum

namespace except_t



end except_t

namespace state_t



end state_t

namespace reader_t



end reader_t

namespace cont_t



end cont_t
