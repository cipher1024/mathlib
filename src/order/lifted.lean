/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon

Orders lifted through a functor
-/

import order.complete_partial_order

variables (F : Type* → Type*)

class preorder1 :=
(to_preorder : ∀ {α} [preorder α], preorder (F α))

attribute [instance] preorder1.to_preorder

meta def prove_comm_diag : tactic unit := `[intros; refl]

class partial_order1 extends preorder1 F :=
(to_partial_order' : ∀ {α}, partial_order α → partial_order (F α))
(poset_commutes : ∀ {α} (h : partial_order α), @partial_order.to_preorder _ (to_partial_order' h) = to_preorder . prove_comm_diag)

instance partial_order1.to_partial_order {α} [h : partial_order α] [partial_order1 F] : partial_order (F α) :=
{ le_antisymm := λ a b, (@partial_order1.poset_commutes F _ α h ▸ @partial_order.le_antisymm (F α) (partial_order1.to_partial_order' F _) a b : a ≤ b → b ≤ a → a = b),
  .. preorder1.to_preorder F }

class complete_partial_order1 extends partial_order1 F :=
(to_complete_partial_order' : ∀ {α}, complete_partial_order α → complete_partial_order (F α))
(cpo_commutes : ∀ {α} (h : complete_partial_order α), @complete_partial_order.to_partial_order _ (to_complete_partial_order' h) = partial_order1.to_partial_order F . prove_comm_diag)

instance complete_partial_order1.to_complete_partial_order {α} [h : complete_partial_order α] [complete_partial_order1 F] : complete_partial_order (F α) :=
{ Sup := λ c, (by { have := @complete_partial_order.Sup (F α) (complete_partial_order1.to_complete_partial_order' F h),
                    rw complete_partial_order1.cpo_commutes at this, exact this c } : F α),
  Sup_le' := by { have := complete_partial_order1.cpo_commutes F h, dsimp [partial_order1.to_partial_order] at *,
                  introv hc,
                  have h₁ := @complete_partial_order.Sup_le' (F α) (complete_partial_order1.to_complete_partial_order' F h) (cast _ c) x (cast _ hc),
                  swap, { congr, rw this },
                  swap, { apply iff.to_eq, apply forall_congr, intro, congr', rw this, rw this, cc },
                  revert h₁, apply iff.mp,
                  congr', h_generalize hp : c == p, h_generalize hq : _ == q,
                  clear_except this h₀ hp hq, revert p q c,  rw [← this], intros, cases hp, cases hq, refl },
  le_Sup' := by { have := complete_partial_order1.cpo_commutes F h, dsimp [partial_order1.to_partial_order] at *,
                  introv,
                  have h₁ := @complete_partial_order.le_Sup' (F α) (complete_partial_order1.to_complete_partial_order' F h) (cast _ c) i,
                  swap, { congr, rw this },
                  revert h₁, apply iff.mp,
                  congr'; h_generalize hp : c == p, cc, h_generalize hq : _ == q,
                  clear_except this h₀ hp hq, revert p q c,  rw [← this], intros, cases hp, cases hq, refl },
  .. partial_order1.to_partial_order F }
