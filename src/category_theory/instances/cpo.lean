
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

The category of complete partial orders
-/
import category_theory.concrete_category
import category_theory.isomorphism
import category_theory.products
import order.complete_partial_order

open category_theory complete_partial_order

namespace category_theory.instances

@[reducible] def CPO : Type* := bundled complete_partial_order

instance complete_partial_order_unbundled (x : CPO) : complete_partial_order x := x.str

namespace complete_partial_order

instance concrete_category_continuous : concrete_category @continuous' := ⟨@continuous_id', @continuous_comp' ⟩

def of (X : Type*) [complete_partial_order X] : CPO := ⟨X, by apply_instance⟩

def discrete : Type* ⥤ CPO :=
{ obj := λ X, ⟨X, discrete.complete_partial_order _⟩,
  map := λ X Y f, ⟨f, discrete.continuous_of _⟩ }

lemma monotone_map {X Y} (f : X → Y) : monotone (roption.map f) :=
by { intros x y h a, simp only [roption.mem_map_iff],
     apply exists_imp_exists, intro b, simp,
     intros hx hf, exact ⟨h _ hx,hf⟩,  }

lemma continuous_map {X Y} (f : X → Y) : continuous' (roption.map f) :=
⟨ monotone_map f,
 by { intro c, apply le_antisymm,
      { apply le_Sup _ _ _, apply chain.mem_map, apply roption.Sup_mem_self },
      { apply Sup_le _ _ _, simp [chain.mem_map_iff], introv hx hy, subst y,
        apply monotone_map f, apply le_Sup _ _ hx } } ⟩

namespace prod

variables {X₀ : Type*} {X₁ : Type*} {Y₀ : Type*} {Y₁ : Type*}
          {f : X₀ → Y₀} {g : X₁ → Y₁}

section mono

variables [preorder X₀] [preorder X₁]
          [preorder Y₀] [preorder Y₁]

lemma monotone_map (hf : monotone f) (hg : monotone g) : monotone (prod.map f g) :=
λ ⟨x,_⟩ ⟨y,_⟩ h, ⟨hf h.1, hg h.2⟩

end mono

variables [complete_partial_order X₀] [complete_partial_order X₁]
          [complete_partial_order Y₀] [complete_partial_order Y₁]

lemma continuous_map : continuous' f → continuous' g → continuous' (prod.map f g)
| ⟨hf,hf'⟩ ⟨hg,hg'⟩ :=
⟨ monotone_map hf hg, λ c,
  by simp [Sup,chain.map_comp,hf' _,hg' _] ⟩

end prod

noncomputable def roption : CPO ⥤ CPO :=
{ obj := λ X, ⟨roption X, by apply_instance⟩,
  map := λ X Y f, ⟨roption.map f.1, continuous_map f⟩,
  map_id' := λ X, by { congr; ext : 1, apply roption.map_id', intro, refl },
  map_comp' := by { intros, congr } }

def prod : CPO × CPO ⥤ CPO :=
{ obj := λ X, ⟨X.1 × X.2, by apply_instance ⟩,
  map := λ X Y F, ⟨prod.map _ _,prod.continuous_map F.1.2 F.2.2⟩,
  map_id' := by { intros, congr, rw prod.map_def, ext; refl },
  map_comp' := by { intros, congr, simp [(∘),prod.map], ext ⟨x,y⟩; refl, },  }

noncomputable def roption_prod {X Y : CPO} : roption.obj (prod.obj (X, Y)) ≅ prod.obj (roption.obj X, roption.obj Y) :=
{ hom := ⟨λ X, (roption.map prod.fst X, roption.map prod.snd X), _⟩,
  inv := ⟨λ X : _root_.roption _ × _, prod.mk <$> X.1 <*> X.2, _⟩,
  hom_inv_id' := _,
  inv_hom_id' := _ }

end complete_partial_order

end category_theory.instances
