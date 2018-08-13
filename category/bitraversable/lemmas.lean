import category.bitraversable.basic

universes u

variables {t : Type u → Type u → Type u} [bitraversable t]
variables {β : Type u}

namespace bitraversable
open functor is_lawful_applicative
variables {F G : Type u → Type u}
          [applicative F] [applicative G]

@[reducible]
def tfirst {α α'} (f : α → F α') : t α β → F (t α' β) :=
bitraverse f pure

@[reducible]
def tsecond {α α'} (f : α → F α') : t β α → F (t β α') :=
bitraverse pure f

variables [is_lawful_bitraversable t]
          [is_lawful_applicative F]
          [is_lawful_applicative G]

@[higher_order tfirst_id]
lemma id_tfirst : Π {α β} (x : t α β), tfirst id.mk x = id.mk x :=
@id_bitraverse _ _ _

@[higher_order tsecond_id]
lemma id_tsecond : Π {α β} (x : t α β), tsecond id.mk x = id.mk x :=
@id_bitraverse _ _ _

@[higher_order tfirst_comp_tfirst]
lemma comp_tfirst {α₀ α₁ α₂ β}
  (f : α₀ → F α₁) (f' : α₁ → G α₂) (x : t α₀ β) :
  comp.mk (tfirst f' <$> tfirst f x) = tfirst (comp.mk ∘ map f' ∘ f) x :=
by simp [tfirst,comp_bitraverse,map_comp_pure,has_pure.pure]

@[higher_order tfirst_comp_tsecond]
lemma tfirst_tsecond {α₀ α₁ β₀ β₁}
  (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
  comp.mk (tfirst f <$> tsecond f' x) =
  bitraverse (comp.mk ∘ pure ∘ f) (comp.mk ∘ map pure ∘ f') x :=
by simp [tfirst,tsecond,comp_bitraverse]

@[higher_order tsecond_comp_tfirst]
lemma tsecond_tfirst {α₀ α₁ β₀ β₁}
  (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
  comp.mk (tsecond f' <$> tfirst f x) =
  bitraverse (comp.mk ∘ map pure ∘ f) (comp.mk ∘ pure ∘ f') x :=
by simp [tfirst,tsecond,comp_bitraverse]

@[higher_order tsecond_comp_tsecond]
lemma comp_tsecond {α β₀ β₁ β₂}
  (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) :
  comp.mk (tsecond g' <$> tsecond g x) = tsecond (comp.mk ∘ map g' ∘ g) x :=
by simp [tsecond,comp_bitraverse]; refl

open bifunctor

private lemma pure_eq_id_mk_comp_id {α} :
  pure = id.mk ∘ @id α := rfl

open function

@[higher_order]
lemma tfirst_eq_first_id {α α' β} (f : α → α') (x : t α β) :
  tfirst (id.mk ∘ f) x = id.mk (first f x) :=
by simp [tfirst,first,pure_eq_id_mk_comp_id,-comp.right_id,bitraverse_eq_bimap_id]

@[higher_order]
lemma tsecond_eq_second_id {α β β'} (f : β → β') (x : t α β) :
  tsecond (id.mk ∘ f) x = id.mk (second f x) :=
by simp [tsecond,second,pure_eq_id_mk_comp_id,-comp.right_id,bitraverse_eq_bimap_id]

attribute [functor_norm] comp_bitraverse comp_tsecond comp_tfirst
  tsecond_comp_tsecond tsecond_comp_tfirst tfirst_comp_tsecond tfirst_comp_tfirst
  bitraverse_comp bitraverse_id_id tfirst_id tsecond_id

end bitraversable
