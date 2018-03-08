
universes u v

variables {α β γ : Type u}

namespace ulift

def pure (x : α) : ulift α := ⟨ x ⟩

instance : has_bind ulift :=
⟨ λ _ _ x f, f (down x) ⟩

lemma bind_assoc (x : ulift α) (f : α → ulift β) (g : β → ulift γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
by { cases x ; refl }

lemma pure_bind (x : α) (f : α → ulift β)
: pure x >>= f = f x :=
by { cases h : f x, simp [pure,has_bind.bind,h], }

lemma id_map (x : ulift α)
: x >>= (ulift.pure ∘ id) = x :=
by { cases x, simp [has_bind.bind,pure] }

end ulift

instance : monad ulift :=
{ pure := @ulift.pure
, pure_bind := @ulift.pure_bind
, bind_assoc := @ulift.bind_assoc
, id_map := @ulift.id_map
, .. ulift.has_bind }

@[norm]
lemma ulift.up_eq_pure (x : α) :
  ulift.up.{v} x = pure x := rfl
