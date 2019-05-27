
import tactic.ext data.stream

attribute [ext] stream.ext

namespace stream

variables {α : Type*} {β : Type*}

lemma mem_def (s : stream α) (x : α) :
  x ∈ s ↔ ∃ i, x = s.nth i := iff.refl _

lemma mem_map_iff (s : stream α) (b : β) (f : α → β) : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
⟨ exists_of_mem_map, λ ⟨a,h,h'⟩, h' ▸ mem_map _ h ⟩

lemma mem_of_mem_drop {s : stream α} {n : ℕ} {x : α} : x ∈ s.drop n → x ∈ s
| ⟨i,h⟩ := ⟨_,h⟩

end stream
