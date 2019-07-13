/-
Copyright (c) 2019 Simon hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon hudon

Laws of the State monad
-/

universes u v

namespace state_t

variables {m : Type u → Type v} [monad m] [is_lawful_monad m]
variables {α β : Type u}

lemma put_get (x : α) : (put x >>= λ _, get : state_t α m α) = (put x >>= λ _, pure x) :=
by simp [put,get,monad_state.lift,(>>=),state_t.bind,has_pure.pure,state_t.pure]

lemma get_get (f : α → α → state_t α m β) : (get >>= λ x, get >>= f x) = get >>= λ x, f x x :=
by simp [put,get,monad_state.lift,(>>=),state_t.bind,has_pure.pure,state_t.pure]

lemma put_put (x y : α) : (put x >>= λ _, put y : state_t α m _) = put y :=
by simp [put,get,monad_state.lift,(>>=),state_t.bind,has_pure.pure,state_t.pure]

end state_t
