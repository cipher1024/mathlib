/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Automation to construct `traversable` instances
-/

import .basic
import category.basic
import tactic.basic

namespace tactic.interactive

open tactic list monad functor

def succeeds {m : Type* → Type*} [alternative m] {α} (cmd : m α) : m bool :=
(tt <$ cmd) <|> pure ff

meta def traverse_field (n : name) (cl f v e : expr) : tactic (option expr) :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then return none
   else if v.occurs t
   then   mcond (succeeds $ is_def_eq t v)
                (pure $ some $ expr.app f e)
                (if ¬ v.occurs (t.app_fn)
                    then some <$> to_expr ``(compose.mk (traversable.traverse %%f %%e))
                    else fail format!"type {t} is not traversable with respect to variable {v}")
   else
         (is_def_eq t.app_fn cl >> some <$> to_expr ``(compose.mk %%e))
     <|> some <$> to_expr ``(@pure %%cl _ _ %%e)

meta def seq_apply_constructor : list expr → expr → tactic expr
| (x :: xs) e := to_expr ``(%%e <*> %%x) >>= seq_apply_constructor xs
| [] e := return e

meta def fill_implicit_arg' : expr → expr → tactic expr
| f (expr.pi n bi d b) :=
if b.has_var then
do v ← mk_meta_var d,
   fill_implicit_arg' (expr.app f v) (b.instantiate_var v)
else return f
| e _ := return e

meta def fill_implicit_arg (n : name) : tactic expr :=
do c ← mk_const n,
   t ← infer_type c,
   fill_implicit_arg' c t

meta def traverse_constructor (c n : name) (f v : expr) (args : list expr) : tactic unit :=
do g ← target,
   args' ← mmap (traverse_field n g.app_fn f v) args,
   constr ← fill_implicit_arg c,
   constr' ← to_expr ``(@pure %%(g.app_fn) _ _ %%constr),
   r ← seq_apply_constructor (filter_map id args') constr',
   () <$ tactic.apply r

open applicative

meta def derive_traverse : tactic unit :=
do `(traversable %%f) ← target | failed,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   constructor,
   `[intros m _ α β f x],
   reset_instance_cache,
   x ← get_local `x,
   xs ← tactic.induction x,
   f ← get_local `f,
   α ← get_local `α,
   β ← get_local `β,
   m ← get_local `m,
   () <$ mmap₂'
      (λ (c : name) (x : name × list expr × _), solve1 (traverse_constructor c n f α x.2.1))
      cs xs

end tactic.interactive
