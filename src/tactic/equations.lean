
import data.list.min_max

namespace tactic

open expr

/--
find_discr h ht g

 1. match: apply assumption
 2. disagree: discard assumption
 3. assumption too specific: destruct variable
-/
meta def find_discr : expr → expr → tactic (option expr)
| (local_const _ _ _ _) (local_const _ _ _ _) := pure none
| (app _ _) v@(local_const _ _ _ _) := pure (some v)
| (app h h') (app g g') := do (some v) ← find_discr h g | find_discr h' g',
                              pure (some v)
| c@(const _ _) c'@(const _ _) := guard (c = c') >> pure none
| c@(const _ _) v@(local_const _ _ _ _) := pure $ some v
| e e' :=
do e  ← pp e,
   e' ← pp e',
   fail format!"{e} - {e'}"

meta def using_equation (hs : list (expr × expr)) : tactic unit :=
do tgt ← target,
   hs.any_of $ λ ⟨h,t⟩, do
     r ← find_discr t tgt,
     match r with
     | (some v) := () <$ cases v; using_equation
     | none := () <$ apply h
     end

meta def mk_ind_principle (n : name) : tactic unit :=
do ls ← get_eqn_lemmas_for ff n,
   ns ← ls.mmap $ λ l,
   do { d ← get_decl l,
        (vs,t) ← mk_local_pis d.type,
        (l,_) ← match_eq t,
        return (l.get_app_args.take_while $ λ c, is_local_constant c).length },
   let n_first_params := ns.minimum,
   d ← get_decl n,
   (vs,t) ← mk_local_pis d.type,
   let univs := `uu7 :: d.univ_params,
   let s := @sort tt $ level.param `uu7,
   v ← mk_local_def `v t,
   let vs' := vs.drop n_first_params,
   t ← pis vs' s,
   C ← mk_local_def `C t,
   hs ← ls.mmap $ λ l,
   do { d ← get_decl l,
        let t := (vs.take n_first_params).foldl (λ t v : expr, t.binding_body.instantiate_var v) d.type,
        (vs,t) ← mk_local_pis t,
        (l,_) ← match_eq t,
        pis vs (C.mk_app $ l.get_app_args.drop n_first_params)
         >>= mk_local_def `h },

   t ← pis (C :: hs ++ vs') (C.mk_app vs'),
   let vs := t.list_local_consts,
   pr ← run_async $ do
   { pr ← mk_meta_var t,
     set_goals [pr],
     C ← intro1,
     hs ← intro_lst $ hs.map expr.local_pp_name,
     vs' ← intro_lst $ vs'.map expr.local_pp_name,
     hs ← hs.mmap $ λ h, do { (_,t) ← infer_type h >>= mk_local_pis, pure (h,t) },
     using_equation hs,
     instantiate_mvars pr >>= lambdas vs },
   t ← pis vs t,
   add_decl $ declaration.thm (n <.> "patts") univs t pr,
   skip

meta def cases_on_equations (e : expr) : tactic unit :=
focus1 $
do let e := e.binding_body,
   let n := e.get_app_fn.const_name,
   d_fn ← get_decl n,
   (ps,t) ← mk_local_pis d_fn.type,
   dp ← mk_const $ n <.> "patts",
   dp_type ← infer_type dp,
   (args,hd) ← mk_local_pis dp_type,
   let vs := hd.get_app_args,
   let dropn := ps.length - vs.length,
   let mvars := args.length - vs.length,
   (lmm,_) ← (list.iota mvars).mfoldl (λ (x : expr × expr) _,
     do let ⟨e,t⟩ := x,
        v ← mk_meta_var t.binding_domain,
        return $ (e v, t.binding_body.instantiate_var v)) (dp, dp_type),
   let gs := lmm.get_app_args,
   apply (lmm.mk_app $ e.get_app_args.drop dropn),
   set_goals gs,
   skip

end tactic
