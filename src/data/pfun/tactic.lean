import data.pfun.fix
import category.bitraversable.instances
import tactic.equations

variables {α : Type*} {β : Type*} {γ : Type*} {φ : Type*}

namespace complete_partial_order

open function has_fix complete_partial_order

section continuity_attr

open tactic native

-- @[user_attribute]
-- meta def continuity_attr : user_attribute (rb_map name $ list name) :=
-- { name := `continuity,
--   descr := "proof rule for continuity in the sense of complete partial orders",
--   cache_cfg := { mk_cache := λ (ls : list name),
--                              do { let m := rb_map.mk name (list name),
--                                   ls.mfoldl (λ m n,
--                                   do { (_,t) ← mk_const n >>= infer_type >>= mk_local_pis,
--                                        `(continuous' %%f) ← pure t <|> fail format!"{t}",
--                                        let l := f.binding_body,
--                                        pure $ m.insert_cons l.get_app_fn.const_name n }) m
--                                    },
--                  dependencies := [] } }

end continuity_attr

-- section mono

-- variables  [preorder α]

-- end mono

-- section continuity

-- variables [complete_partial_order α] [complete_partial_order β] [complete_partial_order γ]

-- lemma cont_const [complete_partial_order β] (f : β) (c : chain α) :
--   Sup (c.map (λ _, f) (const_mono _)) = f :=
-- begin
--   apply le_antisymm,
--   { apply Sup_le, simp [chain.mem_map_iff],
--     intros, subst f },
--   { apply le_Sup, simp [chain.mem_map_iff], exact ⟨ c.elems 0,0,rfl ⟩ }
-- end

-- lemma cont_ite [complete_partial_order β] {p : Prop} {hp : decidable p} (c : chain α) (f g : α → β) (hf hg) :
--   Sup (c.map (λ x, @ite p hp _ (f x) (g x)) (ite_mono hf hg)) = @ite p hp _ (Sup $ c.map f hf) (Sup $ c.map g hg) :=
-- by split_ifs; refl

-- end continuity

end complete_partial_order

namespace tactic

open tactic expr
open function has_fix complete_partial_order

-- meta def continuity_ext : tactic (list expr) :=
-- do `(continuous' %%f) ← target,
--    (args,_) ← infer_type f >>= mk_local_pis,
--    let arity := args.length - 1,
--    iterate_exactly' arity $
--      applyc ``pi.continuous_ext >> intro1

-- meta def continuity_step : tactic unit :=
-- do continuity_ext,
--    e@`(continuous' %%f) ← target,
--    (lam n bi d b) ← pure f,
--    m ← continuity_attr.get_cache,
--    match b.get_app_fn with
--    | (const n _) :=
--      do ls ← m.find n <|> pure [``cont_const'],
--         ls.any_of applyc
--    | v@(var _) :=
--      do let args := b.get_app_args,
--         vs ← args.mmap $ infer_type >=> mk_local_def `v,
--         let f' := lam n bi d $ v.mk_app vs,
--         let e' := (e.app_fn f').pis vs,
--         g ← mk_meta_var e',
--         exact $ g.mk_app args,
--         gs ← get_goals,
--         set_goals $ g :: gs,
--         vs ← intron' args.length,
--         vs.reverse.mmap' $ λ v, refine ``(pi.continuous_congr _ %%v _),
--         refine ``(cont_id')
--    | t := do
--      f ← pp f,
--      fail format!"unsupported {f}"
--    end

meta def show_continuity : tactic unit :=
focus1 $
do `(continuous' %%f) ← target,
   let n := f.get_app_fn.const_name,
   vs ← continuity_ext,
   e@`(continuous' %%f) ← target,
   cases_on_equations f,
   all_goals $ do
   { intros,
     target >>= instantiate_mvars >>= unsafe_change,
     my_unfold n,
     repeat continuity_step,
     done },
   skip

run_cmd add_interactive [``continuity_step,``show_continuity]

open interactive expr

meta def mk_cpo_instance : expr → tactic expr
| (pi n bi d b) :=
do v ← mk_local' n bi d,
   let b' := lam n bi d b,
   inst ← mk_cpo_instance (b.instantiate_var v) >>= lambdas [v],
   mk_mapp ``pi.complete_partial_order [d,b',inst]
| `(roption %%α) := mk_mapp ``roption.complete_partial_order [α]
| e := to_expr ``(complete_partial_order %%e) >>= mk_instance

meta def functional_type_aux : expr → expr → list expr → tactic (list expr × expr)
| e (pi n bi d b) vs :=
  if d =ₐ b
    then return (vs.reverse, e)
    else do v ← mk_local' n bi d,
            e' ← head_beta $ e v,
            functional_type_aux e' (b.instantiate_var v) (v :: vs)
| e _ _ := failed

meta def get_functional (n : name) : tactic (list expr × expr) :=
do d ← get_decl n,
   let ls := d.univ_params,
   let t  := d.type,
   let c : expr := const n $ ls.map level.param,
   functional_type_aux c t []

meta def mk_continuous_stmt (e : expr) (vs : list expr) : tactic expr :=
do t ← infer_type e,
   let t' := t.binding_domain,
   inst ← mk_cpo_instance t',
   mk_mapp ``continuous' [t',t',inst,inst,e] >>= pis vs

run_cmd mk_simp_attr `eqn_lemma

meta def mk_rec_eqns (n p cont_n : name) (vs : list expr) : tactic unit :=
do { ls ← get_eqn_lemmas_for ff n,
     ls.mmap' $ λ l : name,
     do let l' := l.replace_prefix n p,
        d ← get_decl l,
        t ← instantiate_mvars d.type,
        (ps,e) ← mk_local_pis t,
        let arity := vs.length,
        let ps₀ := ps.take arity,
        let ps₁ := ps.drop arity,
        let ls := d.univ_params,
        let fn := (expr.const n $ ls.map level.param : expr).mk_app ps₀ ps₁.head,
        let defn := (expr.const p $ ls.map level.param : expr).mk_app ps₀,
        e ← kabstract e fn >>= flip kabstract ps₁.head,
        let ps := ps₀ ++ ps₁.tail,
        eqn ← pis ps $ e.instantiate_var defn,
        pr ← run_async $ do
          { pr ← mk_meta_var eqn,
            set_goals [pr],
            ps ← intron' ps.length,
            let ps₀ := ps.take arity,
            let ps₁ := ps.drop arity,
            let cont_l := (expr.const cont_n $ ls.map level.param : expr).mk_app ps₀,
            dunfold_target [p],
            (l,r) ← target >>= match_eq,
            fix_eq ← mk_mapp ``lawful_fix.fix_eq [none, none, none, none, none, cont_l],
            (h,p,_) ← rewrite fix_eq l,
            transitivity,
            exact p,
            try $ my_unfold n,
            reflexivity,
            done,
            pr ← instantiate_mvars pr,
            pure pr },
        add_decl $ declaration.thm l' ls eqn pr,
        simp_attr.eqn_lemma.set l' () tt }

meta def check_level : option ℕ → ℕ → bool
| none _ := tt
| (some n) m := m ≤ n

@[user_attribute]
meta def partial_attr : user_attribute unit (option ℕ) :=
{ name := `partial,
  descr := "Create a recursive declaration from a functional",
  parser := optional lean.parser.small_nat,
  after_set := some $ λ n _ b,
    do lvl ← partial_attr.get_param n,
       d ← get_decl n,
       let ls := d.univ_params,
       let p := n.get_prefix,
       let cont_n := p <.> "cont",
       (vs, fn) ← get_functional n,
       mk_ind_principle n,
       when (check_level lvl 1) $
       do { cont_t ← mk_continuous_stmt fn vs,
            pr ← run_async $ do
              { pr ← mk_meta_var cont_t,
                set_goals [pr],
                intron vs.length,
                show_continuity,
                pr ← instantiate_mvars pr,
                let ls := pr.list_meta_vars,
                ls.mmap' $ λ v, infer_type v >>= trace,
                pure pr },
            add_decl $ declaration.thm cont_n ls cont_t pr },
       when (check_level lvl 2) $
       do { df ← mk_app ``has_fix.fix [fn] >>= lambdas vs,
            t  ← infer_type df,
            add_decl $ mk_definition p ls t df },
       when (check_level lvl 3) $
       mk_rec_eqns n p cont_n vs,
       skip
  }

setup_tactic_parser

meta def var := name × binder_info × option pexpr

-- meta def mk_dummy_local (n : name)

meta def mk_meta_type : tactic expr :=
do u ← mk_meta_univ, mk_meta_var $ sort u

meta def mk_bound_var (n : name) (t : option pexpr) : tactic expr :=
do t ← mk_meta_type,
   let v := local_const n n binder_info.default t,
   updateex_env $ λ e, e.add $ declaration.cnst n [] `(true) tt,
   pure v

meta def parse_inst : lean.parser (list expr) :=
do e ← texpr,
   (list.ret <$> mk_bound_var `_ (some e))

meta def parse_var_decl' (bi : binder_info) : lean.parser (list expr) :=
do ns ← ident_*,
   e ← (tk ":" *> texpr)?,
   ns.mmap $ λ n, mk_bound_var n e

meta def var_decl : lean.parser (list expr) :=
brackets "(" ")" (parse_var_decl' binder_info.default) <|>
brackets "{" "}" (parse_var_decl' binder_info.implicit) <|>
brackets "⦃" "⦄"  (parse_var_decl' binder_info.strict_implicit) <|>
brackets "[" "]" (parse_var_decl' binder_info.inst_implicit) <|>
brackets "[" "]" parse_inst

meta def constr_or_var : lean.parser pexpr :=
do n ← ident_,
   ↑(resolve_name n <|> to_pexpr <$> mk_bound_var n none)

meta def constr : lean.parser pexpr :=
do n ← ident,
   resolve_name n

meta def bound_var : lean.parser expr :=
do { n ← ident_,
     mk_bound_var n none }

meta def pat : lean.parser pexpr :=
constr_or_var <|>
brackets "(" ")" (do c ← constr, ps ← many pat, pure $ ps.foldl app c)

meta def eqn_list : lean.parser (list (list pexpr × pexpr)) :=
many $
do tk "|",
   ps ← many pat,
   tk ":=",
   body ← texpr,
   pure (ps, body)

meta def get_opt_type : option pexpr → tactic expr
| none := mk_meta_type
| (some t) := to_expr t

-- @[user_command]
-- meta def partial_def_cmd (_ : parse $ tk "partial_def") : lean.parser unit :=
-- do n ← ident,
--    vs ← many var_decl,
--    let vs := vs.join,
--    t ← (tk ":" *> texpr)?,
--    body ← (tk ":=" *> sum.inl <$> texpr) <|> (sum.inr <$> eqn_list) <|> (pure $ sum.inr []),
--    ↑do t ← get_opt_type t,
--       sig ← mk_local_def n t,
--       -- ps ← vs.mmap $ λ ⟨n,bi,t⟩, do { t ← get_opt_type t, mk_local' n bi t },
--       trace "thus far",
--       pats ← match body with
--              | (sum.inl val) := do e ← to_expr val, pure [(@list.nil pexpr,e)]
--              | (sum.inr val) := traverse (traverse to_expr) val
--              end,
--       trace "thus far",
--       add_defn_equations [] vs sig pats ff .

inductive tree (α : Type*)
| nil {} : tree | node (x : α) : tree → tree → tree

open tree

-- partial_def tree_map'.intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
-- | nil := pure nil
-- | (node x t₀ t₁) :=
-- node (f x) <$> tree_map t₀ <*> tree_map t₁

end tactic
