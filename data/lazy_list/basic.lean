/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for lazy_lists.
-/

import data.traversable.equiv data.lazy_list

namespace lazy_list

open function

def list_equiv_lazy_list (α : Type*) : list α ≃ lazy_list α :=
by { refine { to_fun := lazy_list.of_list, inv_fun := lazy_list.to_list, .. };
     simp [left_inverse,function.right_inverse];
     intros x ,
     all_goals
     { induction x; [ refl, simp! [*] ] },
     ext, rw [punit_eq_punit x], }

instance : traversable lazy_list :=
equiv.traversable list_equiv_lazy_list

instance : is_lawful_traversable lazy_list :=
equiv.is_lawful_traversable list_equiv_lazy_list

end lazy_list
