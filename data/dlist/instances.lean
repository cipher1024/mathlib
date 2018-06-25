
import data.dlist data.traversable.equiv

namespace dlist

variables (α : Type*)

open function equiv

def list_equiv_dlist : list α ≃ dlist α :=
by refine { to_fun := dlist.of_list, inv_fun := dlist.to_list, .. };
   simp [function.right_inverse,left_inverse,to_list_of_list,of_list_to_list]

instance : traversable dlist :=
equiv.traversable list_equiv_dlist

instance : is_lawful_traversable dlist :=
equiv.is_lawful_traversable list_equiv_dlist

end dlist
