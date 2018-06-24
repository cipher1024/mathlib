
import data.traversable.instances data.equiv data.lazy_list

namespace lazy_list

open function

def list_equiv_lazy_list (α : Type*) : list α ≃ lazy_list α :=
by { refine { to_fun := lazy_list.of_list, inv_fun := lazy_list.to_list, .. } ;
     simp [left_inverse,function.right_inverse] ;
     intros x ; { induction x ; [ refl, simp! [*] ] },  }

instance : traversable lazy_list :=
equiv.traversable list_equiv_lazy_list

instance : is_lawful_traversable lazy_list :=
equiv.is_lawful_traversable list_equiv_lazy_list

end lazy_list
