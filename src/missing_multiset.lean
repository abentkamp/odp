import algebra.big_operators

open_locale big_operators

namespace multiset

universe variables u v

#check multiset.fold_distr

lemma sum_add {β : Type u} {α : Type v} [add_comm_monoid β] 
  {f g : α → β}  {s : multiset α} :
  s.sum (λ x, f x + g x)
    = (∑ (x : α) in s, f x) + (∑ (x : α) in s, g x) :=
begin
  dunfold finset.sum,
  exact multiset.fold_distrib (+) f g s,
end
end
end multiset
