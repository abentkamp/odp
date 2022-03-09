/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import algebra.big_operators.basic
import data.multiset.fold

open_locale big_operators

namespace finset

universe variables u v w

lemma sum_add {β : Type u} {α : Type v} [add_comm_monoid β]
  {f g : α → β}  {s : finset α} :
  ∑ (x : α) in s, (f x + g x)
    = (∑ (x : α) in s, f x) + (∑ (x : α) in s, g x) :=
begin
  have : (s.val.map (λ (x : α), f x + g x)).fold has_add.add (0 + 0) =
      (s.val.map f).fold has_add.add 0 + (s.val.map g).fold has_add.add 0 :=
    multiset.fold_distrib (+) 0 0 s.val,
  simp only [multiset.fold_eq_foldr (+) _ _, add_zero] at this,
  exact this,
end

end finset