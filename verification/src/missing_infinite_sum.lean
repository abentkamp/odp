/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import topology.algebra.infinite_sum

section

universe variables u
variables {α β γ : Type u}
variables [add_comm_monoid α] [topological_space α] [t2_space α]

lemma tsum_singleton (b : β) (f : β → α) (hf : summable f) :
  ∑' (x : ({b} : set β)), f x = f b :=
begin
  rw tsum_eq_single,
  { exact (rfl : f (⟨b, _⟩ : ({b} : set β)) = f b),
    rw set.mem_singleton_iff },
  { intros b' hb',
    apply false.elim (hb' _),
    ext,
    exact set.mem_singleton_iff.1 b'.property }
end

lemma function.injective.tsum_range_iff {f : β → α} {g : γ → β} (hg : function.injective g) :
  ∑' (x : set.range g), f x = ∑' x, f (g x) :=
begin
  apply tsum_eq_tsum_of_has_sum_iff_has_sum,
  exact λ a, function.injective.has_sum_range_iff hg
end

lemma set.compl_none_eq_range_some : ({none}ᶜ : set (option β)) = set.range some :=
begin
  ext,
  simp_rw [set.mem_compl_iff,
   set.mem_range,
   set.mem_singleton_iff,
   @eq_comm _ (some _) x,
   ←option.is_some_iff_exists],
  exact option.ne_none_iff_is_some
end

end
