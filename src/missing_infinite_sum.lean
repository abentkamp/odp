import topology.algebra.infinite_sum

section 

universe variables u
variables {α β γ : Type u}
variables [add_comm_group α] [topological_space α] [topological_add_group α] [t2_space α]

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

lemma tsum_option (f : option β → α) (hf : summable f) : 
  ∑' (x : option β), f x = ∑' (x : β), f (some x) + f none :=
begin
  have h_summable_none : summable ((λ (x : option β), f x) ∘ (coe : ({none} : set (option β)) → option β)),
  { apply set.finite.summable,
    simp, },
  have h_summable_some : summable ((λ (x : option β), f x) ∘ (coe : ({none}ᶜ : set (option β)) → option β)),
  { rw summable.summable_compl_iff,
    apply hf,
    apply h_summable_none },
  rw ← tsum_add_tsum_compl h_summable_none h_summable_some,
  rw tsum_singleton none f hf,
  rw add_comm,
  have : ∑' (x : ({none} : set (option β))ᶜ), f ↑x = ∑' (x : β), f (some x),
  { rw ←function.injective.tsum_range_iff (option.some_injective β),
    rw set.compl_none_eq_range_some,
    apply_instance,
    apply_instance,
  },
  rw this,
end

end
