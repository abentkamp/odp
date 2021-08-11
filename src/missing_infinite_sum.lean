import topology.algebra.infinite_sum
import .missing_indicator

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


universe variables u
variables {α β γ : Type u}
variables [add_comm_sub_cancel_monoid α] [topological_space α] [t2_space α]


-- #check set.indicator_compl_add_self
-- #check has_sum.compl_add

-- lemma has_sum.has_sum_compl_iff' [has_continuous_add α]
--   {s : set β} {f : β → α} {a₁ a₂ : α}
--   (hf : has_sum (f ∘ coe : s → α) a₁) :
--   has_sum (f ∘ coe : sᶜ → α) a₂ ↔ has_sum f (a₁ + a₂) :=
-- begin
--   refine ⟨λ h, hf.add_compl h, λ h, _⟩,
--   rw [has_sum_subtype_iff_indicator] at hf ⊢,
--   rw [set.indicator_compl_add_sub_cancel_monoid],
--   have := has_sum.sub,-- This doensn't work!
--   -- Maybe instead map all sums to be sums over the reals instead? (Would also solve the other issue concerning mul with consts)
--   -- Or split while still a union of sets
--   -- simpa only [add_sub_cancel_monoid.add_sub_cancel] using h.sub hf
-- end

-- lemma tsum_option (f : option β → α) (hf : summable f) : 
--   ∑' (x : option β), f x = ∑' (x : β), f (some x) + f none :=
-- begin
--   have h_summable_none : summable ((λ (x : option β), f x) ∘ (coe : ({none} : set (option β)) → option β)),
--   { apply set.finite.summable,
--     simp, },
--   have h_summable_some : summable ((λ (x : option β), f x) ∘ (coe : ({none}ᶜ : set (option β)) → option β)), -- Problem!!
--   { rw summable.summable_compl_iff,
--     apply hf,
--     apply h_summable_none },
--   rw ← tsum_add_tsum_compl h_summable_none h_summable_some,
--   rw tsum_singleton none f hf,
--   rw add_comm,
--   have : ∑' (x : ({none} : set (option β))ᶜ), f ↑x = ∑' (x : β), f (some x),
--   { rw ←function.injective.tsum_range_iff (option.some_injective β),
--     rw set.compl_none_eq_range_some,
--     apply_instance,
--     apply_instance,
--   },
--   rw this,
-- end

-- end
