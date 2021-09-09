import topology.algebra.infinite_sum
import topology.instances.ennreal


open_locale big_operators
open_locale topological_space classical

section sum
variables {α β γ : Type*} [add_comm_monoid α] [topological_space α] [has_continuous_add α] [t2_space α] {f : β ⊕ γ → α} {a b : α}
open filter set

lemma has_sum_of_has_sum_inl_inr (hl : has_sum (f ∘ sum.inl) a) (hr : has_sum (f ∘ sum.inr) b) : has_sum f (a + b) :=
begin
  unfold has_sum at hl hr,
  have hl' : tendsto (λ (s : finset (β ⊕ γ)), ∑ b in s.filter (set.range sum.inl), f b) at_top (𝓝 a) := sorry, -- use hl
  have hr' : tendsto (λ (s : finset (β ⊕ γ)), ∑ b in s.filter (set.range sum.inr), f b) at_top (𝓝 b) := sorry, -- use hr
  convert filter.tendsto.add hl' hr',
    unfold has_sum,
  congr',
  ext s,
  rw ←finset.sum_union,
  rw finset.filter_union_right,
  sorry,
  sorry,
end

lemma summable_of_summable_inl_inr
  (hl : summable (f ∘ sum.inl)) (hr : summable (f ∘ sum.inr)) : summable f :=
begin
  rcases hl with ⟨a, ha⟩,
  rcases hr with ⟨b, hb⟩,
  exact ⟨a + b, has_sum_of_has_sum_inl_inr ha hb⟩
end

lemma tsum_inl_add_tsum_inr (hl : summable (f ∘ sum.inl)) (hr : summable (f ∘ sum.inr)) : 
  ∑' x, f (sum.inl x) + ∑' x, f (sum.inr x) = ∑' x, f x :=
(has_sum_of_has_sum_inl_inr hl.has_sum hr.has_sum).tsum_eq.symm

end sum

section option
variables {α β γ : Type*} {δ : Type*}
variables [add_comm_monoid α] [topological_space α] [has_continuous_add α] [t2_space α] 

lemma tsum_option (f : option β → α) (hf : summable (λ (x : β), f (some x))) : 
  ∑' (x : option β), f x = ∑' (x : β), f (some x) + f none :=
begin
  rw ←equiv.tsum_eq (equiv.option_equiv_sum_punit β).symm,
  rw ←tsum_inl_add_tsum_inr,
  congr,
  simp only [tsum_fintype, fintype.univ_punit, finset.sum_const, equiv.option_equiv_sum_punit_symm_inr, one_nsmul,
  finset.card_singleton],
  exact hf,
  exact ⟨_, has_sum_fintype _⟩,
  apply_instance
end

end option
