import measure_theory.decomposition.unsigned_hahn

namespace measure_theory

variables {α : Type*} [measurable_space α] {μ ν : measure α} [finite_measure μ] [finite_measure ν]

/-- This instance of `finite_measure (μ.restrict s)` assumes `finite_measure μ`
instead of `fact (μ s < ∞)`. This is less general, but better for automation. -/
instance restrict.finite_measure' (s : set α) (μ : measure α) [finite_measure μ] :
  finite_measure (μ.restrict s) :=
@restrict.finite_measure α _ s μ (fact.mk (measure_lt_top μ s))

lemma measure.le_sub_add : μ ≤ μ - ν + ν :=
begin
  obtain ⟨s, hsm, hs, hsc⟩ : ∃ (s : set α),
    measurable_set s ∧
      (∀ (t : set α), measurable_set t → t ⊆ s → μ t ≤ ν t) ∧
        ∀ (t : set α), measurable_set t → t ⊆ sᶜ → ν t ≤ μ t := hahn_decomposition,
  have h_restrict_le_restrict : ν.restrict sᶜ ≤ μ.restrict sᶜ,
    { rw measure.le_iff,
      intros t ht,
      rw [measure.restrict_apply ht, measure.restrict_apply ht],
      exact hsc (t ∩ sᶜ) (by measurability) (by simp) },
  intros t ht,
  have : t = (t ∩ s) ∪ (t ∩ sᶜ), by simp,
  rw [this, measure_union, measure_union, measure.add_apply, measure.add_apply],
  refine add_le_add (le_add_left _) _,
  { exact hs (t ∩ s) (by measurability) (by simp) },
  { --have := finite_measure (ν.restrict sᶜ), by apply_instance,
    haveI : finite_measure (ν.restrict sᶜ) := by apply_instance,
    rw [←measure.restrict_apply ht, ←measure.restrict_apply ht, ←measure.restrict_apply ht, 
        measure.restrict_sub_eq_restrict_sub_restrict (show measurable_set sᶜ, by measurability)],
    rw @measure.sub_apply _ _ _ (ν.restrict sᶜ) _ (by apply_instance) ht,
    convert le_refl _,
    rw [←@measure.sub_apply _ _ _ (ν.restrict sᶜ) _ (by apply_instance) ht, ←measure.add_apply],
    rw @measure.sub_add_cancel_of_le _ _ (μ.restrict sᶜ) (ν.restrict sᶜ) _ _,
    rw measure.le_iff,
    intros t ht,
    rw [measure.restrict_apply ht, measure.restrict_apply ht],
    exact hsc (t ∩ sᶜ) (by measurability) (by simp),
    exact h_restrict_le_restrict,
    exact h_restrict_le_restrict },
  apply set.disjoint_of_subset _ _ (@disjoint_compl_right _ s _),
  { simp },
  { simp },
  { measurability },
  { measurability },
  apply set.disjoint_of_subset _ _ (@disjoint_compl_right _ s _),
  { simp },
  { simp },
  { measurability },
  { measurability },
end

lemma measure.sub_apply_finite {α : Type*} [measurable_space α] (μ ν : measure α) 
  [finite_measure μ] [finite_measure ν] (s : set α) (hs : measurable_set s) : 
  ∃ t, measurable_set t ∧ (μ - ν) s = μ (s ∩ t) - ν (s ∩ t) :=
begin
  rcases @hahn_decomposition _ _ μ ν _ _ with ⟨t, ht, ht₁, ht₂⟩,
  use t,
  rw ←@measure.restrict_compl_add_restrict _ _ (μ - ν) t,
  rw [measure.add_apply, measure.restrict_sub_eq_restrict_sub_restrict, 
    measure.restrict_sub_eq_restrict_sub_restrict],
  have μ_le_ν : μ.restrict tᶜ ≤ ν.restrict tᶜ,
  { rw measure.le_iff,
    intros u hu,
    rw [measure.restrict_apply hu, measure.restrict_apply hu],
    exact ht₂ (u ∩ tᶜ) (by simp [ht, hu]) (set.inter_subset_right _ _) },
  have ν_le_μ : ν.restrict t ≤ μ.restrict t,
  { rw measure.le_iff,
    intros u hu,
    rw [measure.restrict_apply hu, measure.restrict_apply hu],
    exact ht₁ (u ∩ t) (by simp [ht, hu]) (by simp) },
  rw measure.sub_apply _ ν_le_μ,
  rw measure.sub_eq_zero_of_le μ_le_ν,
  simp only [measure.coe_zero, pi.zero_apply, zero_add],
  rw [measure.restrict_apply, measure.restrict_apply],
  refine ⟨ht, _⟩,
  refl,
  apply hs,
  apply hs,
  apply hs,
  apply ht,
  simp [ht],
  apply ht,
end

end measure_theory