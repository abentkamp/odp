import measure_theory.integration

variables {α β γ δ : Type*}
namespace measure_theory
variables [measurable_space α] {μ : measure α}
open encodable
open measure

open_locale ennreal

lemma lintegral_union {s t : set α} (hs : measurable_set s) (ht : measurable_set t)
  (hd : disjoint s t) (f : α → ℝ≥0∞) :
  ∫⁻ a in s ∪ t, f a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in t, f a ∂μ :=
by simp [measure.restrict_union hd hs ht]

lemma lintegral_compl {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂μ = ∫⁻ a in s, f a ∂μ + ∫⁻ a in sᶜ, f a ∂μ :=
by rw [←lintegral_union hs (by measurability) disjoint_compl_right f,
  set.union_compl_self, restrict_univ]

lemma set_lintegral_nonzero {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) 
  (h : ∀ x ∉ s, f x = 0) :
  ∫⁻ a, f a ∂μ = ∫⁻ a in s, f a ∂μ :=
begin
  rw lintegral_compl hs,
  convert add_zero (∫⁻ (a : α) in s, f a ∂μ),
  rw [← @lintegral_zero _ _ (μ.restrict sᶜ)],
  apply measure_theory.lintegral_congr_ae,
  rw measure_theory.ae_restrict_eq,
  apply filter.mem_inf_sets_of_right,
  apply h,
  measurability
end

end measure_theory