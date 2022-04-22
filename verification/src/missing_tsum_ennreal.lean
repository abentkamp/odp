/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import topology.instances.ennreal

open classical set filter metric
open_locale classical topological_space ennreal nnreal big_operators filter

namespace finset
variables {α : Type*}

lemma sum_to_real (s : finset α) (f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞) :
  (∑ (b : α) in s, f b).to_real = (∑ (b : α) in s, (f b).to_real) :=
begin
  let r := λ (b : ℝ≥0∞) (c : ℝ), b ≠ ∞ ∧ b.to_real = c,
  have r00 : r 0 0, refine ⟨ennreal.zero_ne_top, ennreal.zero_to_real⟩,
  have r_step : ∀ (a : α) (b : ℝ≥0∞) (c : ℝ), r b c → r (f a + b) ((f a).to_real + c),
  { intros a b c hbc, dsimp [r] at hbc ⊢,
    simp [ennreal.to_real_add, hf a, hbc.2, hbc.1], },
  exact (finset.sum_hom_rel r00 r_step).2,
end

end finset

namespace ennreal
variables {α : Type*}

lemma has_sum_to_real  (f : α → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞):
  has_sum f a → has_sum (λ x, (f x).to_real) a.to_real :=
begin
  intro h,
  have hf : ∀ x, f x ≠ ∞ := ennreal.ne_top_of_tsum_ne_top (h.tsum_eq.symm ▸ ha),
  unfold has_sum at *,
  rw ←ennreal.tendsto_to_real_iff _ ha at h,
  convert h,
  ext s,
  rw finset.sum_to_real s f hf,
  simp_rw [←lt_top_iff_ne_top, sum_lt_top_iff, lt_top_iff_ne_top],
  intros, apply hf
end

lemma sum_to_real {α : Type*} (f : α → ℝ≥0∞) (hf : ∑' x, f x ≠ ∞) :
  ∑' x, (f x).to_real = (∑' x, f x).to_real :=
begin
  have summable_f : summable f := ennreal.summable,
  rcases summable_f with ⟨b, hb⟩,
  rw has_sum.tsum_eq hb at *,
  rw has_sum.tsum_eq (has_sum_to_real f b hf hb)
end

lemma tsum_all_but_one_zero {ι : Type*} [decidable_eq ι](i : ι) (f : ι → ennreal)
  (hf : ∀ j, j ≠ i → f j = 0) : 
  ∑' j, f j = f i :=
calc
  (∑' j, f j) =  (∑' j, dite (j = i) (λ h, f i) (λ h, 0)) :
  begin
    congr',
    funext,
    conv {
      to_rhs, congr, funext, rw ←h, skip, 
      funext, rw ← hf _ h, },
    simp
  end
  ... = f i : by simp

end ennreal