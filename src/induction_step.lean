import .adversary
import missing_integration
import measure_theory.measure_space
import missing_unsigned_hahn
import missing_infinite_sum

open measure_theory ennreal database_type set
open_locale ennreal
local infix ` ⊗ `:50  := measure.prod

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂] 
variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [probability_measure P₁] [probability_measure P₂]
variables {O₁ O₂ : Type} [measurable_space O₁] [measurable_space O₂]
variables {X : Type} [database_type X] (x x₀ x₁ : X) (hx : neighboring x₀ x₁)
variables (M₁ : X → Ω₁ → O₁) (p : odp_partition P₁ M₁)
variables (ε δ : ℝ≥0∞) (hδ : p.δ ≤ δ)
variables (M₂₀ M₂₁ : O₁ → Ω₂ → O₂) 

noncomputable def pos_hahn : measure O₁ := 
measure.map (λ ω, M₁ x₀ ω) P₁ - ε.exp • measure.map (λ ω, M₁ x₁ ω) P₁

lemma pos_hahn_prop : 
  measure.map (λ ω₁, M₁ x₀ ω₁) P₁ 
    ≤ ε.exp • measure.map (λ ω₁, M₁ x₁ ω₁) P₁ + pos_hahn P₁ x₀ x₁ M₁ ε :=
begin
  rw [add_comm, pos_hahn],
  haveI : finite_measure (measure.map (λ (ω : Ω₁), M₁ x₀ ω) P₁) := sorry,
  haveI : finite_measure (ε.exp • measure.map (λ (ω : Ω₁), M₁ x₁ ω) P₁) := sorry,
  apply measure.le_sub_add,
end

lemma diff_private_aux_min (s : set (O₁ × O₂)) (o₁ : O₁) 
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) (ε - εusage p o₁) (δ - p.δ)) : 
  P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s} 
    ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - p.δ) :=
calc P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s} = min 1 (P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}) :
begin
  rw min_eq_right,
  apply prob_le_one,
end
... ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s} + (δ - p.δ)) :
begin
  refine min_le_min (le_refl _) _,
  apply hM₂ o₁ {o₂ : O₂ | (o₁, o₂) ∈ s},
end
... ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - p.δ) :
begin
  rw min_add_distrib,
  exact le_trans (min_le_right _ _) (add_le_add (le_refl _) (min_le_right _ _)),
end

lemma inequality_slice (s : set (O₁ × O₂)) (i : option p.index) 
  (hs : s ⊆ (odp_set_for p i).prod univ)
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) (ε - εusage p o₁) (δ - p.δ)) :
(P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} 
  ≤ ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s}
    + pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :=
calc
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} 
 = ∫⁻ (ω₁ : Ω₁), P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂₀ (M₁ x₀ ω₁) ω₂) ∈ s} ∂P₁ : 
begin
  rw measure.prod_apply,
  refl,
  sorry
end
... = ∫⁻ (o₁ : O₁), P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ : 
begin
  rw lintegral_map,
  sorry,
  sorry,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i, P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ : 
begin
  rw set_lintegral_nonzero,
  sorry,
  { intros o₁ ho₁,
    convert measure_empty,
    rw eq_empty_iff_forall_not_mem,
    exact λ ω₂ hω₂, ho₁ (mem_prod.1 (hs hω₂)).1 }
end
... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
  min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - p.δ)
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ :
begin
  apply lintegral_mono,
  intro o₁,
  apply diff_private_aux_min,
  apply hM₂,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i,
  min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - p.δ)
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ :
begin
  apply set_lintegral_fun_congr,
  sorry,
  intros ω₁ hω₁,
  simp_rw εusage_eq_εusage_for hω₁,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i,
      min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s})
    ∂measure.map (λ (ω₁ : Ω₁), M₁ x₀ ω₁) P₁
    + (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :
begin
  rw [lintegral_add, lintegral_const, measure.restrict_apply_univ, measure.map_apply],
  refl,
  sorry,
  sorry,
  sorry,
  sorry,
end
... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
      min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) 
    ∂((εusage_for p i).exp • measure.map (λ ω₁, M₁ x₁ ω₁) P₁ + pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i))
    + (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :
begin
  refine add_le_add _ (le_refl _),
  refine measure_theory.lintegral_mono' _ (le_refl _),
  refine measure.restrict_mono (λ x hx, hx) _,
  apply pos_hahn_prop,
end
 ... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
      ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) 
      ∂(εusage_for p i).exp • measure.map (λ (ω₁ : Ω₁), M₁ x₁ ω₁) P₁ +
    ∫⁻ (o₁ : O₁) in odp_set_for p i, 1 ∂pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i)
  + (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
begin
  rw measure.restrict_add,
  rw lintegral_add_measure,
  refine add_le_add (add_le_add 
    (lintegral_mono (λ o₁, min_le_right _ _)) 
    (lintegral_mono (λ o₁, min_le_left _ _))) (le_refl _),
end
 ... = ε.exp * ∫⁻ (o₁ : O₁) in odp_set_for p i,
        P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s} 
        ∂measure.map (λ (ω₁ : Ω₁), M₁ x₁ ω₁) P₁
     + pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
     + (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
begin
  rw [lintegral_const_mul, measure.restrict_smul, lintegral_smul_measure],
  rw [←mul_assoc, ←exp_add, sub_add_cancel_of_le],
  rw [lintegral_one, measure.restrict_apply_univ],
  sorry, -- TODO: εusage_for p i ≤ ε
  sorry,
end
 ... = 
 ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i) +
  (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
begin
  rw ←set_lintegral_nonzero,
  rw lintegral_map,
  rw measure.prod_apply,
  refl,
  sorry,
  sorry,
  sorry,
  sorry,
  { intros o₁ ho₁,
    convert measure_empty,
    rw eq_empty_iff_forall_not_mem,
    exact λ ω₂ hω₂, ho₁ (mem_prod.1 (hs hω₂)).1 },
end

include hx
lemma sum_pos_hahn : 
  ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    = pos_hahn P₁ x₀ x₁ M₁ (εusage_for p none) (odp_set_for p none) :=
begin
  have h_eq_zero : ∀ (i : p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p (some i)) (odp_set_for p (some i)) = 0,
  { intro i,
    apply measure.sub_apply_eq_zero_of_restrict_le_restrict,
    rw measure.le_iff,
    intros s hs,
    rw [measure.restrict_apply, measure.restrict_apply],
    rw [measure.map_apply, measure.smul_apply, measure.map_apply],
    refine p.odp i x₀ x₁ (s ∩ odp_set_for p (some i)) (inter_subset_right _ _) hx,
    sorry,
    sorry,
    sorry,
    sorry,
    exact hs,
    exact hs,
    sorry },
  rw tsum_option,
  rw tsum_congr,
  rw tsum_zero,
  rw zero_add,
  apply h_eq_zero,
  sorry --summable
end

lemma pos_hahn_none : pos_hahn P₁ x₀ x₁ M₁ (εusage_for p none) (odp_set_for p none) ≤ p.δ :=
begin
  have := p.dp x₀ x₁ (odp_set_for p none) hx,
  rw [pos_hahn], 
  rcases @measure.sub_apply_finite _ _
    (measure.map (λ (ω : Ω₁), M₁ x₀ ω) P₁)
    ((εusage_for p none).exp • ⇑(measure.map (λ (ω : Ω₁), M₁ x₁ ω)) P₁) sorry sorry _ _
    with ⟨t, ht⟩,
  rw ht,
  apply ennreal.sub_le_iff_le_add.2,
  rw [add_comm, measure.map_apply, measure.smul_apply, 
    measure.map_apply],
  apply p.dp x₀ x₁ (odp_set_for p none ∩ t) hx,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
end

include hδ
lemma induction_step 
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) 
    (ε - εusage p o₁) (δ - p.δ)) : 
  diff_private_aux (P₁ ⊗ P₂) 
    (λ ω, prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2))
    (λ ω, prod.mk (M₁ x₁ ω.1) (M₂₁ (M₁ x₁ ω.1) ω.2)) ε δ :=
λ s,
calc 
  (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} =
  (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} : rfl
  ... = ∑' (i : option p.index), 
    (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s ∩ (odp_set_for p i).prod univ} : 
  begin
    rw ←measure_Union _,
    apply congr_arg,
    convert preimage_Union,
    rw ←split_set p s,
    sorry,
    sorry,
    sorry,
  end
... ≤ ∑' (i : option p.index), 
  (ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s ∩ (odp_set_for p i).prod univ} +
    pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i) +
  (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i})  : 
begin
  refine tsum_mono _ _ _,
  sorry,-- TODO: summable
  sorry, -- TODO: summable
  intro i,
  apply inequality_slice,
  simp,
  apply hM₂,
end
... = ∑' (b : option p.index),
      ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd) ∈
             s ∩ (odp_set_for p b).prod univ}
    + ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + ∑' (i : option p.index), (δ - p.δ) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}  : 
begin
  unfold pos_hahn,
  rw [tsum_add, tsum_add],
  sorry,-- TODO: summable
  sorry,-- TODO: summable
  sorry,-- TODO: summable
  sorry,-- TODO: summable
end
... = ε.exp * ∑' (b : option p.index),
      (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd) ∈
             s ∩ (odp_set_for p b).prod univ}
    + ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + (δ - p.δ) * ∑' (i : option p.index), P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}  : 
sorry -- Technical issue here: multiplication in ennreal is not continuous
... = ε.exp * (P₁ ⊗ P₂) {ω | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    pos_hahn P₁ x₀ x₁ M₁ (εusage_for p none) (odp_set_for p none) +
  (δ - p.δ) * P₁ (⋃ (i : option p.index), {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}) : 
begin
  have : (⋃ i, (λ ω : Ω₁ × Ω₂, (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd)) ⁻¹'
              (s ∩ (odp_set_for p i).prod univ))
               = (λ ω, (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd)) ⁻¹' s,
  { rw [←preimage_Union], 
    rw ←split_set p s,
  },
  rw sum_pos_hahn,
  rw ←measure_Union _,
  rw ←measure_Union _,
  congr,
  exact this,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
end
... ≤ ε.exp * (P₁ ⊗ P₂) {ω | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    p.δ + (δ - p.δ) : 
begin
  refine add_le_add _ _,
  { refine add_le_add_left _ _,
    apply pos_hahn_none,
    apply hx },
  { convert ennreal.mul_le_mul _ _,
    exact (mul_one _).symm,
    exact le_refl _,
    apply prob_le_one }
end
... = exp ε * (P₁ ⊗ P₂) {ω | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} + δ : 
begin
  rw add_assoc,
  rw ennreal.add_sub_cancel_of_le,
  exact hδ,
end
