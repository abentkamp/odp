import .adversary

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂] 

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [sigma_finite P₁] [sigma_finite P₂]

variables (O₁ O₂ : Type) [measurable_space O₁] [measurable_space O₂]

variables (X : Type) [database_type X] (x₀ x₁ : X) (hx : neighboring x₀ x₁)

variables (M₁ : X → Ω₁ → O₁) (p : odp_partition P₁ M₁)

variables (ε δ : ℝ≥0∞) 

variables (M₂₀ M₂₁ : O₁ → Ω₂ → O₂) 
  

local infix ` ⊗ `:50  := measure.prod

#check lintegral_Union
#check union_odp_set_for_eq_univ
#check measure_theory.measure.restrict_univ


lemma sum_lintegral_odp_set_for (f : O₁ → ℝ≥0∞) (P : measure O₁): 
  (∫⁻ (o : O₁), f o ∂P) = ∑' (i : option p.index), ∫⁻ (o : O₁) in odp_set_for p i, f o ∂P :=
begin
  haveI := p.encodable,
  rw ←lintegral_Union, 
  rw union_odp_set_for_eq_univ,
  rw measure_theory.measure.restrict_univ,
  sorry,
  sorry
end

open set

lemma split_set (s : set (O₁ × O₂)) : s = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod univ :=
calc s = s ∩ (set.prod univ univ) : by simp
... = s ∩ ((set.Union (λ i, odp_set_for p i)).prod univ) : by rw ←union_odp_set_for_eq_univ _
... = s ∩ (⋃ (i : option p.index), (odp_set_for p i).prod univ) : by rw set.Union_prod_const
... = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod univ : by rw inter_Union

lemma induction_step 
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) 
    (ε - εusage p o₁) (δ - δusage p o₁)) : 
  diff_private_aux (P₁ ⊗ P₂) 
    (λ ω, prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2))
    (λ ω, prod.mk (M₁ x₁ ω.1) (M₂₁ (M₁ x₁ ω.1) ω.2)) ε δ :=
λ s,
calc 
  (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} =
  (P₁ ⊗ P₂) ((λ ω, prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2)) ⁻¹' s) : rfl
  ... = ∑' (i : option p.index), 
    (P₁ ⊗ P₂) ((λ ω, (M₁ x₀ ω.fst, M₂₀ (M₁ x₀ ω.fst) ω.snd)) ⁻¹' (s ∩ (odp_set_for p i).prod univ)) : 
  begin
    rw ←measure_Union _,
    rw ←preimage_Union,
    rw ←split_set P₁ O₁ O₂ _ _ p s,
    sorry,
    sorry,
    sorry,
  end
--    ∫⁻ (ω₁ : Ω₁), P₂ ((λ ω₂, (M₁ x₀ ω₁, M₂₀ (M₁ x₀ ω₁) ω₂)) ⁻¹' s) ∂P₁ : 
--   begin rw measure.prod_apply, refl, sorry end
-- ... = ∫⁻ (o₁ : O₁), P₂ ((λ ω₂, (o₁, M₂₀ o₁ ω₂)) ⁻¹' s) ∂(measure.map (λ ω₁, M₁ x₀ ω₁) P₁) : 
--   begin rw lintegral_map, sorry, sorry end
-- ... = ∑' (i : option p.index), ∫⁻ (o₁ : O₁) in odp_set_for p i, P₂ ((λ ω₂, (o₁, M₂₀ o₁ ω₂)) ⁻¹' s) ∂(measure.map (λ ω₁, M₁ x₀ ω₁) P₁) : 
--   begin rw sum_lintegral_odp_set_for _ _ _, sorry end
... ≤ exp ε * (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₁ ω.1) (M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} + δ : sorry
