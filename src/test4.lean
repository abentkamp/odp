import .adversary
import missing_integration
import measure_theory.measure_space

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂] 

variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [probability_measure P₁] [probability_measure P₂]

variables (O₁ O₂ : Type) [measurable_space O₁] [measurable_space O₂]

variables (X : Type) [database_type X] (x x₀ x₁ : X) (hx : neighboring x₀ x₁)

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

lemma δusage_on_odp_set_for (i : option p.index) : 
  (∫⁻ (ω₁ : Ω₁) in M₁ x ⁻¹' (odp_set_for p i), δusage p (M₁ x ω₁) ∂P₁) 
 = ∫⁻ (ω₁ : Ω₁) in M₁ x ⁻¹' (odp_set_for p i), δusage_for p i ∂P₁ :=
begin
  rw set_lintegral_fun_congr _,
  { intros ω₁ hω₁,
    exact δusage_eq_δusage_for hω₁ },
  sorry
end

lemma xx (s : set (O₁ × O₂)) (i : option p.index) (hs : s ⊆ (odp_set_for p i).prod univ)
  (hM₂ : ∀ o₁ : O₁, diff_private_aux P₂ (M₂₀ o₁) (M₂₁ o₁) 
    (ε - εusage p o₁) (δ - δusage p o₁)):
(P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x ω.1, M₂₀ (M₁ x ω.1) ω.2) ∈ s} 
≤ sorry :=
let V := M₁ x ⁻¹' (odp_set_for p i) in
calc 
(P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x ω.1, M₂₀ (M₁ x ω.1) ω.2) ∈ s}  = 
∫⁻ (ω₁ : Ω₁), P₂ {ω₂ : Ω₂ | (M₁ x ω₁, M₂₀ (M₁ x ω₁) ω₂) ∈ s} ∂P₁ : 
begin
  rw measure.prod_apply,
  refl,
  sorry
end
... = ∫⁻ (ω₁ : Ω₁) in V, P₂ {ω₂ : Ω₂ | (M₁ x ω₁, M₂₀ (M₁ x ω₁) ω₂) ∈ s} ∂P₁ :begin
  rw set_lintegral_nonzero,
  sorry,
  { intros ω₁ hω₁,
    convert measure_empty,
    rw eq_empty_iff_forall_not_mem,
    exact λ ω₂ hω₂, hω₁ (mem_prod.1 (hs hω₂)).1 }
end
...  ≤ ∫⁻ (ω₁ : Ω₁) in V, (ε - εusage p (M₁ x ω₁)).exp *
    P₂ {ω : Ω₂ | M₂₁ (M₁ x ω₁) ω ∈ {o₂ : O₂ | (M₁ x ω₁, o₂) ∈ s}} +
  (δ - δusage p (M₁ x ω₁)) ∂P₁ :
  begin 
    apply lintegral_mono,
    intro ω₁,
    exact hM₂ (M₁ x ω₁) {o₂ : O₂ | (M₁ x ω₁, o₂) ∈ s},
 end
...  = ∫⁻ (a : Ω₁) in
    V,
    (ε - εusage p (M₁ x a)).exp *
      P₂ {ω : Ω₂ | M₂₁ (M₁ x a) ω ∈ {o₂ : O₂ | (M₁ x a, o₂) ∈ s}} ∂P₁ +
  (δ * P₁ V - δusage_for p i * P₁ V) : begin rw [lintegral_add, lintegral_sub, lintegral_const, measure.restrict_apply_univ],
rw [δusage_on_odp_set_for, lintegral_const, measure.restrict_apply_univ],
    sorry, sorry, end
...  ≤ sorry : sorry

include x₁ hx
lemma xxx (s : set (O₁ × O₂)) (i : option p.index) (hs : s ⊆ (odp_set_for p i).prod univ) :
(P₁ ⊗ P₂) ((λ ω, (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2)) ⁻¹' s)
≤ (εusage_for p i).exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₀ (M₁ x₁ ω.1) ω.2) ∈ s} +
  δusage_for p i 
:=
calc 
(P₁ ⊗ P₂) ((λ ω, (M₁ x₀ ω.fst, M₂₀ (M₁ x₀ ω.fst) ω.snd)) ⁻¹' s)
= ∫⁻ (ω₂ : Ω₂), P₁ ((λ (ω₁ : Ω₁), (M₁ x₀ ω₁, M₂₀ (M₁ x₀ ω₁) ω₂)) ⁻¹' s) ∂P₂ : 
       begin 
        rw [← measure.prod_swap, measure.map_apply, measure.prod_apply], 
        simp only [preimage_preimage], 
        refl,
        sorry,
        sorry,
        sorry, end
... ≤ ∫⁻ (ω₂ : Ω₂), (εusage_for p i).exp * P₁ {ω : Ω₁ | (M₁ x₁ ω, M₂₀ (M₁ x₁ ω) ω₂) ∈ s} + δusage_for p i ∂P₂ : begin 
  apply lintegral_mono,
  cases i,
  { exact λ ω₂, p.dp x₀ x₁ {o₁ | (o₁, M₂₀ o₁ ω₂) ∈ s} hx },
  { intro ω₂,
    simp_rw [δusage_for, add_zero],
    refine p.odp i x₀ x₁ {o₁ | (o₁, M₂₀ o₁ ω₂) ∈ s} _ hx,
    exact λ o₁ ho₁, (mem_prod.1 (hs ho₁)).1, }, end
... = (εusage_for p i).exp *
    ∫⁻ (ω₂ : Ω₂), P₁ {ω₁ : Ω₁ | (M₁ x₁ ω₁, M₂₀ (M₁ x₁ ω₁) ω₂) ∈ s} ∂P₂ +
  δusage_for p i * P₂ univ :
begin rw lintegral_add,
    rw lintegral_const,
    rw lintegral_const_mul,
    sorry, sorry, sorry end
... = (εusage_for p i).exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₀ (M₁ x₁ ω.1) ω.2) ∈ s} +
  δusage_for p i: 
begin 
        rw [← measure.prod_swap, measure.map_apply, measure.prod_apply, measure_univ, mul_one],
        refl,
    sorry, sorry, sorry
        end
... = sorry : sorry


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
