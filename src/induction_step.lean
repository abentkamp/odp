import .diff_private .missing_integration .missing_unsigned_hahn .missing_pairwise_disjoint .missing_finset .missing_measure .missing_tsum .missing_tsum_ennreal
import topology.instances.ennreal
/-
This file contains the crucial part of the induction step of the main theorem.
-/

open measure_theory ennreal database_type set
open_locale ennreal
open_locale big_operators

local infix ` ⊗ `:50  := measure.prod

/- `Ω₁` and `Ω₂` are sample spaces with associated probability measures `P₁` and `P₂`. -/
variables {Ω₁ Ω₂ : Type} [measurable_space Ω₁] [measurable_space Ω₂] 
variables (P₁ : measure Ω₁) (P₂ : measure Ω₂) [probability_measure P₁] [probability_measure P₂]

/- `O₁` and `O₂` are spaces of outputs. -/
variables {O₁ O₂ : Type} [measurable_space O₁] [measurable_space O₂]

/- `X` is a type of databases. -/
variables {X : Type} [database_type X] (x x₀ x₁ : X) (hx : neighboring x₀ x₁)

/- `M₁` is a ODP mechanism -/
variables (M₁ : X → Ω₁ → O₁) (p : odp_mechanism P₁ M₁)
variables (hM₁ : ∀ x, measurable (M₁ x))

/- `M₂₀` and `M₂₁` are a random variable depending on the output of `M₁` -/
variables (M₂₀ M₂₁ : O₁ → Ω₂ → O₂) 
variables (h_measurable_M₂₀ : measurable (λ (oω : O₁ × Ω₂), M₂₀ oω.1 oω.2))
variables (h_measurable_M₂₁ : measurable (λ (oω : O₁ × Ω₂), M₂₁ oω.1 oω.2))

/- `ε` and `δ` are usually used to denote the total ε-δ-budget. -/
variables (ε δ : ℝ≥0∞) (hε : ε < ∞) (hδ : δusage p ≤ δ)

/-- The `-` in this definition does not yield a signed measure, but only the
positive part of the difference, resulting from Hahn decomposition. -/
noncomputable def pos_hahn : measure O₁ := 
measure.map (λ ω, M₁ x₀ ω) P₁ - ε.exp • measure.map (λ ω, M₁ x₁ ω) P₁


section
include hM₁ hε
/-- Since `pos_hahn` is only missing the negative part of the actual difference
of the two measures, the following inequality holds: -/
lemma pos_hahn_prop : 
  measure.map (λ ω₁, M₁ x₀ ω₁) P₁ 
    ≤ ε.exp • measure.map (λ ω₁, M₁ x₁ ω₁) P₁ + pos_hahn P₁ x₀ x₁ M₁ ε :=
begin
  rw [add_comm, pos_hahn],
  haveI : ∀ x, finite_measure (measure.map (λ (ω : Ω₁), M₁ x ω) P₁) :=
  begin
    intro x,
    apply finite_measure.map _, 
    apply hM₁, 
    apply_instance
  end,
  haveI : finite_measure (ε.exp • measure.map (λ (ω : Ω₁), M₁ x₁ ω) P₁) := 
  begin
    apply finite_measure.smul,
    apply exp_lt_top_of_lt_top,
    apply hε,
  end,
  apply measure.le_sub_add,
end
end

/-- We reformulate an assumption about `diff_private_composition` on `M₂₀` and `M₂₁`
    to incoparate a minimum of `1` and another value. We know that the measure is
    at most `1` because it is a probability measure. -/
lemma diff_private_composition_min (s : set (O₁ × O₂)) (hs : measurable_set s) (o₁ : O₁) 
  (hM₂ : ∀ o₁ : O₁, diff_private_composition P₂ (M₂₀ o₁) (M₂₁ o₁) (ε - εusage p o₁) (δ - δusage p)) : 
  P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s} 
    ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - δusage p) :=
calc P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s} = min 1 (P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}) :
begin
  rw min_eq_right,
  apply prob_le_one,
end
... ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s} + (δ - δusage p)) :
begin
  refine min_le_min (le_refl _) _,
  apply hM₂ o₁ {o₂ : O₂ | (o₁, o₂) ∈ s},
  apply measurable_prod_mk_left hs,
end
... ≤ min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - δusage p) :
begin
  rw min_add_distrib,
  exact le_trans (min_le_right _ _) (add_le_add (le_refl _) (min_le_right _ _)),
end

  -- Some measurability results (TODO: Deduplicate with above)
section
include hM₁ h_measurable_M₂₀
@[measurability]
lemma measurable_M₂_M₁ : measurable (λ (x : Ω₁ × Ω₂), M₂₀ (M₁ x₀ x.fst) x.snd) :=
begin
  apply measurable.comp h_measurable_M₂₀ (measurable.prod_mk _ _),
  measurability
end
end

section
include hM₁ h_measurable_M₂₀
@[measurability]
lemma measurable_set_preimage_s_inter (s: set (O₁ × O₂)) (hs: measurable_set s) :
∀ (i : option p.index), measurable_set
    {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.fst, M₂₀ (M₁ x₀ ω.fst) ω.snd) ∈ s ∩ (odp_set_for p i).prod univ} :=
begin
  intro i,
  apply measurable.prod_mk,
  measurability
end
end

section
include h_measurable_M₂₀
@[measurability]
lemma measurable_P₂_M₂ (s : set (O₁ × O₂)) (hs : measurable_set s) :
  measurable (λ (a : O₁), P₂ {ω₂ : Ω₂ | (a, M₂₀ a ω₂) ∈ s}) :=
begin
  have : measurable_set {oω : O₁ × Ω₂ | (oω.1, M₂₀ oω.1 oω.2) ∈ s}, -- This was tricky!
  { apply measurable.prod,
    measurability },
  apply measurable_measure_prod_mk_left this,
  apply_instance
end
end

section
include hM₁ h_measurable_M₂₀
@[measurability]
lemma measurable_set_M₁_M₂ (s : set (O₁ × O₂)) (hs : measurable_set s) :
  measurable_set {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.fst, M₂₀ (M₁ x₀ ω.fst) ω.snd) ∈ s} :=
begin
  apply measurable.prod_mk,
  measurability
end
end

section
include hM₁ hε h_measurable_M₂₀ h_measurable_M₂₁
/-- First, we prove an inequality on a single set `odp_set_for p i` of the ODP partition. -/
lemma inequality_slice (s : set (O₁ × O₂)) 
  (hs : measurable_set s)
  (i : option p.index) 
  (hsi : s ⊆ (odp_set_for p i).prod univ)
  (h_εusage_for : εusage_for p i ≤ ε)
  (hM₂ : ∀ o₁ : O₁, diff_private_composition P₂ (M₂₀ o₁) (M₂₁ o₁) (ε - εusage p o₁) (δ - δusage p)) :
(P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} 
  ≤ ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s}
    + pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :=
calc
  (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} 
 = ∫⁻ (ω₁ : Ω₁), P₂ {ω₂ : Ω₂ | (M₁ x₀ ω₁, M₂₀ (M₁ x₀ ω₁) ω₂) ∈ s} ∂P₁ : 
begin
  rw measure.prod_apply,
  refl,
  apply measurable_set_M₁_M₂ _ M₁ hM₁ _ h_measurable_M₂₀ s hs,
end
... = ∫⁻ (o₁ : O₁), P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ : 
begin
  rw lintegral_map,
  apply measurable_P₂_M₂ P₂ _ h_measurable_M₂₀ s hs,
  apply hM₁,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i, P₂ {ω₂ : Ω₂ | (o₁, M₂₀ o₁ ω₂) ∈ s}
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ : 
begin
  rw set_lintegral_nonzero,
  apply measurable_set_odp_set_for,
  { intros o₁ ho₁,
    convert measure_empty,
    rw eq_empty_iff_forall_not_mem,
    exact λ ω₂ hω₂, ho₁ (mem_prod.1 (hsi hω₂)).1 }
end
... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
  min 1 ((ε - εusage p o₁).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - δusage p)
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ :
begin
  apply lintegral_mono,
  intro o₁,
  apply diff_private_composition_min,
  apply hs,
  apply hM₂,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i,
  min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) + (δ - δusage p)
  ∂measure.map (λ ω₁, M₁ x₀ ω₁) P₁ :
begin
  apply set_lintegral_fun_congr,
  apply measurable_set_odp_set_for,
  intros ω₁ hω₁,
  simp_rw εusage_eq_εusage_for hω₁,
end
... = ∫⁻ (o₁ : O₁) in odp_set_for p i,
      min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s})
    ∂measure.map (λ (ω₁ : Ω₁), M₁ x₀ ω₁) P₁
    + (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :
begin
  rw [lintegral_add, lintegral_const, measure.restrict_apply_univ, measure.map_apply],
  refl,
  apply hM₁,
  measurability,
end
... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
      min 1 ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) 
    ∂((εusage_for p i).exp • measure.map (λ ω₁, M₁ x₁ ω₁) P₁ + pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i))
    + (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} :
begin
  refine add_le_add _ (le_refl _),
  refine measure_theory.lintegral_mono' _ (le_refl _),
  refine measure.restrict_mono (λ x hx, hx) _,
  apply @pos_hahn_prop _ _ P₁ _ _ _ _ _ x₀ x₁  M₁ hM₁ _,
  apply εusage_for_lt_infty
end
 ... ≤ ∫⁻ (o₁ : O₁) in odp_set_for p i,
      ((ε - εusage_for p i).exp * P₂ {ω₂ : Ω₂ | (o₁, M₂₁ o₁ ω₂) ∈ s}) 
      ∂(εusage_for p i).exp • measure.map (λ (ω₁ : Ω₁), M₁ x₁ ω₁) P₁ +
    ∫⁻ (o₁ : O₁) in odp_set_for p i, 1 ∂pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i)
  + (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
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
     + (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
begin
  rw [lintegral_const_mul, measure.restrict_smul, lintegral_smul_measure],
  rw [←mul_assoc, ←exp_add, ennreal.sub_add_cancel_of_le],
  rw [lintegral_one, measure.restrict_apply_univ],
  apply h_εusage_for,
  apply measurable_P₂_M₂ P₂ _ h_measurable_M₂₁ s hs,
end
 ... = 
 ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i) +
  (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i} : 
begin
  rw ←set_lintegral_nonzero,
  rw lintegral_map,
  rw measure.prod_apply,
  refl,
  apply measurable_set_M₁_M₂ _ M₁ hM₁ _ h_measurable_M₂₁ s hs,
  apply measurable_P₂_M₂ P₂ _ h_measurable_M₂₁ s hs,
  exact hM₁ _,
  apply measurable_set_odp_set_for,
  { intros o₁ ho₁,
    convert measure_empty,
    rw eq_empty_iff_forall_not_mem,
    exact λ ω₂ hω₂, ho₁ (mem_prod.1 (hsi hω₂)).1 },
end
end

section
include hx hM₁
/-- The volume of `pos_hahn` on the `none` slice is bounded by `p.δ`. -/
lemma pos_hahn_none : pos_hahn P₁ x₀ x₁ M₁ (εusage_for p none) (odp_set_for p none) ≤ p.δ :=
begin
  have := p.dp x₀ x₁ (odp_set_for p none) (by measurability) hx,
  rw [pos_hahn], 
  haveI : ∀ x, finite_measure ((measure.map (λ (ω : Ω₁), M₁ x ω)) P₁) :=
    λ x, measure_theory.finite_measure.map _ (hM₁ _),
  haveI : finite_measure ((εusage_for p none).exp • (measure.map (λ (ω : Ω₁), M₁ x₁ ω)) P₁) := 
  begin 
    apply measure_theory.finite_measure.smul,
    apply ennreal.exp_lt_top_of_lt_top,
    apply εusage_for_lt_infty,
  end,
  rcases @measure.sub_apply_finite _ _
    (measure.map (λ (ω : Ω₁), M₁ x₀ ω) P₁)
    ((εusage_for p none).exp • ⇑(measure.map (λ (ω : Ω₁), M₁ x₁ ω)) P₁) _ _ _ _
    with ⟨t, ht₁, ht₂⟩,
  rw ht₂,
  apply ennreal.sub_le_iff_le_add.2,
  rw [add_comm, measure.map_apply, measure.smul_apply, 
    measure.map_apply],
  apply p.dp x₀ x₁ (odp_set_for p none ∩ t) (by measurability) hx,
  measurability,
end
end


section
include hx hM₁
lemma pos_hahn_some (i : p.index) : 
  pos_hahn P₁ x₀ x₁ M₁ (εusage_for p (some i)) (odp_set_for p (some i))
    ≤ p.δ_for i :=
begin --TODO: Dediplicate with above?
  rw [pos_hahn], 
  haveI : ∀ x, finite_measure ((measure.map (λ (ω : Ω₁), M₁ x ω)) P₁) :=
    λ x, measure_theory.finite_measure.map _ (hM₁ _),
  haveI : finite_measure ((εusage_for p (some i)).exp • (measure.map (λ (ω : Ω₁), M₁ x₁ ω)) P₁) := 
  begin 
    apply measure_theory.finite_measure.smul,
    apply ennreal.exp_lt_top_of_lt_top,
    apply εusage_for_lt_infty,
  end,
  rcases @measure.sub_apply_finite _ _
    (measure.map (λ (ω : Ω₁), M₁ x₀ ω) P₁)
    ((εusage_for p (some i)).exp • ⇑(measure.map (λ (ω : Ω₁), M₁ x₁ ω)) P₁) _ _ _ _
    with ⟨t, ht₁, ht₂⟩,
  rw ht₂,
  apply ennreal.sub_le_iff_le_add.2,
  rw [add_comm, measure.map_apply, measure.smul_apply, 
    measure.map_apply],
  apply p.odp i,
  { apply set.inter_subset_left },
  measurability
end
end

section
include hx hM₁
lemma sum_pos_hahn : 
  ∑' i : option p.index, pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    ≤ δusage p :=
begin
  rw [tsum_option _ ennreal.summable, add_comm],
  unfold δusage,
  refine add_le_add _ _,
  { exact pos_hahn_none _ _ _ hx _ p hM₁, },
  { refine tsum_le_tsum _ ennreal.summable ennreal.summable,
    exact pos_hahn_some _ _ _ hx _ p hM₁,}
end
end

include hx hδ hM₁ hε h_measurable_M₂₀ h_measurable_M₂₁
/-- This is the crucial part of the induction step of the main theorem. -/
lemma induction_step 
  (h_εusage_for : ∀ i, εusage_for p i ≤ ε)
  (hM₂ : ∀ o₁ : O₁, diff_private_composition P₂ (M₂₀ o₁) (M₂₁ o₁) 
    (ε - εusage p o₁) (δ - δusage p)) : 
  diff_private_composition (P₁ ⊗ P₂) 
    (λ ω, prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2))
    (λ ω, prod.mk (M₁ x₁ ω.1) (M₂₁ (M₁ x₁ ω.1) ω.2)) ε δ :=
begin
  intros s hs,
  haveI : encodable (option p.index) := @encodable.option _ p.encodable,
calc
  (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} =
  (P₁ ⊗ P₂) {ω | prod.mk (M₁ x₀ ω.1) (M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s} : rfl
  ... = ∑' (i : option p.index), 
    (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₀ ω.1, M₂₀ (M₁ x₀ ω.1) ω.2) ∈ s ∩ (odp_set_for p i).prod univ} : 
begin
  rw ←measure_Union _,
  apply congr_arg,
  convert ←preimage_Union,
  rw ←split_set p s,
  apply measurable_set_preimage_s_inter _ _ _ _ hM₁ _ h_measurable_M₂₀ s hs,
  apply_instance,
  apply_instance,
  { apply pairwise_disjoint_on_preimage,
    apply pairwise_disjoint_on_inter,
    apply pairwise_disjoint_on_prod (odp_set_for p) univ,
    apply pairwise_disjoint_on_odp_set_for, }
end
... ≤ ∑' (i : option p.index), 
  (ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s ∩ (odp_set_for p i).prod univ} +
    pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i) +
  (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i})  : 
begin
  refine tsum_mono ennreal.summable ennreal.summable _,
  intro i,
  apply inequality_slice,
  apply hM₁,
  apply h_measurable_M₂₀,
  apply h_measurable_M₂₁,
  apply hε,
  { measurability },
  simp,
  apply h_εusage_for,
  apply hM₂,
end
... = ∑' (b : option p.index),
      ε.exp * (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd) ∈
             s ∩ (odp_set_for p b).prod univ}
    + ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + ∑' (i : option p.index), (δ - δusage p) * P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}  : 
begin
  unfold pos_hahn,
  rw [tsum_add, tsum_add],
  { apply ennreal.summable },
  { apply ennreal.summable },
  { apply ennreal.summable },
  { apply ennreal.summable },
end
... = ε.exp * ∑' (b : option p.index),
      (P₁ ⊗ P₂) {ω : Ω₁ × Ω₂ | (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd) ∈
             s ∩ (odp_set_for p b).prod univ}
    + ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i)
    + (δ - δusage p) * ∑' (i : option p.index), P₁ {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}  : 
begin
  rw ennreal.tsum_mul_left,
  rw ennreal.tsum_mul_left,
end  
... = ε.exp * (P₁ ⊗ P₂) {ω | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    ∑' (i : option p.index), pos_hahn P₁ x₀ x₁ M₁ (εusage_for p i) (odp_set_for p i) +
  (δ - δusage p) * P₁ (⋃ (i : option p.index), {ω₁ : Ω₁ | M₁ x₀ ω₁ ∈ odp_set_for p i}) : 
begin
  have : (⋃ i, (λ ω : Ω₁ × Ω₂, (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd)) ⁻¹'
              (s ∩ (odp_set_for p i).prod univ))
               = (λ ω, (M₁ x₁ ω.fst, M₂₁ (M₁ x₁ ω.fst) ω.snd)) ⁻¹' s,
  { rw [←preimage_Union], 
    rw ←split_set p s,
  },
  congr,
  { rw ←measure_Union _, 
    congr,
    exact this,
    apply measurable_set_preimage_s_inter _ _ _ _ hM₁ _ h_measurable_M₂₁ s hs,
    apply_instance,
    apply_instance,
    { apply pairwise_disjoint_on_preimage, -- TODO: Deduplicate
      apply pairwise_disjoint_on_inter,
      apply pairwise_disjoint_on_prod (odp_set_for p) univ,
      apply pairwise_disjoint_on_odp_set_for, }, },
  { rw ←measure_Union _, 
    { measurability },
    apply_instance,
    { apply pairwise_disjoint_on_preimage,
      apply pairwise_disjoint_on_odp_set_for, } }
end
... ≤ ε.exp * (P₁ ⊗ P₂) {ω | (M₁ x₁ ω.1, M₂₁ (M₁ x₁ ω.1) ω.2) ∈ s} +
    δusage p + (δ - δusage p) : 
begin
  refine add_le_add _ _,
  { refine add_le_add_left _ _,
    apply sum_pos_hahn,
    apply hx,
    apply hM₁ },
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
end