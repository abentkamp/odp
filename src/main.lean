import .induction_step data.set.basic .adversary

/- This file contains the main theorem. (Theorem 7) -/

open measure_theory ennreal database_type matrix
open_locale ennreal
open_locale matrix

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ),
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

/- `Ω` is a sample space with a probability measure `P` on it. -/
variables {Ω : Type} [measurable_space Ω] {P : measure Ω} [probability_measure P]

/- `Ωₐ` is a sample space with an associated probability measure `Pₐ`.
   They are used for randomization of the adversary's decisions. -/
variables (Ωₐ : Type) [measurable_space Ωₐ] (Pₐ : measure Ωₐ) [probability_measure Pₐ]

/- `O` is the type of outputs of mechanisms. -/
variables {O : Type} [measurable_space O]

/- `X` is the type of databases. -/
variables {X : Type} [database_type X] [measurable_space X]

/-- Main Theorem for deterministic adversaries. The randomization `ωₐ` of the
  adversary is fixed here.

  We use `P` as the probablity measure on sample space `Ω` for each of the `n`
  mechanisms, and thus the product measure `P ^^ n` is the probability measure
  on the joint sample space.
-/
theorem odp_composition_theorem_det
  (𝒜 : adversary P Ωₐ O X) (ωₐ : Ωₐ) (ε δ : ℝ≥0∞) (hε : ε < ∞) (n : ℕ) :
  let v bit := odp_composition 𝒜 n bit ωₐ ε δ in
  ∀ (s : set (fin n → O)) (hs : measurable_set s),
    (P ^^ n) {ω | v 0 ω ∈ s} ≤ exp ε * (P ^^ n) {ω | v 1 ω ∈ s} + δ :=
begin
  show diff_private_composition (P ^^ n)
    (odp_composition 𝒜 n 0 ωₐ ε δ)
    (odp_composition 𝒜 n 1 ωₐ ε δ) ε δ,
  induction n generalizing 𝒜 ε δ,
  case zero : {
    intros s hs,
    by_cases h : s = set.univ,
    { simp only [h, set.mem_univ, set.set_of_true],
      refine le_trans _ _,
      exact ε.exp * ⇑(measure.pi (λ (i : fin 0), P)) set.univ,
      refine le_mul_of_one_le_left' _,
      apply one_le_exp,
      exact le_add_of_nonneg_right (zero_le _),
    },
    { simp [set.eq_empty_of_subsingleton_of_not_univ s h] }},
  case succ : n ih {
    have ih' : ∀ (o₁ : O), diff_private_composition (P ^^ n)
        (λ ω, odp_composition₀ 𝒜 o₁ n 0 ωₐ ε δ ω)
        (λ ω, odp_composition₀ 𝒜 o₁ n 1 ωₐ ε δ ω)
        (ε - εusage ((𝒜 0).choose ωₐ ![] ε δ).odp_partition o₁)
        (δ - ((𝒜 0).choose ωₐ ![] ε δ).odp_partition.δ),
      { intro o,
        let 𝒜_choice : adversary_choice P O X ε δ := (𝒜 0).choose ωₐ ![] ε δ,
        let  ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
        let  δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ,
        let  𝒜' : adversary P Ωₐ O X := inform 𝒜 o,
        have hε' : ε' < ∞ := lt_of_le_of_lt (ennreal.sub_le_self _ _) hε,
        exact ih 𝒜' ε' δ' hε' },
    have h_diff_private_composition_PPn : diff_private_composition (P ⊗ P ^^ n)
      (λ ω, odp_composition 𝒜 (n+1) 0 ωₐ ε δ (vec_cons ω.1 ω.2))
      (λ ω, odp_composition 𝒜 (n+1) 1 ωₐ ε δ (vec_cons ω.1 ω.2)) ε δ,
    { have hM : ∀ (x : X), measurable (((𝒜 0).choose ωₐ ![] ε δ).M x),
      { intro x,
        apply (𝒜 0).measurable_M measurable_const measurable_const measurable_const measurable_const measurable_const measurable_id },
      have h_ind_step : diff_private_composition (P ⊗ P ^^ n)
        (λ ω, let o := ((𝒜 0).choose ωₐ ![] ε δ).M (((𝒜 0).choose ωₐ ![] ε δ).x 0) ω.1 in
              (o, odp_composition₀ 𝒜 o n 0 ωₐ ε δ ω.2))
        (λ ω, let o := ((𝒜 0).choose ωₐ ![] ε δ).M (((𝒜 0).choose ωₐ ![] ε δ).x 1) ω.1 in
              (o, odp_composition₀ 𝒜 o n 1 ωₐ ε δ ω.2))
        ε δ,
      { apply induction_step P (P ^^ n)
          (((𝒜 0).choose ωₐ ![] ε δ).x 0)
          (((𝒜 0).choose ωₐ ![] ε δ).x 1)
          ((𝒜 0).choose ωₐ ![] ε δ).hx (λ x ω, ((𝒜 0).choose ωₐ ![] ε δ).M x ω)
          ((𝒜 0).choose ωₐ ![] ε δ).odp_partition hM
          (λ o ω, odp_composition₀ 𝒜 o n 0 ωₐ ε δ ω)
          (λ o ω, odp_composition₀ 𝒜 o n 1 ωₐ ε δ ω),
        exact measurable_odp_composition₀ 𝒜 0 ωₐ _ _,
        exact measurable_odp_composition₀ 𝒜 1 ωₐ _ _,
        exact hε,
        exact ((𝒜 0).choose ωₐ ![] ε δ).hε_for,
        exact ((𝒜 0).choose ωₐ ![] ε δ).hδ,
        exact ih' },
      dunfold odp_composition,
      apply diff_private_composition_map_vec_head_vec_tail,
      convert h_ind_step,
      simp only [tail_cons, head_cons, odp_composition₀],
      simp [odp_composition₀],
    },
    show diff_private_composition (P ^^ (n+1))
      (odp_composition 𝒜 (n+1) 0 ωₐ ε δ)
      (odp_composition 𝒜 (n+1) 1 ωₐ ε δ) ε δ,
    { simp only,
      rw [measure.pi_succ (λ i, Ω) (λ i, P)],
      unfold diff_private_composition,
      intros s hs,
      rw [measure.map_apply, measure.map_apply],
      rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
      revert s hs,
      exact h_diff_private_composition_PPn,
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_odp_composition_det 𝒜 1 ωₐ ε δ hs, --measurability
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_odp_composition_det 𝒜 0 ωₐ ε δ hs, --measurability
      apply_instance
   } }
end

/-- Main Theorem (Theorem 7): For every adversary `𝒜` and for every set of
  views `s` of `𝒜` returned by `odp_composition`, we have that `Pr(v⁰ ∈ s) ≤
  exp ε * Pr(v¹ ∈ s) + δ`.

  We use `P` as the probablity measure on sample space `Ω` for each of the `n`
  mechanisms and `Pₐ` as the probablity measure on sample space `Ωₐ` for the
  adversary. So the joint probability measure is `Pₐ ⊗ P ^^ n`.
-/
theorem odp_composition_theorem 
  (𝒜 : adversary P Ωₐ O X) (ε δ : ℝ≥0∞) (hε : ε < ∞) (n : ℕ) :
  let v bit (ω : Ωₐ × (fin n → Ω)) := odp_composition 𝒜 n bit ω.1 ε δ ω.2 in
  ∀ (s : set (fin n → O)) (hs : measurable_set s),
    (Pₐ ⊗ P ^^ n) {ω | v 0 ω ∈ s} ≤ exp ε * (Pₐ ⊗ P ^^ n) {ω | v 1 ω ∈ s} + δ :=
begin
  have h_measurable_odp_composition : 
    ∀ bit, measurable (λ ω : Ωₐ × (fin n → Ω), odp_composition 𝒜 n bit ω.fst ε δ ω.snd),
  { intros, apply measurable_odp_composition_nondet },
  intros v s hs,
  convert lintegral_mono _,
  { rw measure.prod_apply,
    apply (h_measurable_odp_composition 0) hs },
  { rw measure.prod_apply, 
    rw ←lintegral_const_mul,
    convert (lintegral_add _ _).symm,
    { rw ← mul_one δ,
      convert (lintegral_const δ).symm,
      rw measure_univ },
    { apply measurable.const_mul,
      apply measurable_measure_prod_mk_left,
      apply (h_measurable_odp_composition 1) hs },
    { measurability },
    { apply measurable_measure_prod_mk_left,
      apply (h_measurable_odp_composition 1) hs },
    { apply (h_measurable_odp_composition 1) hs }, },
  intro ωₐ,
  dsimp [v],
  exact odp_composition_theorem_det _ 𝒜 ωₐ ε δ hε n s hs,
end