import .induction_step data.set.basic .missing

open measure_theory ennreal database_type matrix
open_locale ennreal
open_locale matrix

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) [probability_measure P] (O : Type) [measurable_space O]
variables (X : Type) [database_type X] 
variables {P} {O} {X} (𝒜 : adversary P O X)
variables (bit : fin 2) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

noncomputable def algo_step (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ω : fin n → Ω) :=     
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ in
  let ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o in
  let δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ in
  let 𝒜' := λ (os : list O), 𝒜 (o :: os) in 
  odp_composition 𝒜' n bit ε' δ' ω

theorem main (n : ℕ) :
diff_private_aux (P ^^ n)
  (odp_composition 𝒜 n 0 ε δ)
  (odp_composition 𝒜 n 1 ε δ) ε δ :=
begin
  induction n generalizing 𝒜 ε δ,
  case zero : { 
    intro s,
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
    have ih' : ∀ (o₁ : O), diff_private_aux (P ^^ n)
        (λ ω, algo_step 𝒜 o₁ n 0 ε δ ω)
        (λ ω, algo_step 𝒜 o₁ n 1 ε δ ω)
        (ε - εusage (𝒜 [] ε δ).odp_partition o₁)
        (δ - (𝒜 [] ε δ).odp_partition.δ),
      { intro o,
        let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
        let  ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
        let  δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ,
        let  𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os),
        exact ih 𝒜' ε' δ' },
    have h_diff_private_aux_PPn : diff_private_aux (P ⊗ P ^^ n)
      (λ ω, odp_composition 𝒜 (n+1) 0 ε δ (vec_cons ω.1 ω.2))
      (λ ω, odp_composition 𝒜 (n+1) 1 ε δ (vec_cons ω.1 ω.2)) ε δ,
    { haveI : probability_measure (P ^^ n) := 
        sorry, -- TODO
      have hM : ∀ (x : X), measurable ((𝒜 list.nil ε δ).M x) :=
        sorry, 
      have h_ind_step : diff_private_aux (P ⊗ P ^^ n)
        (λ ω, let o := (𝒜 [] ε δ).M ((𝒜 [] ε δ).x 0) ω.1 in 
              (o, algo_step 𝒜 o n 0 ε δ ω.2))
        (λ ω, let o := (𝒜 [] ε δ).M ((𝒜 [] ε δ).x 1) ω.1 in
              (o, algo_step 𝒜 o n 1 ε δ ω.2))
        ε δ,
      { exact @induction_step _ _ _ _ P (P ^^ n) _ _ _ _ _ _ _ _ 
          ((𝒜 list.nil ε δ).x 0) 
          ((𝒜 list.nil ε δ).x 1) 
          (𝒜 list.nil ε δ).hx (λ x ω, (𝒜 [] ε δ).M x ω) hM
          (𝒜 [] ε δ).odp_partition ε δ
          (𝒜 list.nil ε δ).hδ
          (λ o ω, algo_step 𝒜 o n 0 ε δ ω) 
          (λ o ω, algo_step 𝒜 o n 1 ε δ ω) ih' },
      simp only [odp_composition_succ] {zeta := ff},
      apply diff_private_aux_map_inj _ _ _ _ (λ o, (vec_head o, vec_tail o)),
      apply injective_head_tail,
      convert h_ind_step,
      simp only [tail_cons, head_cons, algo_step], 
      simp [algo_step],
    },
    show diff_private_aux (P ^^ (n+1))
      (odp_composition 𝒜 (n+1) 0 ε δ)
      (odp_composition 𝒜 (n+1) 1 ε δ) ε δ,
    { simp only,
      rw [measure.pi_succ (λ i, Ω) (λ i, P)],
      unfold diff_private_aux,
      intro s,
      rw [measure.map_apply, measure.map_apply],
      rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
      revert s,
      exact h_diff_private_aux_PPn,
    
      sorry, --measurability
      sorry, --measurability
      sorry, --measurability
      sorry, --measurability
      sorry, --sigma-finiteness
   } }
end