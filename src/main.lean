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
variables (bit : fin 2) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (hε : ε < ∞) (ω : Ω)(ωs : list Ω)

noncomputable def algo_step (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ω : fin n → Ω) :=     
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ in
  let ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o in
  let δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ in
  let 𝒜' := λ (os : list O), 𝒜 (o :: os) in 
  odp_composition 𝒜' n bit ε' δ' ω

--TODO: move
def vec_cons.equiv (n : ℕ) : O × (fin n → O) ≃ (fin n.succ → O) :=
⟨λ x, vec_cons x.1 x.2,
 λ x, (vec_head x, vec_tail x), 
 begin intro x, simp end, 
 begin intro x, simp end⟩

lemma diff_private_aux_map_vec_head_vec_tail {Ω : Type} [measurable_space Ω] (P : measure Ω) {n : ℕ} (M₀ M₁ : Ω → fin n.succ → O) : 
  let f := (λ o : fin n.succ → O, (vec_head o, vec_tail o)) in
  diff_private_aux P (λ ω, f (M₀ ω)) (λ ω, f (M₁ ω)) ε δ → diff_private_aux P M₀ M₁ ε δ :=
begin
  intros f h s hs,
  rw [←set.preimage_image_eq s (injective_head_tail n)],
  refine h (f '' s) _,
  have : measurable_set ((λ x : _ × _, vec_cons x.1 x.2) ⁻¹' s),
  { apply measurable.fin_cons,
    apply measurable_fst,
    apply measurable_snd,
    exact hs },
  convert this,
  exact equiv.image_eq_preimage (vec_cons.equiv n).symm s,
end


lemma measurable_set_odp_composition {n : ℕ}:
  measurable (odp_composition 𝒜 n bit ε δ) :=
begin
  induction n with n ih generalizing 𝒜 ε δ,
  case zero { show measurable (λ ω, ![]), by apply measurable_const },
  case succ { show measurable (λ ω, odp_composition 𝒜 (n + 1) bit ε δ ω),
    suffices : measurable (λ ω, odp_composition 𝒜 (n + 1) bit ε δ (vec_cons (vec_head ω) (vec_tail ω))),
      by simpa only [cons_head_tail] using this,
    simp_rw [odp_composition_succ],
    apply measurable.fin_cons,
    { have : ∀ b, measurable ((𝒜 [] ε δ).M b), sorry,
      measurability },
    { sorry }, }
end

lemma measurable_algo_step {n : ℕ} : 
  measurable (λ (oω : O × (fin n → Ω)), algo_step 𝒜 oω.1 n bit ε δ oω.2) :=
begin
  unfold algo_step,
  sorry
end

include hε
theorem main (n : ℕ) :
diff_private_aux (P ^^ n)
  (odp_composition 𝒜 n 0 ε δ)
  (odp_composition 𝒜 n 1 ε δ) ε δ :=
begin
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
        have hε' : ε' < ∞ := lt_of_le_of_lt (ennreal.sub_le_self _ _) hε,
        exact ih 𝒜' ε' δ' hε' },
    have h_diff_private_aux_PPn : diff_private_aux (P ⊗ P ^^ n)
      (λ ω, odp_composition 𝒜 (n+1) 0 ε δ (vec_cons ω.1 ω.2))
      (λ ω, odp_composition 𝒜 (n+1) 1 ε δ (vec_cons ω.1 ω.2)) ε δ,
    { have hM : ∀ (x : X), measurable ((𝒜 list.nil ε δ).M x) :=
        sorry, 
      have h_ind_step : diff_private_aux (P ⊗ P ^^ n)
        (λ ω, let o := (𝒜 [] ε δ).M ((𝒜 [] ε δ).x 0) ω.1 in 
              (o, algo_step 𝒜 o n 0 ε δ ω.2))
        (λ ω, let o := (𝒜 [] ε δ).M ((𝒜 [] ε δ).x 1) ω.1 in
              (o, algo_step 𝒜 o n 1 ε δ ω.2))
        ε δ,
      { apply induction_step P (P ^^ n)
          ((𝒜 list.nil ε δ).x 0) 
          ((𝒜 list.nil ε δ).x 1)
          (𝒜 list.nil ε δ).hx (λ x ω, (𝒜 [] ε δ).M x ω)-- hM,
          (𝒜 [] ε δ).odp_partition hM
          (λ o ω, algo_step 𝒜 o n 0 ε δ ω) 
          (λ o ω, algo_step 𝒜 o n 1 ε δ ω),
        exact measurable_algo_step 𝒜 0 _ _, -- measurablity,
        exact measurable_algo_step 𝒜 1 _ _, -- measurablity,
        exact hε,
        exact (𝒜 list.nil ε δ).hδ,
        exact (λ i, εusage_for_le_ε _ _ _ _ _),
        exact ih' },
      simp only [odp_composition_succ] {zeta := ff},
      apply diff_private_aux_map_vec_head_vec_tail,
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
      intros s hs,
      rw [measure.map_apply, measure.map_apply],
      rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
      revert s hs,
      exact h_diff_private_aux_PPn,
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_set_odp_composition 𝒜 1 ε δ hs, --measurability
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_set_odp_composition 𝒜 0 ε δ hs, --measurability
      apply_instance
   } }
end