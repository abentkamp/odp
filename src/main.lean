/-

TODO:
- Concrete Example
- measurable space of methods
- More comments

-/

import .induction_step data.set.basic .adversary

open measure_theory ennreal database_type matrix
open_locale ennreal
open_locale matrix

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) [probability_measure P] (O : Type) [measurable_space O]
variables (X : Type) [database_type X] [measurable_space X]
variables {P} {O} {X} (𝒜 : adversary P O X)
variables (bit : fin 2) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (hε : ε < ∞) (ω : Ω) (ωs : list Ω)

noncomputable def algo_step (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ω : fin n → Ω) :=     
  let 𝒜_choice : adversary_choice P O X ε δ := (𝒜 0).choose ![] ε δ in
  let ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_mechanism o in
  let δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_mechanism.δ in
  let 𝒜' := inform 𝒜 o in 
  odp_composition 𝒜' n bit ε' δ' ω


--TODO: move
def vec_cons.equiv (n : ℕ) : O × (fin n → O) ≃ (fin n.succ → O) :=
⟨λ x, vec_cons x.1 x.2,
 λ x, (vec_head x, vec_tail x), 
 begin intro x, simp end, 
 begin intro x, simp end⟩

lemma diff_private_composition_map_vec_head_vec_tail {Ω : Type} [measurable_space Ω] (P : measure Ω) {n : ℕ} (M₀ M₁ : Ω → fin n.succ → O) : 
  let f := (λ o : fin n.succ → O, (vec_head o, vec_tail o)) in
  diff_private_composition P (λ ω, f (M₀ ω)) (λ ω, f (M₁ ω)) ε δ → diff_private_composition P M₀ M₁ ε δ :=
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

example {c : ℕ} {f : ℕ → ℕ} (hf : ∀ x, f x = c) : (λ y, f y) =  (λ y, c) :=
begin
  simp_rw hf,
end

-- I haven't been able to prove this using an adversary that gets fed a list instead of a vector
-- because lists are currently not instantiated as a measurable space.
lemma measurable_set_odp_composition {n : ℕ} {α : Type} [measurable_space α] 
  (m : ℕ) (os : α → (fin m → O)) (ε δ : α → ℝ≥0∞) (ω : α → (fin n → Ω))
  (hos : measurable os) (hε : measurable ε) (hδ : measurable δ) (hω : measurable ω) :
  measurable (λ a : α, odp_composition (inform_vec 𝒜 m (os a)) n bit (ε a) (δ a) (ω a)) :=
begin
  induction n with n ih generalizing m ε δ os,
  case zero { show measurable (λ ω, ![]), by apply measurable_const },
  case succ { show measurable (λ a, odp_composition (inform_vec 𝒜 m (os a)) (n+1) bit (ε a) (δ a) (ω a)),
    suffices : measurable (λ a, odp_composition (inform_vec 𝒜 m (os a)) (n+1) bit (ε a) (δ a) (vec_cons (vec_head (ω a)) (vec_tail (ω a)))),
      by simpa only [cons_head_tail] using this,
    unfold odp_composition,
    apply measurable.fin_cons,
    { simp_rw [cons_head_tail, inform_vec_choose 𝒜],
      apply (𝒜 m).measurable_M hos hε hδ _ (measurable.comp measurable.vec_head hω),
      apply (𝒜 m).measurable_x bit hos hε hδ, },
    { simp_rw [inform_inform_vec, matrix.cons_head_tail, inform_vec_choose 𝒜],
      apply ih (λ a, vec_tail (ω a)) _ (m+1),
      apply measurable.vec_snoc,
      exact hos,
      apply (𝒜 m).measurable_M hos hε hδ _ (measurable.comp measurable.vec_head hω),
      apply (𝒜 m).measurable_x bit hos hε hδ,
      { apply measurable.sub hε, --TODO: why can't I rewrite inform_vec_choose here?
        suffices : measurable (λ (a : α),
          εusage (( 𝒜 m ).choose (os a) (ε a) (δ a)).odp_mechanism
            (((𝒜 m).choose (os a) (ε a) (δ a)).M (((𝒜 m).choose (os a) (ε a) (δ a)).x bit) (vec_head (ω a)))),
        { convert this, apply funext, intro i,
          rw inform_vec_choose 𝒜 (os i) },
        refine (𝒜 m).measurable_ε hos _ hε hδ,
        apply (𝒜 m).measurable_M hos hε hδ _ (measurable.comp measurable.vec_head hω),
        apply (𝒜 m).measurable_x bit hos hε hδ, },
      { apply measurable.sub hδ,
        suffices : measurable (λ (a : α), 
          ((𝒜 m).choose (os a) (ε a) (δ a)).odp_mechanism.δ),
        { convert this, apply funext, intro i,
          rw inform_vec_choose 𝒜 (os i) },
        exact (𝒜 m).measurable_δ hos hε hδ },
      exact measurable.comp measurable.vec_tail hω } }
end

lemma measurable_set_odp_composition' {n : ℕ}:
  measurable (odp_composition 𝒜 n bit ε δ) :=
begin
  apply measurable_set_odp_composition 
    𝒜 bit 0 (λ_, ![]) (λ_, ε) (λ_, δ) (λ ω, ω),
  measurability,
end

lemma measurable_algo_step {n : ℕ} : 
  measurable (λ (oω : O × (fin n → Ω)), algo_step 𝒜 oω.1 n bit ε δ oω.2) :=
begin
  apply measurable_set_odp_composition 𝒜 bit 1
    (λ oω : O × (fin n → Ω), ![oω.1])
    (λ oω : O × (fin n → Ω), ε - εusage ((𝒜 0).choose vec_empty ε δ).odp_mechanism oω.fst)
    (λ oω : O × (fin n → Ω), δ - ((𝒜 0).choose vec_empty ε δ).odp_mechanism.δ)
    (λ oω : O × (fin n → Ω), oω.2),
  apply measurable.vec_cons,
  measurability
end

include hε
theorem main (n : ℕ) :
diff_private_composition (P ^^ n)
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
    have ih' : ∀ (o₁ : O), diff_private_composition (P ^^ n)
        (λ ω, algo_step 𝒜 o₁ n 0 ε δ ω)
        (λ ω, algo_step 𝒜 o₁ n 1 ε δ ω)
        (ε - εusage ((𝒜 0).choose ![] ε δ).odp_mechanism o₁)
        (δ - ((𝒜 0).choose ![] ε δ).odp_mechanism.δ),
      { intro o,
        let 𝒜_choice : adversary_choice P O X ε δ := (𝒜 0).choose ![] ε δ,
        let  ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_mechanism o,
        let  δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_mechanism.δ,
        let  𝒜' : adversary P O X := inform 𝒜 o,
        have hε' : ε' < ∞ := lt_of_le_of_lt (ennreal.sub_le_self _ _) hε,
        exact ih 𝒜' ε' δ' hε' },
    have h_diff_private_composition_PPn : diff_private_composition (P ⊗ P ^^ n)
      (λ ω, odp_composition 𝒜 (n+1) 0 ε δ (vec_cons ω.1 ω.2))
      (λ ω, odp_composition 𝒜 (n+1) 1 ε δ (vec_cons ω.1 ω.2)) ε δ,
    { have hM : ∀ (x : X), measurable (((𝒜 0).choose ![] ε δ).M x),
      { intro x,
        apply (𝒜 0).measurable_M measurable_const measurable_const measurable_const measurable_const measurable_id }, 
      have h_ind_step : diff_private_composition (P ⊗ P ^^ n)
        (λ ω, let o := ((𝒜 0).choose ![] ε δ).M (((𝒜 0).choose ![] ε δ).x 0) ω.1 in 
              (o, algo_step 𝒜 o n 0 ε δ ω.2))
        (λ ω, let o := ((𝒜 0).choose ![] ε δ).M (((𝒜 0).choose ![] ε δ).x 1) ω.1 in
              (o, algo_step 𝒜 o n 1 ε δ ω.2))
        ε δ,
      { apply induction_step P (P ^^ n)
          (((𝒜 0).choose ![] ε δ).x 0) 
          (((𝒜 0).choose ![] ε δ).x 1)
          ((𝒜 0).choose ![] ε δ).hx (λ x ω, ((𝒜 0).choose ![] ε δ).M x ω)-- hM,
          ((𝒜 0).choose ![] ε δ).odp_mechanism hM
          (λ o ω, algo_step 𝒜 o n 0 ε δ ω) 
          (λ o ω, algo_step 𝒜 o n 1 ε δ ω),
        exact measurable_algo_step 𝒜 0 _ _, -- measurablity,
        exact measurable_algo_step 𝒜 1 _ _, -- measurablity,
        exact hε,
        exact ((𝒜 0).choose ![] ε δ).hδ,
        exact (λ i, εusage_for_le_ε _ _ _ _ _),
        exact ih' },
      dunfold odp_composition,
      apply diff_private_composition_map_vec_head_vec_tail,
      convert h_ind_step,
      simp only [tail_cons, head_cons, algo_step],
      simp [algo_step],
    },
    show diff_private_composition (P ^^ (n+1))
      (odp_composition 𝒜 (n+1) 0 ε δ)
      (odp_composition 𝒜 (n+1) 1 ε δ) ε δ,
    { simp only,
      rw [measure.pi_succ (λ i, Ω) (λ i, P)],
      unfold diff_private_composition,
      intros s hs,
      rw [measure.map_apply, measure.map_apply],
      rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
      revert s hs,
      exact h_diff_private_composition_PPn,
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_set_odp_composition' 𝒜 1 ε δ hs, --measurability
      exact measurable.fin_cons (measurable_fst) (measurable_snd),
      exact measurable_set_odp_composition' 𝒜 0 ε δ hs, --measurability
      apply_instance
   } }
end