
import .test4 data.set.basic

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) [probability_measure P] (O : Type) [measurable_space O]

variables (X : Type) [database_type X] 


variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix


variables (bit : bool) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

instance is_empty_fin_zero : is_empty (fin 0) :=
is_empty.mk (λ x, nat.not_lt_zero x.1 x.2)

instance subsingleton_fun_is_empty (α β : Type*) [is_empty α] : 
  subsingleton (α → β) :=
begin
  apply subsingleton.intro,
  intros a b,
  ext x,
  apply is_empty.elim _ x,
  apply_instance,
end

lemma set.eq_empty_of_subsingleton_of_not_univ {α : Type*} [subsingleton α]
  (s : set α) (hs : s ≠ set.univ) : s = ∅ :=
begin
  apply set.eq_empty_of_subset_empty,
  intros a ha,
  apply hs,
  apply set.eq_univ_iff_forall.2,
  intro b,
  rw subsingleton.elim b a,
  apply ha
end

-- lemma xx (n : nat) : ∀ (i : fin n.succ), sigma_finite ((λ (i : fin n.succ), P) i) := sorry

theorem main (n : ℕ) :
diff_private_aux (P ^^ n)
  (odp_composition 𝒜 n ff ε δ)
  (odp_composition 𝒜 n tt ε δ) ε δ :=
begin
  induction n generalizing 𝒜 ε δ,
  case zero : { intro s,
    by_cases h : s = set.univ,
    { simp [h], sorry -- This is relatively simple arithmetic
    },
    { simp [set.eq_empty_of_subsingleton_of_not_univ s h] }},
  case succ : n ih {
    simp only,
    rw [measure.pi_succ (λ i, Ω) (λ i, P)],
    unfold diff_private_aux,
    intro s,
    rw [measure.map_apply, measure.map_apply],
    rw [set.preimage_set_of_eq, set.preimage_set_of_eq],
    revert s,
    change diff_private_aux (P ⊗ P ^^ n)
      (λ x, odp_composition 𝒜 n.succ ff ε δ (vec_cons x.fst x.snd))
      (λ x, odp_composition 𝒜 n.succ tt ε δ (vec_cons x.fst x.snd)) ε δ,
    simp only [odp_composition_succ] {zeta := ff},
    apply diff_private_aux_map_inj _ _ _ _ (λ o, (vec_head o, vec_tail o)),
    sorry, --injectivity of (vec_head, vec_tail)
    haveI : probability_measure ((λ (μ : measure Ω) (n : ℕ), measure.pi (λ (i : fin n), μ)) P n) := 
      sorry, -- TODO
    convert induction_step P (P ^^ n)
      ((𝒜 list.nil ε δ).x ff) ((𝒜 list.nil ε δ).x tt) (𝒜 list.nil ε δ).hx (λ x ω, (𝒜 [] ε δ).M x ω) 
      _ ε δ
      -- (𝒜 list.nil ε δ).hδ
       (λ o ω,
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
       ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
       δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ,
       𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os)
   in odp_composition 𝒜' n ff ε' δ' ω) 
   (λ o ω,
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
       ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
       δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ,
       𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os)
   in odp_composition 𝒜' n tt ε' δ' ω) _,
   simp only [tail_cons, head_cons],
   simp,
   apply (𝒜 _ _ _).odp_partition,
   { intro o,
      let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
      let  ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
      let  δ' : ℝ≥0∞ := δ - 𝒜_choice.odp_partition.δ,
      let  𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os),
     exact ih 𝒜' ε' δ',
   },
   sorry, --measurability
   sorry, --measurability
   sorry, --measurability
   sorry, --measurability
   sorry, --sigma-finiteness
    sorry }
end