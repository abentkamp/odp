
import .test4

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) (O : Type) [measurable_space O]

variables (X : Type) [database_type X] 


variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix


variables (bit : bool) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

local infix ` ^^ `:60 := λ (μ : measure_theory.measure _) (n : ℕ), 
  measure.pi (λ i : fin n, μ)

local infix ` ⊗ `:50  := measure.prod

theorem main (n : ℕ) :
diff_private_aux (P ^^ n)
  (odp_composition 𝒜 n ff ε δ)
  (odp_composition 𝒜 n tt ε δ) ε δ :=
begin
  cases n,
  { sorry },
  { simp only,
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
    sorry,
    convert induction_step P (P ^^ n) O _ X
      ((𝒜 list.nil ε δ).x ff) ((𝒜 list.nil ε δ).x tt) (λ x ω, (𝒜 [] ε δ).M x ω) _ _ _ (λ o ω,
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
       ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
       δ' : ℝ≥0∞ := δ - δusage 𝒜_choice.odp_partition o,
       𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os)
   in odp_composition 𝒜' n ff ε' δ' ω) 
   (λ o ω,
  let 𝒜_choice : adversary_choice P O X ε δ := 𝒜 list.nil ε δ,
       ε' : ℝ≥0∞ := ε - εusage 𝒜_choice.odp_partition o,
       δ' : ℝ≥0∞ := δ - δusage 𝒜_choice.odp_partition o,
       𝒜' : list O → Π (ε δ : ℝ≥0∞), adversary_choice P O X ε δ := λ (os : list O), 𝒜 (o :: os)
   in odp_composition 𝒜' n tt ε' δ' ω) _,
   simp only [tail_cons, head_cons],
   simp,
   apply (𝒜 _ _ _).odp_partition,
   { sorry --TODO: use induction hypothesis here
   },
   sorry,
   sorry,
   sorry,
   sorry,
   sorry,
    }
end