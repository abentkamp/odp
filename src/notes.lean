import measure_theory.prod

open measure_theory

variables {Ω : Type} [measurable_space Ω]
variables (Pr : measure Ω) [hPr : sigma_finite Pr]

variables (O : Type) [measurable_space O] 
variables (X Y : Ω → O) [measurable X] [measurable Y] 

variables (V : set (O × O)) [measurable_set V] 

-- Conditional Probs:
noncomputable def measure_theory.measure.cond (A : set Ω) := (Pr A)⁻¹ • Pr.restrict A

open measure_theory

-- lemma measure.inter_le_left (A B : set Ω) : Pr (A ∩ B) ≤ Pr A := 
-- by simp [measure_mono]

lemma Pr_cond (A B : set Ω) [measurable_set A] [hB : measurable_set B] : 
  Pr A * Pr.cond A B = Pr (A ∩ B) :=
  sorry
-- begin
--   unfold measure_theory.measure.cond,
--   rw [measure.smul_apply, measure.restrict_apply],
--   by_cases h : Pr A = 0,
--   { have : Pr (A ∩ B) ≤ 0,
--     { rw ←h, apply measure.inter_le_left },
--     simp only [h, ennreal.inv_zero, zero_mul],
--     apply le_antisymm,
--     apply measure.zero_le,
--     sorry,
--     apply this },
--     rw [←mul_assoc, mul_inv_of_self],
--   sorry,
--   -- measurability,
--   -- apply (le_zero_iff.1 _).symm,
-- end




example : Pr {ω : Ω | (X ω, Y ω) ∈ V} 
  = sorry = sorry :=
calc
Pr {ω : Ω | (X ω, Y ω) ∈ V} 
  = Pr (X ⁻¹' {o : O | (o, Y ω) ∈ V}) : sorry
... = 
   


example : Pr {ω : Ω | (X ω, Y ω) ∈ V} = sorry :=
calc 
  Pr {ω : Ω | (X ω, Y ω) ∈ V} = Pr ((λ ω : Ω, (X ω, Y ω)) ⁻¹' V) :
    by refl
  ... = measure.map (λ ω : Ω, (X ω, Y ω)) Pr V : 
    begin
      apply (measure.map_apply _ _).symm,
      measurability,
    end
  ... = ∫⁻ (o : O × O) in V, 1 ∂measure.map (λ ω : Ω, (X ω, Y ω)) Pr : 
   by rw [measure_theory.set_lintegral_one]
  ... = sorry :
  begin
   rw ←lintegral_lintegral,
  end
... = sorry : sorry