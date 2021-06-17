import measure_theory.prod
import .missing_ennreal

class database_type (X : Type*) :=
(neighboring : X → X → Prop)

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) {O : Type} [measurable_space O]

variables {X : Type} [database_type X] (M : X → Ω → O) 

variables (ε δ : ℝ≥0∞)

def diff_private :=
  ∀ (x y : X) (s : set O), neighboring x y → 
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ