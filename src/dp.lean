import measure_theory.prod
import .missing_ennreal

class database_type (X : Type*) :=
(neighboring : X → X → Prop)

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) {O : Type} [measurable_space O]

variables {X : Type} [database_type X] (M : X → Ω → O) (M₀ : Ω → O) (M₁ : Ω → O)

variables (ε δ : ℝ≥0∞)

def diff_private_aux :=
  ∀ (s : set O),
  P {ω : Ω | M₀ ω ∈ s} ≤ exp ε * P {ω : Ω | M₁ ω ∈ s} + δ

def diff_private :=
  ∀ (x y : X) (s : set O), neighboring x y → 
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ

def output_diff_private (s : set O) :=
  ∀ (x y : X) (t : set O) (hs : t ⊆ s), neighboring x y → 
  P {ω : Ω | M x ω ∈ t} ≤ exp ε * P {ω : Ω | M y ω ∈ t}

structure odp_partition :=
(ε δ : ℝ≥0∞)
(index : Type*) 
[encodable : encodable index] 
(partition : index → set O) 
(ε_for : index → ℝ≥0∞)
(disjoint : pairwise (disjoint on partition))  
(dp : diff_private P M ε δ)
(odp : ∀ i, output_diff_private P M (ε_for i) (partition i))

open_locale classical
noncomputable theory

def odb_index (p : odp_partition P M) (o : O) : option p.index := 
  if h : ∃ i : p.index, o ∈ p.partition i then some (classical.some h) else none

def εusage (p : odp_partition P M) (o : O) := match odb_index P M p o with
| none := p.ε
| some i :=  p.ε_for i
end

def δusage (p : odp_partition P M) (o : O) := match odb_index P M p o with
| none := p.δ
| some i := 0
end

