import .dp

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) (O : Type) [measurable_space O]

variables (X : Type) [database_type X] 

structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_partition : odp_partition P M)
(hε : odp_partition.ε ≤ ε)
(hδ : odp_partition.δ ≤ δ)
(hε_for : ∀ i, odp_partition.ε_for i ≤ ε)
(x : bool → X)
(hx : neighboring (x ff) (x tt))

def adversary := Π (outputs : list O) (ε δ : ℝ≥0∞), adversary_choice P O X ε δ

variables (𝒜 : adversary P O X)

open_locale matrix
open matrix

noncomputable def odp_composition (bit : bool) : Π (outputs : list O) (ε δ : ℝ≥0∞) (n : ℕ) (ω : fin n → Ω), fin n → O
| outputs ε δ 0 ω := ![]
| outputs ε δ (m + 1) ω := 
  let 𝒜_choice := 𝒜 outputs ε δ in 
  let output := 𝒜_choice.M (𝒜_choice.x bit) (ω 0) in
  let outputs := list.cons output outputs in
  let ε := ε - 1 in --TODO compute real epsilon
  let δ := δ - 1 in --TODO compute real delta
  fin.cons output (odp_composition outputs ε δ m (vec_tail ω))