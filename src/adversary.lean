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

variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix

noncomputable def odp_composition_aux (bit : bool) : 
  Π (acc : list O) (ε δ : ℝ≥0∞) (ω : list Ω), list O
| acc ε δ [] := acc
| acc ε δ (ω :: ωs) := 
  let 𝒜_choice := 𝒜 acc ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let acc := acc ++ [o] in
  let ε := ε - εusage 𝒜_choice.odp_partition o in
  let δ := δ - δusage 𝒜_choice.odp_partition o in
  odp_composition_aux acc ε δ ωs

noncomputable def odp_composition (bit : bool) : Π (ε δ : ℝ≥0∞) (ωs : list Ω), list O := 
odp_composition_aux 𝒜 bit []

variables (bit : bool) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

lemma append_odp_composition_aux : 
  acc₁ ++ (odp_composition_aux (λ os, 𝒜 (acc₁ ++ os)) bit acc₂ ε δ ωs)
  = odp_composition_aux 𝒜 bit (acc₁ ++ acc₂) ε δ ωs :=
begin
  induction ωs generalizing acc₂ ε δ,
  { simp [odp_composition_aux] },
  { unfold odp_composition_aux,
    simp [ωs_ih] }
end

lemma append_odp_composition_aux' : 
  acc ++ (odp_composition_aux (λ os, 𝒜 (acc ++ os)) bit [] ε δ ωs) 
    = odp_composition_aux 𝒜 bit acc ε δ ωs :=
by simp [append_odp_composition_aux 𝒜 bit acc [] ε δ ωs]

lemma cons_odp_composition_aux : 
  o :: (odp_composition_aux (λ os, 𝒜 (o :: os)) bit [] ε δ ωs) 
    = odp_composition_aux 𝒜 bit [o] ε δ ωs :=
by {rw ←append_odp_composition_aux' 𝒜 bit [o] ε δ ωs, simp}

lemma odp_composition_nil : 
  odp_composition 𝒜 bit ε δ [] = [] := rfl

lemma odp_composition_cons : 
  odp_composition 𝒜 bit ε δ (ω :: ωs) = 
  let 𝒜_choice := 𝒜 [] ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  let δ' := δ - δusage 𝒜_choice.odp_partition o in
  let 𝒜' := (λ os, 𝒜 (o :: os)) in
  o :: odp_composition 𝒜' bit ε' δ' ωs := 
by simp [odp_composition, odp_composition_aux, cons_odp_composition_aux]

lemma length_odp_composition : 
  (odp_composition 𝒜 bit ε δ ωs).length = ωs.length :=
begin
  induction ωs generalizing 𝒜 ε δ,
  { refl },
  { simp [odp_composition_cons, ωs_ih] }
end