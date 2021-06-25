import .dp
import measure_theory.pi

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

noncomputable def odp_composition₀_aux (bit : bool) : 
  Π (acc : list O) (ε δ : ℝ≥0∞) (ω : list Ω), list O
| acc ε δ [] := acc
| acc ε δ (ω :: ωs) := 
  let 𝒜_choice := 𝒜 acc ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let acc := acc ++ [o] in
  let ε := ε - εusage 𝒜_choice.odp_partition o in
  let δ := δ - δusage 𝒜_choice.odp_partition o in
  odp_composition₀_aux acc ε δ ωs

noncomputable def odp_composition₀ (bit : bool) : Π (ε δ : ℝ≥0∞) (ωs : list Ω), list O := 
odp_composition₀_aux 𝒜 bit []

variables (bit : bool) (acc acc₁ acc₂ : list O) (o : O) (ε δ : ℝ≥0∞) (ω : Ω)(ωs : list Ω)

lemma append_odp_composition₀_aux : 
  acc₁ ++ (odp_composition₀_aux (λ os, 𝒜 (acc₁ ++ os)) bit acc₂ ε δ ωs)
  = odp_composition₀_aux 𝒜 bit (acc₁ ++ acc₂) ε δ ωs :=
begin
  induction ωs generalizing acc₂ ε δ,
  { simp [odp_composition₀_aux] },
  { unfold odp_composition₀_aux,
    simp [ωs_ih] }
end

lemma append_odp_composition₀_aux' : 
  acc ++ (odp_composition₀_aux (λ os, 𝒜 (acc ++ os)) bit [] ε δ ωs) 
    = odp_composition₀_aux 𝒜 bit acc ε δ ωs :=
by simp [append_odp_composition₀_aux 𝒜 bit acc [] ε δ ωs]

lemma cons_odp_composition₀_aux : 
  o :: (odp_composition₀_aux (λ os, 𝒜 (o :: os)) bit [] ε δ ωs) 
    = odp_composition₀_aux 𝒜 bit [o] ε δ ωs :=
by {rw ←append_odp_composition₀_aux' 𝒜 bit [o] ε δ ωs, simp}

lemma odp_composition₀_nil : 
  odp_composition₀ 𝒜 bit ε δ [] = [] := rfl

lemma odp_composition₀_cons : 
  odp_composition₀ 𝒜 bit ε δ (ω :: ωs) = 
  let 𝒜_choice := 𝒜 [] ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) ω in
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  let δ' := δ - δusage 𝒜_choice.odp_partition o in
  let 𝒜' := (λ os, 𝒜 (o :: os)) in
  o :: odp_composition₀ 𝒜' bit ε' δ' ωs := 
by simp [odp_composition₀, odp_composition₀_aux, cons_odp_composition₀_aux]

@[simp]
lemma length_odp_composition₀ : 
  (odp_composition₀ 𝒜 bit ε δ ωs).length = ωs.length :=
begin
  induction ωs generalizing 𝒜 ε δ,
  { refl },
  { simp [odp_composition₀_cons, ωs_ih] }
end

-- TODO: move
def fin.to_list {α : Type*} : Π {n : ℕ} (a : fin n → α), list α
| 0 a := []
| (n + 1) a := vec_head a :: fin.to_list (vec_tail a)

-- TODO: move
def list.to_fin {α : Type*} : Π (l : list α), fin (l.length) → α
| [] := ![]
| (x :: xs) := vec_cons x (xs.to_fin)

-- TODO: move
@[simp]
lemma fin.length_to_list {α : Type*} : ∀ {n : ℕ} (a : fin n → α),
  (fin.to_list a).length = n
| 0 a := rfl
| (n + 1) a := by simp [fin.to_list, fin.length_to_list]

noncomputable def odp_composition (n : ℕ) (bit : bool) (ε δ : ℝ≥0∞) (ωs : fin n → Ω) : fin n → O := 
cast (by rw [length_odp_composition₀, fin.length_to_list]) 
  (odp_composition₀ 𝒜 bit ε δ (fin.to_list ωs)).to_fin


theorem main (n : ℕ) :
diff_private_aux (measure.pi (λ i : fin n, P))
  (λ ω, odp_composition 𝒜 n ff ε δ)
  (λ ω, odp_composition 𝒜 n tt ε δ) ε δ := sorry