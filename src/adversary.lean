import .diff_private .missing_measure .missing_matrix

/-
This file defines the role of the adversary and the ODP algorithm.
-/

open measure_theory ennreal database_type matrix
open_locale ennreal
open_locale matrix

/- `Ω` is a sample space with an associated probability measure `P`. -/
variables {Ω : Type} [measurable_space Ω] (P : measure Ω) [probability_measure P] 

/- `O` is the type of outputs of meachanisms. -/
variables (O : Type) [measurable_space O]

/- `X` is a type of databases. -/
variables (X : Type) [database_type X] [measurable_space X]

/-- At each iteration of the algorithm, the adversary can choose an ODP
mechanism and two neighboring databases. The ODP mechanism must not exceed the
remaining ε-δ-budget. -/
structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_mechanism : odp_mechanism P M)
(hε : odp_mechanism.ε ≤ ε)
(hδ : odp_mechanism.δ ≤ δ)
(hε_for : ∀ i, odp_mechanism.ε_for i ≤ ε)
(x : fin 2 → X)
(hx : neighboring (x 0) (x 1))

/-- The structure `adversary_n` represents an adversary after `n` iterations.
Given `n` outputs and the remaining ε-δ-budget, the adversary must make a
choice. There a couple of measurability requirements on the adversary
as a function from previous outputs and budget to the adversary's choice. -/
structure adversary_n (n : ℕ) :=
(choose : Π (outputs : fin n → O) (ε δ : ℝ≥0∞), adversary_choice P O X ε δ)
(measurable_M : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞} {x : α → X} {ω : α → Ω},
  measurable os → measurable ε → measurable δ → measurable x → measurable ω →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).M (x a) (ω a)))
(measurable_x : 
  ∀ (bit : fin 2) {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable os → measurable ε → measurable δ →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).x bit))
(measurable_ε : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {o : α → O} {ε δ : α → ℝ≥0∞},
  measurable os → measurable o → measurable ε →  measurable δ →
  measurable (λ (a : α), εusage (choose (os a) (ε a) (δ a)).odp_mechanism (o a)))
(measurable_δ : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable os → measurable ε →  measurable δ →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).odp_mechanism.δ))

/-- An adversary is a collection of `adversary_n` structures for each number of iterations `n`. -/
def adversary := Π (n : ℕ), adversary_n P O X n

/-- An `adversary_choice` is constructed so that it can never violate the ε-budget. -/
lemma εusage_for_le_ε {ε δ : ℝ≥0∞} (𝒜_choice : adversary_choice P O X ε δ) (i : option 𝒜_choice.odp_mechanism.index) : 
  εusage_for 𝒜_choice.odp_mechanism i ≤ ε := 
begin 
  cases i,
  apply 𝒜_choice.hε,
  apply 𝒜_choice.hε_for
end

variables {P} {O} {X} (𝒜 : adversary P O X)

/-- We can produce an adversary for `n` previous outputs from an adversary for
`n + 1` previous outputs by informing them about a new output. -/
def inform_n {n : ℕ} (𝒜 : adversary_n P O X (n+1)) (o : O) : adversary_n P O X n :=
⟨λ os, 𝒜.choose (vec_cons o os),
begin 
  intros,
  apply 𝒜.measurable_M (measurable.fin_cons _ _),
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_x _ (measurable.fin_cons _ _),
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_ε (measurable.fin_cons _ _),
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_δ (measurable.fin_cons _ _),
  measurability
end⟩

/-- The adversary `inform 𝒜 o` is `𝒜` after having been informed about a new
output `o`. -/
def inform (𝒜 : adversary P O X) (o : O) : adversary P O X :=
λ n, inform_n (𝒜 (n+1)) o

/-- The adversary `inform_vec 𝒜 m os` is `𝒜` after having been informed about
`m` new outputs `os`. -/
def inform_vec : adversary P O X → Π (m : ℕ), (fin m → O) → adversary P O X
| 𝒜 0 os := 𝒜
| 𝒜 (m+1) os := inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os)

lemma inform_inform_vec_comm (𝒜 : adversary P O X) {m : ℕ} (os : fin m.succ → O) : 
inform (inform_vec 𝒜 m (vec_butlast os)) (vec_last os) 
= inform_vec (inform 𝒜 (vec_head os)) m (vec_tail os)
:= begin
  induction m with m ih,
  { refl },
  { unfold inform_vec, 
  rw ih,
  rw [head_butlast, last_tail, butlast_tail], }
end

lemma inform_vec_choose (𝒜 : adversary P O X) {m : ℕ} (os : fin m → O) : 
(inform_vec 𝒜 m os 0).choose ![] = (𝒜 m).choose os :=
begin
  induction m with m ih generalizing os 𝒜,
  { unfold inform_vec, congr' },
  { unfold inform_vec,
    rw inform_inform_vec_comm,
    rw ih,
    unfold inform,
    unfold inform_n,
    unfold adversary_n.choose,
    simp, }
end

lemma inform_inform_vec (𝒜 : adversary P O X) (m : ℕ) (o : O) (os : fin m → O) : 
  inform (inform_vec 𝒜 m os) o = inform_vec 𝒜 (m+1) (vec_snoc os o) :=
by rw [inform_vec, butlast_snoc, last_snoc]

/-- This is the main algorithm. -/
noncomputable def odp_composition : Π (𝒜 : adversary P O X) (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ωs : fin n → Ω), fin n → O
| 𝒜 0 bit ε δ ωs := ![]
| 𝒜 (n+1) bit ε δ ωs := 
-- At each iteration:
  -- The adversary makes a choice.
  let 𝒜_choice := (𝒜 0).choose ![] ε δ in 
  -- We sample the chosen meachanism.
  let o := 𝒜_choice.M (𝒜_choice.x bit) (vec_head ωs) in 
  -- We calculate the remaining ε-budget.
  let ε' := ε - εusage 𝒜_choice.odp_mechanism o in 
  -- We calculate the remaining δ-budget.
  let δ' := δ - 𝒜_choice.odp_mechanism.δ in 
  -- We inform the adversary about the new output.
  let 𝒜' := inform 𝒜 o in 
  -- We return the output and enter the next iteration for the remaining outputs.
  vec_cons o (odp_composition 𝒜' n bit ε' δ' (vec_tail ωs)) 
