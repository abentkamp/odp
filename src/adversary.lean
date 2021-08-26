import .dp .missing_measure .missing_matrix

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) (O : Type) [measurable_space O]

variables (X : Type) [database_type X] [measurable_space X] -- TODO: What does it mean for X to be measurable?

structure adversary_choice (ε δ : ℝ≥0∞) :=
(M : X → Ω → O)
(odp_partition : odp_partition P M)
(hε : odp_partition.ε ≤ ε)
(hδ : odp_partition.δ ≤ δ)
(hε_for : ∀ i, odp_partition.ε_for i ≤ ε)
(x : fin 2 → X)
(hx : neighboring (x 0) (x 1))

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
  measurable (λ (a : α), εusage (choose (os a) (ε a) (δ a)).odp_partition (o a)))
(measurable_δ : 
  ∀ {α : Type} [measurable_space α] {os : α → (fin n → O)} {ε δ : α → ℝ≥0∞},
  measurable os → measurable ε →  measurable δ →
  measurable (λ (a : α), (choose (os a) (ε a) (δ a)).odp_partition.δ))

def adversary := Π (n : ℕ), adversary_n P O X n

lemma εusage_for_le_ε {ε δ : ℝ≥0∞} (𝒜_choice : adversary_choice P O X ε δ) (i : option 𝒜_choice.odp_partition.index) : 
  εusage_for 𝒜_choice.odp_partition i ≤ ε := 
begin 
  cases i,
  apply 𝒜_choice.hε,
  apply 𝒜_choice.hε_for
end

variables {P} {O} {X} (𝒜 : adversary P O X)

open_locale matrix
open matrix

def inform_n {n : ℕ} (𝒜 : adversary_n P O X (n+1)) (o : O) : adversary_n P O X n :=
⟨λ os, 𝒜.choose (vec_cons o os),
begin 
  intros,
  apply 𝒜.measurable_M,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_x,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_ε,
  apply measurable.fin_cons,
  measurability
end,
begin 
  intros,
  apply 𝒜.measurable_δ,
  apply measurable.fin_cons,
  measurability
end⟩

def inform (𝒜 : adversary P O X) (o : O) : adversary P O X :=
λ n, inform_n (𝒜 (n+1)) o

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

noncomputable def odp_composition : Π (𝒜 : adversary P O X) (n : ℕ) (bit : fin 2) (ε δ : ℝ≥0∞) (ωs : fin n → Ω), fin n → O
| 𝒜 0 bit ε δ ωs := ![]
| 𝒜 (n+1) bit ε δ ωs :=
  let 𝒜_choice := (𝒜 0).choose ![] ε δ in 
  let o := 𝒜_choice.M (𝒜_choice.x bit) (vec_head ωs) in
  let ε' := ε - εusage 𝒜_choice.odp_partition o in
  let δ' := δ - 𝒜_choice.odp_partition.δ in
  let 𝒜' := inform 𝒜 o in
  vec_cons o (odp_composition 𝒜' n bit ε' δ' (vec_tail ωs))
