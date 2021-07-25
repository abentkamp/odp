import measure_theory.prod
import .missing_ennreal

class database_type (X : Type*) :=
(neighboring : X → X → Prop)

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) {O : Type} {O' : Type}

variables {X : Type} [database_type X] (M : X → Ω → O) (M₀ : Ω → O) (M₁ : Ω → O) (M₀' : Ω → O') (M₁' : Ω → O')

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

variables {P} {M}

def odp_index (p : odp_partition P M) (o : O) : option p.index := 
  if h : ∃ i : p.index, o ∈ p.partition i then some (classical.some h) else none

def εusage_for (p : odp_partition P M) : option p.index → ℝ≥0∞
| none := p.ε
| (some i) :=  p.ε_for i

def εusage (p : odp_partition P M) (o : O) := εusage_for p (odp_index p o)

def δusage_for (p : odp_partition P M) : option p.index → ℝ≥0∞
| none := p.δ
| (some i) := 0

def δusage (p : odp_partition P M) (o : O) := δusage_for p (odp_index p o)

def odp_set_for (p : odp_partition P M) : option p.index → set O
| none := set.univ \ ⋃ i, p.partition i
| (some i) :=  p.partition i

def omega_set_for (p : odp_partition P M) (g : Ω → O) (i : option p.index) : set Ω := g ⁻¹' odp_set_for p i

lemma odp_index_unique {o : O} {p : odp_partition P M} {i j : p.index}
  (hi : o ∈ p.partition i) (hj : o ∈ p.partition j) : i = j :=
begin
  by_contra h,
  exact p.disjoint i j h ⟨hi, hj⟩,
end

lemma odp_index_of_mem_partition {o : O} {p : odp_partition P M} {i : p.index}
  (hi : o ∈ p.partition i) : odp_index p o = some i :=
begin
  have hex : ∃ j, o ∈ p.partition j := ⟨i, hi⟩,
  simp only [odp_index, hex, dif_pos],
  exact odp_index_unique (classical.some_spec hex) hi
end

lemma δusage_eq_δusage_for {o : O} {p : odp_partition P M} {i : option p.index} (ho : o ∈ odp_set_for p i) :
  δusage p o = δusage_for p i :=
begin
  cases i,
  { simp [odp_index, δusage, λ h, set.not_mem_of_mem_diff ho (set.mem_Union.2 h)] },
  { unfold odp_set_for at ho, 
    rw [δusage, odp_index_of_mem_partition ho] }
end

lemma εusage_eq_εusage_for {o : O} {p : odp_partition P M} {i : option p.index} (ho : o ∈ odp_set_for p i) :
  εusage p o = εusage_for p i :=
begin
  cases i,
  { simp [odp_index, εusage, λ h, set.not_mem_of_mem_diff ho (set.mem_Union.2 h)] },
  { unfold odp_set_for at ho, 
    rw [εusage, odp_index_of_mem_partition ho] }
end

lemma mem_odp_set_for_odp_index (p : odp_partition P M) (o : O) : o ∈ odp_set_for p (odp_index p o) :=
begin
  by_cases h : ∃ (i : p.index), o ∈ p.partition i,
  { simp only [odp_set_for, odp_index, h, dif_pos],
    exact classical.some_spec2 (λ i, o ∈ p.partition i) (λ a h, h) },
  { simp [odp_set_for, odp_index, h, dif_neg] }
end

lemma union_odp_set_for_eq_univ (p : odp_partition P M) : (⋃ i, odp_set_for p i) = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intros o,
  apply set.mem_Union.2,
  use odp_index p o,
  apply mem_odp_set_for_odp_index
end

lemma diff_private_aux_map_inj (f : O → O') (hf : function.injective f) : diff_private_aux P (λ ω, f (M₀ ω)) (λ ω, f (M₁ ω)) ε δ → diff_private_aux P M₀ M₁ ε δ :=
begin
  intros h s,
  rw [←set.preimage_image_eq s hf],
  exact h (f '' s)
end
