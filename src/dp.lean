import measure_theory.constructions.prod
import .missing_ennreal

class database_type (X : Type*) :=
(neighboring : X → X → Prop)

open measure_theory ennreal database_type
open_locale ennreal

variables {Ω : Type} [measurable_space Ω] (P : measure Ω) {O : Type} {O' : Type} [measurable_space O] [measurable_space O']

variables {X : Type} [database_type X] (M : X → Ω → O) (M₀ : Ω → O) (M₁ : Ω → O) (M₀' : Ω → O') (M₁' : Ω → O')

variables (ε δ : ℝ≥0∞)

/- Differential provacy for compositions M₀, M₁ of mechanisms -/
def diff_private_composition :=
  ∀ (s : set O) (hs : measurable_set s),
  P {ω : Ω | M₀ ω ∈ s} ≤ exp ε * P {ω : Ω | M₁ ω ∈ s} + δ

-- TODO: need to add measurability assumption on s?
def diff_private :=
  ∀ (x y : X) (s : set O), measurable_set s → neighboring x y → 
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ

def output_diff_private (s : set O) :=
  ∀ (x y : X) (t : set O) (hs : t ⊆ s), measurable_set t → neighboring x y → 
  P {ω : Ω | M x ω ∈ t} ≤ exp ε * P {ω : Ω | M y ω ∈ t}

structure odp_partition :=
(ε δ : ℝ≥0∞)
(ε_lt_infty : ε < ∞)
(index : Type) 
[finite : fintype index] -- We assume finiteness of the ODP partition for now
(partition : O → option index)
(measurable_partition : ∀ i, measurable_set {o : O | partition o = i})
(ε_for : option index → ℝ≥0∞)
(ε_for_lt_infty : ∀ i, ε_for i < ∞)
(dp : diff_private P M ε δ)
(odp : ∀ i, output_diff_private P M (ε_for i) {o : O | partition o = i})

-- TODO: Example instance

open_locale classical
noncomputable theory

variables {P} {M}

-- def odp_index (p : odp_partition P M) (o : O) : option p.index := 
--   if h : ∃ i : p.index, o ∈ p.partition i then some (classical.some h) else none

def εusage_for (p : odp_partition P M) : option p.index → ℝ≥0∞
| none := p.ε
| (some i) :=  p.ε_for i

lemma εusage_for_lt_infty (p : odp_partition P M) (i : option p.index) : 
  εusage_for p i < ∞ := 
begin
  cases i,
  apply p.ε_lt_infty,
  apply p.ε_for_lt_infty,
end

def εusage (p : odp_partition P M) (o : O) := εusage_for p (p.partition o)

def odp_set_for (p : odp_partition P M) : option p.index → set O :=
λ i, {o : O | p.partition o = i}

lemma partition_eq_of_mem_odp_set_for {p : odp_partition P M} {i : option p.index} {o : O} (ho: o ∈ odp_set_for p i) : 
  p.partition o = i := ho

lemma pairwise_disjoint_on_odp_set_for {p : odp_partition P M} : pairwise (disjoint on odp_set_for p) :=
begin
  rintros i j hij a ⟨ha₁, ha₂⟩,
  change p.partition a = i at ha₁,
  change p.partition a = j at ha₂,
  rw [←ha₁, ←ha₂] at hij,
  contradiction,
end

-- lemma odp_index_of_mem_partition {o : O} {p : odp_partition P M} {i : p.index}
--   (hi : o ∈ p.partition i) : odp_index p o = some i :=
-- begin
--   have hex : ∃ j, o ∈ p.partition j := ⟨i, hi⟩,
--   simp only [odp_index, hex, dif_pos],
--   exact odp_index_unique (classical.some_spec hex) hi
-- end

lemma εusage_eq_εusage_for {o : O} {p : odp_partition P M} {i : option p.index} (ho : o ∈ odp_set_for p i) :
  εusage p o = εusage_for p i :=
begin
  rw ← partition_eq_of_mem_odp_set_for ho,
  refl,
end

lemma mem_odp_set_for_odp_index (p : odp_partition P M) (o : O) : o ∈ odp_set_for p (p.partition o) :=
by simp [odp_set_for]

@[measurability]
lemma measurable_set_odp_set_for (p : odp_partition P M) (i : option p.index) : 
  measurable_set (odp_set_for p i) :=
p.measurable_partition i

instance (p : odp_partition P M) : measurable_space p.index := ⊤
instance (p : odp_partition P M) : measurable_space (option p.index) := ⊤

@[measurability]
lemma measurable_partition (p : odp_partition P M) : 
  measurable (p.partition) :=
begin
  haveI : fintype p.index := p.finite,
  intros s hs,
  rw ←set.bUnion_preimage_singleton,
  change measurable_set (⋃ i ∈ s, odp_set_for p i),
  apply set.finite.measurable_set_bUnion,
  apply set.finite.of_fintype,
  intros,
  apply measurable_set_odp_set_for,
end

lemma union_odp_set_for_eq_univ (p : odp_partition P M) : (⋃ i, odp_set_for p i) = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intros o,
  apply set.mem_Union.2,
  use p.partition o,
  apply mem_odp_set_for_odp_index
end

lemma split_set (p : odp_partition P M) (s : set (O × O')) : s = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod set.univ :=
calc s = s ∩ (set.prod set.univ set.univ) : by simp
... = s ∩ ((set.Union (λ i, odp_set_for p i)).prod set.univ) : by rw ←union_odp_set_for_eq_univ _
... = s ∩ (⋃ (i : option p.index), (odp_set_for p i).prod set.univ) : by rw set.Union_prod_const
... = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod set.univ : by rw set.inter_Union
