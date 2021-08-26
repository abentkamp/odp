import measure_theory.constructions.prod
import .missing_ennreal

noncomputable theory
open measure_theory ennreal 
open_locale ennreal
open_locale classical

/-- For our purposes, the type of databases is arbitrary, but it must have some
notion of neighboring databases. -/
class database_type (X : Type*) :=
(neighboring : X → X → Prop)
open database_type

/- `Ω` is a sample space with a probability measure `P` on it. -/
variables {Ω : Type} [measurable_space Ω] (P : measure Ω)

/- `O` is the type of outputs of mechanisms. -/
variables {O : Type} {O' : Type} [measurable_space O] [measurable_space O']

/- `X` is the type of databases. -/
variables {X : Type} [database_type X] 

/- `M` is a mechanism, i.e., a randomized function from databases to outputs. -/
variables (M : X → Ω → O) 

/- When considering compositions of mechanisms, the adversary can choose pairs
of databases at each iteration. The output of the mechanism then depends no longer
on a single database. For compositions we therefore use two random variables 
`M₀` and `M₁`. -/
variables (M₀ : Ω → O) (M₁ : Ω → O)

/- `ε` and `δ` are parameters of the notion of differential privacy. -/
variables (ε δ : ℝ≥0∞)

/-- Differential privacy for a single mechanism -/
def diff_private :=
  ∀ (x y : X) (s : set O), measurable_set s → neighboring x y → 
  P {ω : Ω | M x ω ∈ s} ≤ exp ε * P {ω : Ω | M y ω ∈ s} + δ

/-- Differential privacy for compositions M₀, M₁ of mechanisms -/
def diff_private_composition :=
  ∀ (s : set O) (hs : measurable_set s),
  P {ω : Ω | M₀ ω ∈ s} ≤ exp ε * P {ω : Ω | M₁ ω ∈ s} + δ

/-- Output differential privacy on a given set `s` of outputs -/
def output_diff_private (s : set O) :=
  ∀ (x y : X) (t : set O) (hs : t ⊆ s), measurable_set t → neighboring x y → 
  P {ω : Ω | M x ω ∈ t} ≤ exp ε * P {ω : Ω | M y ω ∈ t}

/-- Given an (ε, δ)-differentially private mechanism M (where δ may be zero),
an ODP parti- tion P = {Pδ } ∪ {Pε }k for M is a partition of Range(M) into k
setsPδ,Pε,Pε,...,andassociatedvaluesε(Pε),ε(Pε),···≥0 1212 (Pδ has no associated
ε-value) such that for each k, (M,Pε) k fulfills ε (Pε )-ODP. -/
structure odp_mechanism :=
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

variables {P} {M}

def εusage_for (p : odp_mechanism P M) : option p.index → ℝ≥0∞
| none := p.ε
| (some i) :=  p.ε_for i

lemma εusage_for_lt_infty (p : odp_mechanism P M) (i : option p.index) : 
  εusage_for p i < ∞ := 
begin
  cases i,
  apply p.ε_lt_infty,
  apply p.ε_for_lt_infty,
end

def εusage (p : odp_mechanism P M) (o : O) := εusage_for p (p.partition o)

def odp_set_for (p : odp_mechanism P M) : option p.index → set O :=
λ i, {o : O | p.partition o = i}

lemma partition_eq_of_mem_odp_set_for {p : odp_mechanism P M} {i : option p.index} {o : O} (ho: o ∈ odp_set_for p i) : 
  p.partition o = i := ho

lemma pairwise_disjoint_on_odp_set_for {p : odp_mechanism P M} : pairwise (disjoint on odp_set_for p) :=
begin
  rintros i j hij a ⟨ha₁, ha₂⟩,
  change p.partition a = i at ha₁,
  change p.partition a = j at ha₂,
  rw [←ha₁, ←ha₂] at hij,
  contradiction,
end

-- lemma odp_index_of_mem_partition {o : O} {p : odp_mechanism P M} {i : p.index}
--   (hi : o ∈ p.partition i) : odp_index p o = some i :=
-- begin
--   have hex : ∃ j, o ∈ p.partition j := ⟨i, hi⟩,
--   simp only [odp_index, hex, dif_pos],
--   exact odp_index_unique (classical.some_spec hex) hi
-- end

lemma εusage_eq_εusage_for {o : O} {p : odp_mechanism P M} {i : option p.index} (ho : o ∈ odp_set_for p i) :
  εusage p o = εusage_for p i :=
begin
  rw ← partition_eq_of_mem_odp_set_for ho,
  refl,
end

lemma mem_odp_set_for_odp_index (p : odp_mechanism P M) (o : O) : o ∈ odp_set_for p (p.partition o) :=
by simp [odp_set_for]

@[measurability]
lemma measurable_set_odp_set_for (p : odp_mechanism P M) (i : option p.index) : 
  measurable_set (odp_set_for p i) :=
p.measurable_partition i

instance (p : odp_mechanism P M) : measurable_space p.index := ⊤
instance (p : odp_mechanism P M) : measurable_space (option p.index) := ⊤

@[measurability]
lemma measurable_partition (p : odp_mechanism P M) : 
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

lemma union_odp_set_for_eq_univ (p : odp_mechanism P M) : (⋃ i, odp_set_for p i) = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intros o,
  apply set.mem_Union.2,
  use p.partition o,
  apply mem_odp_set_for_odp_index
end

lemma split_set (p : odp_mechanism P M) (s : set (O × O')) : s = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod set.univ :=
calc s = s ∩ (set.prod set.univ set.univ) : by simp
... = s ∩ ((set.Union (λ i, odp_set_for p i)).prod set.univ) : by rw ←union_odp_set_for_eq_univ _
... = s ∩ (⋃ (i : option p.index), (odp_set_for p i).prod set.univ) : by rw set.Union_prod_const
... = ⋃ (i : option p.index), s ∩ (odp_set_for p i).prod set.univ : by rw set.inter_Union
