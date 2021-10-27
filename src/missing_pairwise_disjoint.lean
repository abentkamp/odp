import data.set.pairwise

namespace set

--TODO: move
lemma pairwise_disjoint_on_preimage {ι α β : Type*} (f : α → β) (s : ι → set β) (h : pairwise (disjoint on s)) : 
  pairwise (disjoint on (λ i, f ⁻¹' (s i))) :=
begin
  intros i j hij a ha,
  apply h i j hij (set.mem_inter _ _),
  exact f a,
  apply ((set.mem_inter_iff _ _ _).1 ha).1,
  apply ((set.mem_inter_iff _ _ _).1 ha).2,
end

--TODO: move
lemma pairwise_disjoint_on_inter {ι β : Type*} (s : ι → set β) (t : set β) (h : pairwise (disjoint on s)) : 
  pairwise (disjoint on λ i, t ∩ s i) :=
begin
  intros i j hij a ha,
  apply h i j hij (set.mem_inter _ _),
  exact mem_of_mem_inter_right ha.1,
  exact mem_of_mem_inter_right ha.2,
end

--TODO: move
lemma pairwise_disjoint_on_prod {ι α β : Type*} (s : ι → set α) (t : set β) (h : pairwise (disjoint on s)) : 
  pairwise (disjoint on λ i, (s i).prod t) :=
begin
  intros i j hij a ha,
  apply h i j hij (set.mem_inter _ _),
  exact a.1,
  apply (set.mem_prod.2 ha.1).1,
  apply (set.mem_prod.2 ha.2).1,
end

end set