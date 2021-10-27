import algebra.indicator_function

set_option old_structure_cmd true

@[protect_proj, ancestor add_cancel_monoid sub_neg_monoid]
class add_sub_cancel_monoid (M : Type*)
  extends add_cancel_monoid M, sub_neg_monoid M  :=
(add_sub_cancel :  ∀ (a b : M), a + b - b = a)

namespace add_sub_cancel_monoid

  variables {M : Type*} [add_sub_cancel_monoid M] (a b c : M)

  @[simp] lemma sub_self : a - a = 0 :=
  begin
    convert add_sub_cancel_monoid.add_sub_cancel 0 a,
    exact (zero_add a).symm
  end

  @[simp] lemma sub_zero : a - 0 = a :=
  begin
    convert add_sub_cancel_monoid.add_sub_cancel a 0,
    exact (add_zero a).symm
  end

end add_sub_cancel_monoid

@[protect_proj, ancestor add_sub_cancel_monoid add_comm_monoid]
class add_comm_sub_cancel_monoid (M : Type*) extends add_sub_cancel_monoid M, add_comm_monoid M


namespace set

lemma indicator_compl_add_sub_cancel_monoid {α M : Type*} [add_sub_cancel_monoid M] (s : set α) (f : α → M) :
  indicator sᶜ f = f - indicator s f :=
begin
  ext x,
  by_cases h : x ∈ s; simp [indicator, h],
end

end set