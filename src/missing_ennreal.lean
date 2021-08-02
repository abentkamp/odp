import data.real.ennreal
import data.complex.exponential


open_locale ennreal

namespace ennreal

noncomputable def exp (x : ℝ≥0∞) : ℝ≥0∞ :=
if x = ∞ then ∞ else (real.exp x.to_real).to_nnreal

lemma exp_ne_zero (x : ℝ≥0∞) : x.exp ≠ 0 :=
begin
  by_cases hx : x = ∞;
  simp [exp, hx, real.exp_pos]
end


lemma one_le_exp (x : ℝ≥0∞) : 1 ≤ x.exp :=
begin
  by_cases hx : x = ∞,
  { simp [exp, hx, real.exp_pos, real.one_le_exp] },
  { simp only [exp, hx, one_le_coe_iff, if_false],
    rw [←one_le_coe_iff],
    norm_cast,
    refine le_max_of_le_left (real.one_le_exp _),
    apply ennreal.to_real_nonneg }
end

@[simp] lemma exp_top : (∞ : ℝ≥0∞).exp = ∞ := rfl

lemma exp_add (x y : ℝ≥0∞) : exp (x + y) = exp x * exp y :=
begin
  by_cases hx : x = ∞;
  by_cases hy : y = ∞,
  { simp [exp, hx, hy] },
  { rw [exp, if_pos, hx, exp_top, top_mul, if_neg (exp_ne_zero _)],
    rw [hx, top_add] },
  { rw [exp, if_pos, hy, exp_top, mul_top, if_neg (exp_ne_zero _)],
    rw [hy, add_top] },
  { rw [exp, if_neg, exp, if_neg hx, exp, if_neg hy],
    rw [to_real_add hx hy, real.exp_add, real.to_nnreal_mul, ennreal.coe_mul],
    apply le_of_lt (real.exp_pos _),
    simp [hx, hy] }
end

end ennreal