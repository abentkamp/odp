import data.real.ennreal
import data.complex.exponential


open_locale ennreal

namespace ennreal

noncomputable def exp (x : ℝ≥0∞) : ℝ≥0∞ :=
if x = ∞ then ∞ else (real.exp x.to_real).to_nnreal

end ennreal