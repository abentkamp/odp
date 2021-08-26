import .main
import measure_theory.measure.lebesgue


noncomputable theory
open measure_theory ennreal
open_locale ennreal

def databases := ℤ

def laplace_pdf (b : ℝ) (x : ℝ): ℝ≥0∞ := 
ennreal.of_real (1 / (2 * b) * real.exp (- (abs x) / b))

def laplace (b : ℝ) : measure ℝ :=
  measure_space.volume.with_density (laplace_pdf b)

def ε : ℝ := 1

def mechanism (x : ℤ) :=  measure.map (λ y, abs (x : ℝ) + y) (laplace (1 / ε)) 


#check mechanism