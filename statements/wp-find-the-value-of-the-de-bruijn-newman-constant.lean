import Mathlib

/-!
# Find the value of the de Bruijn–Newman constant

Source: https://en.wikipedia.org/wiki/De_Bruijn–Newman_constant
Credit: @PastaPastaPasta

We use the normalization of Rodgers and Tao, arXiv:1801.05914, equations (1)–(4).
The constant is the unique threshold for reality of all zeros of the deformed
cosine transform. We state directly that this threshold is zero.
-/

namespace OMA.S_wp_find_the_value_of_the_de_bruijn_newman_constant

noncomputable def phi (u : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) -
      3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))

noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (t * u ^ 2) * phi u : ℝ) : ℂ) *
    Complex.cos (z * (u : ℂ))

theorem main : ∀ t : ℝ, (∀ z : ℂ, H t z = 0 → z.im = 0) ↔ 0 ≤ t := by
  sorry

end OMA.S_wp_find_the_value_of_the_de_bruijn_newman_constant
