import Mathlib
import OAI.MeasureTheory.DyadicAvoidance.Main

/-!
# Compact avoidance sets for finite dyadic models

The imported periodic hitting theorem is from OpenAI's formalization of the
geometric case of the Erdős similarity conjecture. We transfer it to sets which
model arbitrarily long dyadic prefixes to arbitrary accuracy at small scales.
-/

namespace DyadicBlocks
open Set MeasureTheory Topology
open scoped ENNReal

/-- An open periodic hit on a compact parameter rectangle survives uniform perturbations
of a sufficiently long finite prefix. -/
theorem robust_periodic_hit {H : Set ℝ} (hH : IsOpen H)
    (hper : ∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H)
    (g : ℕ → ℝ)
    (hhit : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (1 : ℝ) 2,
      ∃ n : ℕ, x + t * g n ∈ H) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ (x t : ℝ), t ∈ Set.Icc (1 : ℝ) 2 →
      ∀ v : ℕ → ℝ, (∀ i ≤ N, |v i - g i| < δ) → ∃ i ≤ N, x + t * v i ∈ H := by
  let K := Icc (0 : ℝ) 1 ×ˢ Icc (1 : ℝ) 2
  let P (S : Set (ℝ × ℝ)) := ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ p ∈ S, ∀ v : ℕ → ℝ, (∀ i ≤ N, |v i - g i| < δ) →
      ∃ i ≤ N, p.1 + p.2 * v i ∈ H
  have hcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK : P K := by
    apply hcompact.induction_on (p := P)
    · exact ⟨0, 1, zero_lt_one, fun _ h ↦ h.elim⟩
    · rintro S T hST ⟨N, δ, hδ, hT⟩
      exact ⟨N, δ, hδ, fun p hp ↦ hT p (hST hp)⟩
    · rintro S T ⟨N, δ, hδ, hS⟩ ⟨M, ε, hε, hT⟩
      refine ⟨max N M, min δ ε, lt_min hδ hε, ?_⟩
      rintro p (hp | hp) v hv
      · obtain ⟨i, hi, hh⟩ := hS p hp v (fun i hi ↦
          (hv i (hi.trans (le_max_left _ _))).trans_le (min_le_left _ _))
        exact ⟨i, hi.trans (le_max_left _ _), hh⟩
      · obtain ⟨i, hi, hh⟩ := hT p hp v (fun i hi ↦
          (hv i (hi.trans (le_max_right _ _))).trans_le (min_le_right _ _))
        exact ⟨i, hi.trans (le_max_right _ _), hh⟩
    · intro p hp
      obtain ⟨n, hn⟩ := hhit p.1 hp.1 p.2 hp.2
      let f (q : (ℝ × ℝ) × ℝ) := q.1.1 + q.1.2 * q.2
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hmem : f ⁻¹' H ∈ 𝓝 (p, g n) := (hH.preimage hf).mem_nhds hn
      obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hmem
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, n, δ, hδ, ?_⟩
      intro q hq v hv
      have hvn : v n ∈ Metric.ball (g n) δ := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hv n le_rfl
      exact ⟨n, le_rfl, hUV (show (q, v n) ∈ U ×ˢ V from ⟨hq, hball hvn⟩)⟩
  obtain ⟨N, δ, hδ, h⟩ := hK
  refine ⟨N, δ, hδ, ?_⟩
  intro x t ht v hv
  have hp : (Int.fract x, t) ∈ K :=
    ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ht⟩
  obtain ⟨i, hi, hh⟩ := h _ hp v hv
  refine ⟨i, hi, ?_⟩
  have hshift := (hper (Int.fract x + t * v i) ⌊x⌋).mpr hh
  rwa [add_right_comm, Int.fract_add_floor] at hshift

theorem periodic_scaled_bound (H : Set ℝ) (_hH : IsOpen H)
    (hper : ∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    volume (Icc (0 : ℝ) 1 ∩ ((fun y : ℝ => y / d) ⁻¹' H)) ≤
      2 * volume (Icc (0 : ℝ) 1 ∩ H) := by
  let A := Icc (0 : ℝ) 1 ∩ H
  let N := ⌊1 / d⌋₊ + 1
  let C (j : ℕ) := (fun x : ℝ => x + -(j : ℝ)) ⁻¹' A
  have hcov : Icc (0 : ℝ) (1 / d) ∩ H ⊆ ⋃ j ∈ Finset.range N, C j := by
    intro x hx
    obtain ⟨⟨hx0, hx1⟩, hxH⟩ := hx
    have hj : ⌊x⌋₊ ∈ Finset.range N := Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.floor_mono hx1))
    refine mem_iUnion₂.mpr ⟨⌊x⌋₊, hj, ?_⟩
    change x + -(⌊x⌋₊ : ℝ) ∈ Icc 0 1 ∩ H
    refine ⟨⟨by linarith [Nat.floor_le hx0], by linarith [Nat.lt_floor_add_one x]⟩, ?_⟩
    simpa using (hper x (-(⌊x⌋₊ : ℤ))).2 hxH
  have hC (j : ℕ) : volume (C j) = volume A :=
    measure_preimage_add_right volume _ A
  have hvol : volume (Icc (0 : ℝ) (1 / d) ∩ H) ≤ (N : ℝ≥0∞) * volume A := calc
    _ ≤ volume (⋃ j ∈ Finset.range N, C j) := measure_mono hcov
    _ ≤ ∑ j ∈ Finset.range N, volume (C j) := measure_biUnion_finset_le _ _
    _ = _ := by simp [hC, nsmul_eq_mul]
  have hscale : Icc (0 : ℝ) 1 ∩ ((fun y : ℝ => y / d) ⁻¹' H) =
      (· * d⁻¹) ⁻¹' (Icc (0 : ℝ) (1 / d) ∩ H) := by
    ext y
    change ((0 ≤ y ∧ y ≤ 1) ∧ y / d ∈ H) ↔
      ((0 ≤ y * d⁻¹ ∧ y * d⁻¹ ≤ 1 / d) ∧ y * d⁻¹ ∈ H)
    rw [← div_eq_mul_inv, div_le_div_iff_of_pos_right hd, le_div_iff₀ hd, zero_mul]
  have hN : d * (N : ℝ) ≤ 2 := by
    have hfloor := Nat.floor_le (show (0 : ℝ) ≤ 1 / d by positivity)
    have hmul := mul_le_mul_of_nonneg_left hfloor hd.le
    have hcancel : d * (1 / d) = 1 := by field_simp
    calc
      d * (N : ℝ) = d * (⌊1 / d⌋₊ : ℝ) + d := by simp [N, mul_add]
      _ ≤ d * (1 / d) + 1 := add_le_add hmul hd1
      _ = 2 := by rw [hcancel]; norm_num
  have hbound : ENNReal.ofReal d * (N : ℝ≥0∞) ≤ 2 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hd.le]
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hN
  rw [hscale, Real.volume_preimage_mul_right (inv_ne_zero hd.ne'), inv_inv, abs_of_pos hd]
  exact (mul_le_mul_of_nonneg_left hvol zero_le).trans <| by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbound zero_le

theorem periodic_neg_scaled_bound (H : Set ℝ) (hH : IsOpen H)
    (hper : ∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H)
    (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
    volume (Icc (0 : ℝ) 1 ∩ ((fun y : ℝ => -y / d) ⁻¹' H)) ≤
      2 * volume (Icc (0 : ℝ) 1 ∩ H) := by
  let K := (fun x : ℝ => -x) ⁻¹' H
  have hopen : IsOpen K := hH.preimage continuous_neg
  have hK (x : ℝ) (j : ℤ) : x + (j : ℝ) ∈ K ↔ x ∈ K := by
    simpa [K, neg_add, add_comm] using hper (-x) (-j)
  have heq : Icc (0 : ℝ) 1 ∩ K = (fun x : ℝ => 1 - x) ⁻¹' (Icc (0 : ℝ) 1 ∩ H) := by
    ext x
    have hp : 1 - x ∈ H ↔ -x ∈ H := by simpa [sub_eq_add_neg, add_comm] using hper (-x) 1
    change (x ∈ Icc 0 1 ∧ -x ∈ H) ↔ (1 - x ∈ Icc 0 1 ∧ 1 - x ∈ H)
    rw [hp]
    exact and_congr_left fun _ => by simp [mem_Icc]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hvol : volume (Icc (0 : ℝ) 1 ∩ K) = volume (Icc (0 : ℝ) 1 ∩ H) := by
    rw [heq]
    have hr (x : ℝ) : 1 - x = (x * (-1)) + 1 := by ring
    simp_rw [hr]
    change volume ((· * (-1 : ℝ)) ⁻¹' ((· + (1 : ℝ)) ⁻¹' _)) = _
    rw [Real.volume_preimage_mul_right (by norm_num : (-1 : ℝ) ≠ 0), measure_preimage_add_right]
    norm_num
    rfl
  have hb := periodic_scaled_bound K hopen hK d hd hd1
  rw [hvol] at hb
  simpa only [K, preimage_preimage, Function.comp_def, neg_div] using hb

/-- For all affine copies at one absolute dilation band, two scaled holes suffice. -/
theorem finite_pattern_band {A : Set ℝ} (g : ℕ → ℝ) {H : Set ℝ}
    (ho : IsOpen H) (hp : ∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H)
    (hit : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 : ℝ) 2, ∃ i, x + t * g i ∈ H)
    (model : ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
      ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N, ∃ z ∈ A, |(z - c) / r - g i| < δ)
    {s : ℝ} (hs : 0 < s) :
    ∃ O : Set ℝ, IsOpen O ∧ volume (Icc (0 : ℝ) 1 ∩ O) ≤ 4 * volume (Icc (0 : ℝ) 1 ∩ H) ∧
      ∀ a b : ℝ, |a| ∈ Icc s (s * 2) →
        ∃ z ∈ A, a * z + b ∈ O := by
  classical
  obtain ⟨N, δ, hδ, robust⟩ := robust_periodic_hit ho hp g hit
  obtain ⟨c, r, hr, hr', hz⟩ := model N δ (1 / s) hδ (by positivity)
  let z : ℕ → ℝ := fun i => if h : i ≤ N then (hz i h).choose else c
  have zspec (i : ℕ) (hi : i ≤ N) : z i ∈ A ∧ |(z i - c) / r - g i| < δ := by
    simpa [z, hi] using (hz i hi).choose_spec
  let d := s * r
  have hd : 0 < d := mul_pos hs hr
  have hd1 : d ≤ 1 := by
    simpa only [d, mul_comm s r] using (le_div_iff₀ hs).mp hr'
  let I := Icc (0 : ℝ) 1
  let P := (fun y : ℝ => y / d) ⁻¹' H
  let M := (fun y : ℝ => -y / d) ⁻¹' H
  have hP : IsOpen P := ho.preimage (by fun_prop)
  have hM : IsOpen M := ho.preimage (by fun_prop)
  refine ⟨P ∪ M, hP.union hM, ?_, ?_⟩
  · calc
      volume (I ∩ (P ∪ M)) = volume ((I ∩ P) ∪ (I ∩ M)) := by rw [inter_union_distrib_left]
      _ ≤ volume (I ∩ P) + volume (I ∩ M) := measure_union_le _ _
      _ ≤ 2 * volume (I ∩ H) + 2 * volume (I ∩ H) :=
        add_le_add (periodic_scaled_bound H ho hp d hd hd1) (periodic_neg_scaled_bound H ho hp d hd hd1)
      _ = 4 * volume (I ∩ H) := by rw [← add_mul]; norm_num
  · intro a b ha
    have ht : |a| / s ∈ Icc (1 : ℝ) 2 :=
      ⟨(one_le_div hs).mpr ha.1, (div_le_iff₀ hs).mpr (by linarith [ha.2])⟩
    let v := fun i => (z i - c) / r
    have hv : ∀ i ≤ N, |v i - g i| < δ := fun i hi => (zspec i hi).2
    by_cases h : 0 ≤ a
    · obtain ⟨i, hi, hhit⟩ := robust ((a * c + b) / d) _ ht v hv
      rw [abs_of_nonneg h] at hhit
      refine ⟨z i, (zspec i hi).1, Or.inl ?_⟩
      change (a * z i + b) / d ∈ H
      convert hhit using 1
      dsimp [d, v]
      field_simp
      ring
    · obtain ⟨i, hi, hhit⟩ := robust (-(a * c + b) / d) _ ht v hv
      rw [abs_of_neg (lt_of_not_ge h)] at hhit
      refine ⟨z i, (zspec i hi).1, Or.inr ?_⟩
      change -(a * z i + b) / d ∈ H
      convert hhit using 1
      dsimp [d, v]
      field_simp
      ring

/-- Transfer a periodic hitting theorem for any template g to its approximate finite
models. The exceptional open set has arbitrarily small measure inside the unit interval. -/
theorem small_holes_for_models {A : Set ℝ} (g : ℕ → ℝ)
    (holes : ∀ ε : ℝ≥0∞, 0 < ε → ∃ H : Set ℝ, IsOpen H ∧
      (∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H) ∧ volume (Icc 0 1 ∩ H) ≤ ε ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 : ℝ) 2, ∃ i : ℕ, x + t * g i ∈ H)
    (model : ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
      ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N, ∃ z ∈ A, |(z - c) / r - g i| < δ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ U : Set ℝ, IsOpen U ∧ volume (Icc (0 : ℝ) 1 ∩ U) < η ∧
      ∀ a b : ℝ, a ≠ 0 → ∃ z ∈ A, a * z + b ∈ U := by
  classical
  obtain ⟨ε, hε, hsum⟩ := ENNReal.exists_pos_tsum_mul_lt_of_countable hη.ne'
    (fun _ : ℤ => (4 : ℝ≥0∞)) (by norm_num)
  have band (k : ℤ) : ∃ O : Set ℝ, IsOpen O ∧ volume (Icc (0 : ℝ) 1 ∩ O) ≤ 4 * ε k ∧
      ∀ a b : ℝ, |a| ∈ Icc ((2 : ℝ)^k) (2^k * 2) → ∃ z ∈ A, a * z + b ∈ O := by
    obtain ⟨H, ho, hp, hvol, hit⟩ := holes (ε k) (ENNReal.coe_pos.mpr (hε k))
    obtain ⟨O, hO, hle, hc⟩ := finite_pattern_band g ho hp hit model
      (show 0 < (2 : ℝ) ^ k by positivity)
    exact ⟨O, hO, hle.trans (mul_le_mul_of_nonneg_left hvol (by positivity)), hc⟩
  choose O hopen hvol hhit using band
  refine ⟨⋃ k, O k, isOpen_iUnion hopen, ?_, ?_⟩
  · rw [inter_iUnion]
    exact ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hvol)).trans_lt hsum
  · intro a b ha
    obtain ⟨k, hlo, hhi⟩ := exists_mem_Ico_zpow (abs_pos.mpr ha) (by norm_num : (1 : ℝ) < 2)
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hhi
    obtain ⟨z, hz, hzO⟩ := hhit k a b ⟨hlo, hhi.le⟩
    exact ⟨z, hz, mem_iUnion.mpr ⟨k, hzO⟩⟩

open OAI.Problem310 OAI.Problem310Support

private theorem dyadic_holes (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H) ∧ volume (Icc 0 1 ∩ H) ≤ ε ∧
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 : ℝ) 2, ∃ i : ℕ, x + t * dyadicPoint i ∈ H := by
  obtain ⟨e, he, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have he' : 0 < (e : ℝ) := by exact_mod_cast (ENNReal.coe_pos.mp he)
  let p := min (e : ℝ) 1 / 12
  have hp : 0 < p := div_pos (lt_min he' zero_lt_one) (by norm_num)
  have hp1 : p < 1 := by dsimp [p]; linarith [min_le_right (e : ℝ) 1]
  obtain ⟨H, ho, hper, hvol, hhit⟩ := periodic_hitting_set p hp hp1
  refine ⟨H, ho, ?_, ?_, ?_⟩
  · intro x j
    cases j with
    | ofNat n => simpa using periodic_mem_nat hper n x
    | negSucc n =>
      have h := periodic_mem_nat hper (n + 1) (x - ((n + 1 : ℕ) : ℝ))
      rw [sub_add_cancel] at h
      simpa [sub_eq_add_neg] using h.symm
  · have hp6 : 6 * p ≤ (e : ℝ) := by dsimp [p]; linarith [min_le_left (e : ℝ) 1]
    have hδ := hvol.trans (ENNReal.ofReal_le_ofReal hp6)
    rw [ENNReal.ofReal_coe_nnreal] at hδ
    have hle := hδ.trans heε.le
    simpa [periodDensity, inter_comm] using hle
  · intro x _ t ht
    obtain ⟨i, _, hi⟩ := hhit x t ht
    exact ⟨i, hi⟩

/-- Finite approximation by normalized dyadic prefixes at arbitrarily small scales. -/
def ModelsDyadicPrefixes (A : Set ℝ) : Prop :=
  ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
    ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N, ∃ z ∈ A, |(z - c) / r - dyadicPoint i| < δ

/-- A compact subset of the unit interval of measure arbitrarily close to one
can miss at least one point of every nondegenerate affine copy of the model. -/
theorem compact_avoidance_of_models {A : Set ℝ} (model : ModelsDyadicPrefixes A)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ IsCompact E ∧ ENNReal.ofReal (1 - η) < volume E ∧
      ∀ a b : ℝ, a ≠ 0 → ∃ z ∈ A, a * z + b ∉ E := by
  obtain ⟨U, hU, hsmall, hit⟩ := small_holes_for_models dyadicPoint dyadic_holes model
    (η := ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨hcomp, hvol⟩ := compact_complement_volume hU hη hη1 (by simpa [inter_comm] using hsmall.le)
  refine ⟨Icc 0 1 \ U, sdiff_subset, hcomp, hvol, ?_⟩
  intro a b ha
  obtain ⟨z, hz, hzU⟩ := hit a b ha
  exact ⟨z, hz, fun h => h.2 hzU⟩

/-- The union of the rows with dyadic exponents from 2^n through 2^n+n. -/
def sparseDyadicBlocks : Set ℝ :=
  {z | ∃ n i : ℕ, i ≤ n ∧ z = ((2 : ℝ)⁻¹) ^ (2 ^ n + i)}

theorem sparseDyadicBlocks_models : ModelsDyadicPrefixes sparseDyadicBlocks := by
  intro N δ D hδ hD
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hD (by norm_num : (2 : ℝ)⁻¹ < 1)
  let n := max N k
  have hk' : k ≤ 2 ^ n := (le_max_right N k).trans (n.lt_two_pow_self.le)
  let r := ((2 : ℝ)⁻¹) ^ (2 ^ n)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrD : r ≤ D := (pow_le_pow_of_le_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num) hk').trans hk.le
  refine ⟨0, r, hr, hrD, ?_⟩
  intro i hi
  refine ⟨r * dyadicPoint i, ⟨n, i, hi.trans (le_max_left _ _), ?_⟩, ?_⟩
  · simp only [r, dyadicPoint, pow_add]
  · simpa [hr.ne'] using hδ

theorem sparseDyadicBlocks_avoidance {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ IsCompact E ∧ ENNReal.ofReal (1 - η) < volume E ∧
      ∀ a b : ℝ, a ≠ 0 → ∃ z ∈ sparseDyadicBlocks, a * z + b ∉ E :=
  compact_avoidance_of_models sparseDyadicBlocks_models hη hη1

open Set Filter Topology

/-- The exponents in the dyadic blocks of lengths one, two, three, and so on. -/
def blockExponents : Set ℕ := {e | ∃ n i : ℕ, i ≤ n ∧ e = 2 ^ n + i}

/-- Every positive-step arithmetic progression hits a gap between two blocks. -/
theorem blockExponents_miss_progression (a d : ℕ) (hd : 0 < d) :
    ∃ k : ℕ, a + d * k ∉ blockExponents := by
  let n := (a + d + 2) + 2
  have hwide : n + d + a < 2 ^ n := by
    dsimp [n]
    rw [pow_add (2 : ℕ) (a + d + 2) 2]
    have : a + d + 2 < 2 ^ (a + d + 2) := Nat.lt_two_pow_self
    norm_num
    omega
  let t := 2 ^ n + n
  let k := t / d + 1
  have hgap : t < a + d * k ∧ a + d * k < 2 ^ (n + 1) := by
    have hrem := Nat.mod_lt t hd
    have heq := Nat.mod_add_div t d
    dsimp only [k]
    rw [Nat.mul_succ, pow_succ]
    dsimp only [t] at *
    omega
  refine ⟨k, ?_⟩
  rintro ⟨m, i, hi, he⟩
  by_cases hmn : m ≤ n
  · have hpow : 2 ^ m ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by decide) hmn
    dsimp only [t] at hgap
    omega
  · have hpow : 2 ^ (n + 1) ≤ (2 : ℕ) ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- Each block is a finite geometric progression of ratio one half. -/
def dyadicBlockSet : Set ℝ := (fun e : ℕ => (1 / 2 : ℝ) ^ e) '' blockExponents

/-- This union of arbitrarily long finite geometric blocks has no translated and
rescaled infinite geometric progression with ratio strictly between zero and one. -/
theorem dyadicBlockSet_no_affine_geometric (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (a b : ℝ) (ha : a ≠ 0) : ¬ ∀ n : ℕ, a * q ^ n + b ∈ dyadicBlockSet := by
  intro h
  choose e hblock he using h
  have hqanti := pow_right_strictAnti₀ hq.1 hq.2
  have hei : Function.Injective e := by
    intro m n heq
    apply hqanti.injective
    apply mul_left_cancel₀ ha
    apply add_right_cancel (b := b)
    rw [← he m, ← he n, heq]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
  have hzero : Tendsto (fun n : ℕ => a * q^n + b) atTop (𝓝 0) := by
    simpa only [← he, Function.comp_def] using hpow.comp hei.nat_tendsto_atTop
  have hqpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2
  have hlim : Tendsto (fun n : ℕ => a * q^n + b) atTop (𝓝 b) := by
    simpa using (hqpow.const_mul a).add_const b
  have hb : b = 0 := tendsto_nhds_unique hlim hzero
  subst b
  simp only [add_zero] at he
  have ha' : 0 < a := by
    simpa only [he 0, pow_zero, mul_one] using (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (e 0))
  have hpanti := pow_right_strictAnti₀ (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)
  have hlt : e 0 < e 1 := by
    apply hpanti.lt_iff_gt.mp
    rw [he 1, he 0, pow_one, pow_zero, mul_one]
    exact mul_lt_of_lt_one_right ha' hq.2
  have hstep (n : ℕ) : e (n + 1) + e 0 = e n + e 1 := by
    apply hpanti.injective
    change (1 / 2 : ℝ) ^ (e (n+1) + e 0) = (1 / 2 : ℝ) ^ (e n + e 1)
    rw [pow_add, pow_add, he (n+1), he 0, he n, he 1, pow_succ]
    ring
  let d := e 1 - e 0
  have harith (n : ℕ) : e n = e 0 + d * n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ]
      have hh := hstep n
      dsimp only [d] at *
      omega
  obtain ⟨n, hn⟩ := blockExponents_miss_progression (e 0) d (Nat.sub_pos_of_lt hlt)
  exact hn (harith n ▸ hblock n)

/-- All real ratios producing infinitely many different powers are excluded, including
expanding and alternating progressions. -/
theorem dyadicBlockSet_no_infinite_geometric (q : ℝ) (hq0 : q ≠ 0) (hq1 : |q| ≠ 1)
    (a b : ℝ) (ha : a ≠ 0) : ¬ ∀ n : ℕ, a * q ^ n + b ∈ dyadicBlockSet := by
  intro h
  rcases lt_or_gt_of_ne hq1 with hsmall | hlarge
  · have hsq : q ^ 2 < 1 := by
      rw [← sq_abs]
      exact pow_lt_one₀ (abs_nonneg q) hsmall (by decide)
    apply dyadicBlockSet_no_affine_geometric (q ^ 2) ⟨sq_pos_of_ne_zero hq0, hsq⟩ a b ha
    intro n
    simpa only [← pow_mul] using h (2 * n)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + |b|) / |a|) hlarge
    obtain ⟨e, _, he⟩ := h n
    have hlo : 0 ≤ a * q ^ n + b := he ▸ pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) _
    have hhi : a * q ^ n + b ≤ 1 := he ▸ pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    have hb : |a * q ^ n| ≤ 1 + |b| := by
      rw [abs_le]
      constructor <;> linarith [le_abs_self b, neg_abs_le b]
    rw [abs_mul, abs_pow] at hb
    have hh := (div_lt_iff₀ (abs_pos.mpr ha)).mp hn
    exact (not_lt_of_ge hb) (mul_comm |a| (|q| ^ n) ▸ hh)


theorem sparseDyadicBlocks_eq : sparseDyadicBlocks = dyadicBlockSet := by
  ext z
  constructor
  · rintro ⟨n, i, hi, rfl⟩
    exact ⟨2 ^ n + i, ⟨n, i, hi, rfl⟩, by simp⟩
  · rintro ⟨e, ⟨n, i, hi, rfl⟩, rfl⟩
    exact ⟨n, i, hi, by simp⟩

/-- The same set has no infinite affine geometric progression, yet arbitrarily
large compact subsets of the unit interval avoid every affine copy of it. -/
theorem sparseDyadicBlocks_no_progression_and_avoidance :
    (∀ q : ℝ, q ≠ 0 → |q| ≠ 1 → ∀ a b : ℝ, a ≠ 0 →
      ¬ ∀ n : ℕ, a * q ^ n + b ∈ sparseDyadicBlocks) ∧
    (∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ IsCompact E ∧
      ENNReal.ofReal (1 - η) < volume E ∧
      ∀ a b : ℝ, a ≠ 0 → ∃ z ∈ sparseDyadicBlocks, a * z + b ∉ E) := by
  refine ⟨?_, fun _ hη hη1 => sparseDyadicBlocks_avoidance hη hη1⟩
  simpa only [sparseDyadicBlocks_eq] using dyadicBlockSet_no_infinite_geometric

#print axioms OAI.Problem310.periodic_hitting_set
#print axioms compact_avoidance_of_models
#print axioms sparseDyadicBlocks_avoidance
#print axioms sparseDyadicBlocks_no_progression_and_avoidance

end DyadicBlocks
