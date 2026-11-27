import FormalConjectures.ErdosProblems.«120»

/-!
# Transferring periodic hitting sets to finite affine models

OpenAI's *The geometric case of the Erdős similarity conjecture* (Proposition 2.1)
constructs periodic hitting sets for geometric progressions. Jiang and Xi extend this to
profiles with two-sided adjacent-ratio bounds (arXiv:2610.11449, Proposition 2.2). Compactness
gives a finite prefix and a perturbation tolerance uniform in center and dilation.
Each dyadic band can then use a different finite pattern inside the candidate set.
It suffices to treat strictly decreasing positive null sequences without such a profile.
The finite rows may even have different ratio sequences in a fixed compact subinterval of (0,1).
-/

namespace OMA.R_Erdos120_erdos_120_R1

open Set MeasureTheory Filter Topology
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

/-- Jiang and Xi, Proposition 2.2, with an arbitrarily small density budget.
The initial value one fixes the scale of the template. -/
def H1 : Prop := ∀ (g : ℕ → ℝ) (α β : ℝ), 0 < α → β < 1 → g 0 = 1 →
  (∀ i, 0 < g i) → (∀ i, α * g i ≤ g (i+1) ∧ g (i+1) ≤ β * g i) →
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ H : Set ℝ, IsOpen H ∧ (∀ (x : ℝ) (j : ℤ), x + (j : ℝ) ∈ H ↔ x ∈ H) ∧
    volume (Icc 0 1 ∩ H) ≤ ε ∧
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (1 : ℝ) 2, ∃ i, x + t * g i ∈ H

/-- It remains to avoid strictly decreasing positive null sequences that fail to model
every profile with fixed adjacent-ratio bounds, at arbitrarily small positive scales. -/
def H2 : Prop := ∀ f : ℕ → ℝ, StrictAnti f → (∀ n, 0 < f n) → Tendsto f atTop (𝓝 0) →
  (¬ ∃ (g : ℕ → ℝ) (α β : ℝ), 0 < α ∧ β < 1 ∧ g 0 = 1 ∧
    (∀ i, 0 < g i) ∧ (∀ i, α * g i ≤ g (i+1) ∧ g (i+1) ≤ β * g i) ∧
    ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
      ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N,
        ∃ z ∈ range f, |(z - c) / r - g i| < δ) → Erdos120.Erdos120For (range f)

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

theorem bounded_ratio_models_avoid (h : H1) {A : Set ℝ} (g : ℕ → ℝ) (α β : ℝ)
    (hα : 0 < α) (hβ : β < 1) (h0 : g 0 = 1) (hp : ∀ i, 0 < g i)
    (hr : ∀ i, α * g i ≤ g (i+1) ∧ g (i+1) ≤ β * g i)
    (model : ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
      ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N, ∃ z ∈ A, |(z - c) / r - g i| < δ) :
    Erdos120.Erdos120For A := by
  obtain ⟨U, ho, hvol, hit⟩ := small_holes_for_models g (h g α β hα hβ h0 hp hr) model
    (η := 1) zero_lt_one
  let I := Icc (0 : ℝ) 1
  refine ⟨I \ U, measurableSet_Icc.diff ho.measurableSet, ?_, ?_⟩
  · have hdiff : I \ U = I \ (I ∩ U) := by ext; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [hdiff]
    refine lt_of_lt_of_le (tsub_pos_of_lt ?_) le_measure_sdiff
    simpa [I] using hvol
  · intro a b ha hsub
    obtain ⟨z, hz, hu⟩ := hit a b ha
    exact (hsub (mem_image_of_mem _ hz)).2 hu

/-- Consecutive ratios may change from row to row and from point to point. Compactness of
the ratio interval supplies one limiting template for all finite accuracies. -/
theorem variable_rows_avoid (h : H1) {A : Set ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 1)
    (t : ℕ → ℕ → Icc α β) (c r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0))
    (rows : ∀ n i : ℕ, i ≤ n →
      c n + r n * (∏ j ∈ Finset.range i, (t n j : ℝ)) ∈ A) : Erdos120.Erdos120For A := by
  obtain ⟨u, φ, hφ, hu⟩ := CompactSpace.tendsto_subseq t
  let g (i : ℕ) := ∏ j ∈ Finset.range i, (u j : ℝ)
  have hpos (i : ℕ) : 0 < g i := Finset.prod_pos (fun j _ => hα.trans_le (u j).2.1)
  have hratio (i : ℕ) : α * g i ≤ g (i+1) ∧ g (i+1) ≤ β * g i := by
    have hstep : g (i+1) = (u i : ℝ) * g i := by simp [g, Finset.prod_range_succ, mul_comm]
    rw [hstep]
    exact ⟨mul_le_mul_of_nonneg_right (u i).2.1 (hpos i).le,
      mul_le_mul_of_nonneg_right (u i).2.2 (hpos i).le⟩
  apply bounded_ratio_models_avoid h g α β hα hβ (by simp [g]) hpos hratio
  intro N δ D hδ hD
  let v (m i : ℕ) := ∏ j ∈ Finset.range i, (t (φ m) j : ℝ)
  have hv (i : ℕ) : Tendsto (fun m => v m i) atTop (𝓝 (g i)) := by
    apply tendsto_finsetProd
    intro j _
    exact continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp hu j)
  have close : ∀ᶠ m in atTop, ∀ i ∈ Finset.range (N+1), |v m i - g i| < δ :=
    (eventually_all_finset _).mpr fun i _ => by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp (hv i) δ hδ)
  have small := (hlim.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hD)
  obtain ⟨m, hclose, hsmall, hN⟩ := (close.and (small.and (eventually_ge_atTop N))).exists
  refine ⟨c (φ m), r (φ m), hr _, hsmall.le, fun i hi => ⟨_, rows (φ m) i
    (hi.trans (hN.trans (hφ.id_le m))), ?_⟩⟩
  simpa [v, (hr (φ m)).ne'] using hclose i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem geometric_models_avoid (h : H1) {A : Set ℝ} (q : ℝ) (hq : q ∈ Ioo 0 1)
    (model : ∀ (N : ℕ) (δ D : ℝ), 0 < δ → 0 < D →
      ∃ c r : ℝ, 0 < r ∧ r ≤ D ∧ ∀ i ≤ N, ∃ z ∈ A, |(z - c) / r - q ^ i| < δ) :
    Erdos120.Erdos120For A :=
  bounded_ratio_models_avoid h (fun i => q ^ i) q q hq.1 hq.2 (pow_zero q)
    (pow_pos hq.1) (fun i => by simp [pow_succ, mul_comm]) model

/-- Widen each isolated exponent 2^n to a row of n+1 consecutive exponents. -/
theorem dyadic_rows_avoid (h : H1) :
    Erdos120.Erdos120For {x | ∃ n i : ℕ, i ≤ n ∧ x = (1 / 2 : ℝ) ^ (2 ^ n + i)} := by
  apply variable_rows_avoid h (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)
    (fun _ _ => ⟨1 / 2, le_rfl, le_rfl⟩)
    (fun _ => 0) (fun n : ℕ => (1 / 2 : ℝ) ^ (2 ^ n : ℕ)) (by intro n; positivity)
  · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num)).comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ)))
  · intro n i hi
    exact ⟨n, i, hi, by simp [pow_add]⟩

/-- The isolated powers already fail to model the first three points of any strictly
decreasing positive profile. The two gaps determine explicit accuracy and scale bounds. -/
theorem doubleLacunary_excludes_three (g : ℕ → ℝ) (h0 : g 0 = 1)
    (h21 : g 2 < g 1) (h10 : g 1 < 1) (h1 : 0 < g 1) :
    let d := min (1 - g 1) (g 1 - g 2)
    ¬ ∃ c r : ℝ, 0 < r ∧ r ≤ d / 64 ∧
      ∀ i ≤ 2, ∃ z ∈ range (fun n : ℕ => (1 / 2 : ℝ) ^ (2 ^ n : ℕ)),
        |(z - c) / r - g i| < d / 8 := by
  dsimp only
  let doubleLacunary (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (2 ^ n : ℕ)
  have doubleLacunary_strictAnti : StrictAnti doubleLacunary :=
    (pow_right_strictAnti₀ (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)).comp_strictMono
      (pow_right_strictMono₀ (by decide : 1 < (2 : ℕ)))
  let d := min (1 - g 1) (g 1 - g 2)
  have hd : 0 < d := lt_min (sub_pos.mpr h10) (sub_pos.mpr h21)
  have hd1 : d ≤ 1 - g 1 := min_le_left _ _
  have hd2 : d ≤ g 1 - g 2 := min_le_right _ _
  rintro ⟨c, r, hr, hrD, h⟩
  change ∀ i ≤ 2, ∃ z ∈ range doubleLacunary, _ at h
  let u (z : ℝ) := (z - c) / r
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h 0 (by decide)
  obtain ⟨_, ⟨j, rfl⟩, hj⟩ := h 1 (by decide)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := h 2 (by decide)
  rw [h0] at hi
  replace hi : -(d/8) < u (doubleLacunary i) - 1 ∧ u (doubleLacunary i) - 1 < d/8 :=
    abs_lt.mp hi
  replace hj : -(d/8) < u (doubleLacunary j) - g 1 ∧ u (doubleLacunary j) - g 1 < d/8 :=
    abs_lt.mp hj
  replace hk : -(d/8) < u (doubleLacunary k) - g 2 ∧ u (doubleLacunary k) - g 2 < d/8 :=
    abs_lt.mp hk
  have gap (a b : ℝ) : (u a - u b) * r = a - b := by
    dsimp [u]
    field_simp
    ring
  have hji : doubleLacunary j < doubleLacunary i := by
    have : 0 < u (doubleLacunary i) - u (doubleLacunary j) := by linarith [hi.1, hj.2]
    have hpos := mul_pos this hr
    rwa [gap, sub_pos] at hpos
  have hij : i + 1 ≤ j := doubleLacunary_strictAnti.lt_iff_gt.mp hji
  have hsq : doubleLacunary j ≤ (doubleLacunary i)^2 := by
    simpa only [doubleLacunary, pow_succ (2 : ℕ), pow_mul] using
      doubleLacunary_strictAnti.antitone hij
  have hhalf : doubleLacunary i ≤ 1 / 2 := by
    simpa [doubleLacunary] using doubleLacunary_strictAnti.antitone (Nat.zero_le i)
  have hpos (m : ℕ) : 0 ≤ doubleLacunary m := by unfold doubleLacunary; positivity
  have hdif : doubleLacunary i - doubleLacunary j < 2 * r := by
    rw [← gap]
    apply mul_lt_mul_of_pos_right _ hr
    linarith [hi.2, hj.1, h1]
  have hsmall : doubleLacunary i < 4 * r := by
    nlinarith [mul_nonneg (hpos i) (sub_nonneg.mpr hhalf)]
  have hlower : d/2 * r < doubleLacunary j - doubleLacunary k := by
    rw [← gap]
    apply mul_lt_mul_of_pos_right _ hr
    linarith [hj.1, hk.2]
  have hsquare := mul_self_lt_mul_self (hpos i) hsmall
  change r ≤ d / 64 at hrD
  nlinarith [mul_nonneg (sub_nonneg.mpr hrD) hr.le, hpos k]

/-- An avoiding set for a sequence also avoids any set containing an affine copy of the sequence. -/
theorem avoid_of_affine_sequence {A : Set ℝ} {f : ℕ → ℝ}
    (hf : Erdos120.Erdos120For (range f)) (s t : ℝ) (hs : s ≠ 0)
    (hsub : ∀ n, s * f n + t ∈ A) : Erdos120.Erdos120For A := by
  obtain ⟨E, hE, hvol, havoid⟩ := hf
  refine ⟨E, hE, hvol, ?_⟩
  intro a b ha hAE
  apply havoid (a * s) (a * t + b) (mul_ne_zero ha hs)
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  convert hAE (mem_image_of_mem (fun x : ℝ => a * x + b) (hsub n)) using 1
  ring

/-- Every bounded infinite set contains, up to translation and reflection, the range of a
strictly decreasing positive sequence converging to zero. Unbounded sets already avoid the unit
interval at every nonzero scale. -/
theorem null_sequences_suffice
    (hnull : ∀ f : ℕ → ℝ, StrictAnti f → (∀ n, 0 < f n) →
      Tendsto f atTop (𝓝 0) → Erdos120.Erdos120For (range f)) :
    ∀ A : Set ℝ, A.Infinite → Erdos120.Erdos120For A := by
  intro A hA
  by_cases fits : ∃ a b : ℝ, a ≠ 0 ∧ (fun x => a * x + b) '' A ⊆ Icc 0 1
  · obtain ⟨a, b, ha, hAB⟩ := fits
    let : Infinite A := hA.to_subtype
    obtain ⟨f, hf⟩ := Infinite.exists_strictMono_or_strictAnti A
    let g (n : ℕ) := (f n : ℝ)
    have hI (n : ℕ) : a * g n + b ∈ Icc 0 1 :=
      hAB (mem_image_of_mem _ (f n).property)
    obtain ⟨l, _, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hI
    let y (n : ℕ) := g (φ n)
    let L := (l - b) / a
    have hconv : Tendsto y atTop (𝓝 L) := by
      convert (hlim.sub_const b).div_const a using 1
      funext n
      dsimp [y, Function.comp_def]
      field_simp
      ring
    rcases hf with inc | dec
    · have hinc : StrictMono y := fun _ _ h => inc (hφ h)
      have hpositive (n : ℕ) : 0 < L - y n := sub_pos.mpr <|
        (hinc (Nat.lt_succ_self n)).trans_le (hinc.monotone.ge_of_tendsto hconv (n+1))
      have hanti : StrictAnti (fun n => L - y n) := fun _ _ h => sub_lt_sub_left (hinc h) L
      have ht : Tendsto (fun n => L - y n) atTop (𝓝 0) := by
        simpa using hconv.const_sub L
      apply avoid_of_affine_sequence (hnull _ hanti hpositive ht) (-1) L (by norm_num)
      intro n
      simp [y, g]
    · have hdec : StrictAnti y := fun _ _ h => dec (hφ h)
      have hpositive (n : ℕ) : 0 < y n - L := sub_pos.mpr <|
        (hdec.antitone.le_of_tendsto hconv (n+1)).trans_lt (hdec (Nat.lt_succ_self n))
      have hanti : StrictAnti (fun n => y n - L) := fun _ _ h => sub_lt_sub_right (hdec h) L
      have ht : Tendsto (fun n => y n - L) atTop (𝓝 0) := by
        simpa using hconv.sub_const L
      apply avoid_of_affine_sequence (hnull _ hanti hpositive ht) 1 L one_ne_zero
      intro n
      simp [y, g]
  · exact ⟨Icc 0 1, measurableSet_Icc, by simp, fun a b ha hsub => fits ⟨a,b,ha,hsub⟩⟩

theorem main : H1 → H2 → type_of% @Erdos120.erdos_120 := by
  classical
  intro h residual
  apply null_sequences_suffice
  intro f hanti hpos hlim
  by_contra hn
  apply hn
  apply residual f hanti hpos hlim
  rintro ⟨g, α, β, hα, hβ, h0, hp, hr, model⟩
  exact hn (bounded_ratio_models_avoid h g α β hα hβ h0 hp hr model)

end OMA.R_Erdos120_erdos_120_R1
