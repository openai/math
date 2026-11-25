import Mathlib.Tactic

/-! # Endpoint couplings in the exterior-algebra wire decomposition

The exponent table records the four placements of two marked indices. Splitting
the first index reduces the range of the two column gaps by an exact factor
of two in each child. Consequently the independent endpoint cost at each leaf
is controlled by the cost of any coupling of the initial marginals.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

abbrev EndpointTable := Fin 2 → Fin 2 → ℝ

namespace EndpointTable

noncomputable section

/-- Endpoint masses of a point at fraction `u` along an interval. -/
def bernoulliWeight (u : ℝ) : Fin 2 → ℝ := ![1 - u, u]

/-- Product distribution of the two endpoint choices. -/
def independent (u v : ℝ) : EndpointTable := fun i j ↦ bernoulliWeight u i * bernoulliWeight v j

/-- Cost of the endpoint coupling `w` on the table `N`. -/
def cost (w N : EndpointTable) : ℝ := ∑ i, ∑ j, w i j * N i j

/-- A coupling of the two prescribed Bernoulli distributions. -/
structure IsCoupling (w : EndpointTable) (u v : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ w i j
  row_sum : ∀ i, ∑ j, w i j = bernoulliWeight u i
  col_sum : ∀ j, ∑ i, w i j = bernoulliWeight v j

theorem independent_isCoupling {u v : ℝ} (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) :
    IsCoupling (independent u v) u v := by
  have hnonneg {a : ℝ} (ha : a ∈ Set.Icc 0 1) (i : Fin 2) : 0 ≤ bernoulliWeight a i := by
    fin_cases i
    · exact sub_nonneg.mpr ha.2
    · exact ha.1
  refine ⟨fun i j ↦ mul_nonneg (hnonneg hu i) (hnonneg hv j), ?_, ?_⟩
  · intro i
    change (∑ j, bernoulliWeight u i * bernoulliWeight v j) = _
    rw [← Finset.mul_sum]
    simp [Fin.sum_univ_two, bernoulliWeight]
  · intro j
    change (∑ i, bernoulliWeight u i * bernoulliWeight v j) = _
    rw [← Finset.sum_mul]
    simp [Fin.sum_univ_two, bernoulliWeight]

/-- The coupling supported on synchronized choices of endpoints. -/
def synchronized (u : ℝ) : EndpointTable := fun i j ↦ if i = j then bernoulliWeight u i else 0

theorem synchronized_isCoupling {u : ℝ} (hu : u ∈ Set.Icc 0 1) : IsCoupling (synchronized u) u u := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold synchronized
    split_ifs
    · fin_cases i
      · exact sub_nonneg.mpr hu.2
      · exact hu.1
    · rfl
  · intro i
    simp [synchronized]
  · intro j
    simp [synchronized]

theorem cost_synchronized (u : ℝ) (M : EndpointTable) :
    cost (synchronized u) M = (1-u) * M 0 0 + u * M 1 1 := by
  simp [cost, Fin.sum_univ_two, synchronized, bernoulliWeight]

/-- Difference of the upper and lower entries in a column. -/
def gap (N : EndpointTable) (j : Fin 2) : ℝ := N 0 j - N 1 j

/-- Width of the two column gaps. -/
def width (N : EndpointTable) : ℝ := |gap N 0 - gap N 1|

/-- The threshold for the two exterior levels at a node. -/
def midpoint (N : EndpointTable) : ℝ := (gap N 0 + gap N 1) / 2

/-- Exponent tables of the two children in the exterior decomposition. -/
def plus (N : EndpointTable) : EndpointTable := ![fun j ↦ min (N 0 j) (N 1 j + midpoint N), N 1]

def minus (N : EndpointTable) : EndpointTable := ![N 0, fun j ↦ min (N 1 j) (N 0 j - midpoint N)]

theorem plus_le (N : EndpointTable) : plus N ≤ N := by
  intro i j
  fin_cases i
  · exact min_le_left _ _
  · rfl

theorem minus_le (N : EndpointTable) : minus N ≤ N := by
  intro i j
  fin_cases i
  · rfl
  · exact min_le_left _ _

theorem gap_plus (N : EndpointTable) (j : Fin 2) : gap (plus N) j = min (gap N j) (midpoint N) := by
  change min (N 0 j) (N 1 j + midpoint N) - N 1 j = _
  rw [← min_sub_sub_right, add_sub_cancel_left]
  rfl

theorem gap_minus (N : EndpointTable) (j : Fin 2) : gap (minus N) j = max (gap N j) (midpoint N) := by
  change N 0 j - min (N 1 j) (N 0 j - midpoint N) = _
  rw [← max_sub_sub_left, sub_sub_cancel]
  rfl

private theorem midpoint_width (x y : ℝ) :
    |min x ((x+y)/2) - min y ((x+y)/2)| = |x-y| / 2 ∧
    |max x ((x+y)/2) - max y ((x+y)/2)| = |x-y| / 2 := by
  rcases le_total x y with h | h
  · have hx : x ≤ (x+y)/2 := by linarith
    have hy : (x+y)/2 ≤ y := by linarith
    rw [min_eq_left hx, min_eq_right hy, max_eq_right hx, max_eq_left hy,
      abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hy),
      abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> ring
  · have hx : (x+y)/2 ≤ x := by linarith
    have hy : y ≤ (x+y)/2 := by linarith
    rw [min_eq_right hx, min_eq_left hy, max_eq_left hx, max_eq_right hy,
      abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (sub_nonneg.mpr hy),
      abs_of_nonneg (sub_nonneg.mpr h)]
    constructor <;> ring

theorem width_plus (N : EndpointTable) : width (plus N) = width N / 2 := by
  simpa only [width, gap_plus, midpoint] using (midpoint_width (gap N 0) (gap N 1)).1

theorem width_minus (N : EndpointTable) : width (minus N) = width N / 2 := by
  simpa only [width, gap_minus, midpoint] using (midpoint_width (gap N 0) (gap N 1)).2

/-- The mixed difference is the only part of the table detected by changing
a coupling while keeping its marginals. -/
theorem cost_sub_cost {w π : EndpointTable} {u v : ℝ} (hw : IsCoupling w u v)
    (hπ : IsCoupling π u v) (N : EndpointTable) :
    cost w N - cost π N = (w 0 0 - π 0 0) * (gap N 0 - gap N 1) := by
  have hr0 := (hw.row_sum 0).trans (hπ.row_sum 0).symm
  have hr1 := (hw.row_sum 1).trans (hπ.row_sum 1).symm
  have hc0 := (hw.col_sum 0).trans (hπ.col_sum 0).symm
  simp only [Fin.sum_univ_two] at hr0 hr1 hc0
  have h01 : w 0 1 = π 0 1 - (w 0 0 - π 0 0) := by linarith
  have h10 : w 1 0 = π 1 0 - (w 0 0 - π 0 0) := by linarith
  have h11 : w 1 1 = π 1 1 + (w 0 0 - π 0 0) := by linarith
  simp only [cost, Fin.sum_univ_two, gap, h01, h10, h11]
  ring

theorem cost_le_cost_add_width {w π : EndpointTable} {u v : ℝ} (hw : IsCoupling w u v)
    (hπ : IsCoupling π u v) (hu : 0 ≤ u) (N : EndpointTable) :
    cost w N ≤ cost π N + width N := by
  have hbound {p : EndpointTable} (hp : IsCoupling p u v) : p 0 0 ≤ 1 := by
    have h := hp.row_sum 0
    simp [Fin.sum_univ_two, bernoulliWeight] at h
    linarith [hp.nonneg 0 1]
  have ha : |w 0 0 - π 0 0| ≤ 1 := abs_le.mpr
    ⟨by linarith [hw.nonneg 0 0, hbound hπ], by linarith [hπ.nonneg 0 0, hbound hw]⟩
  have h : |cost w N - cost π N| ≤ width N := by
    rw [cost_sub_cost hw hπ, abs_mul]
    exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans_eq (one_mul _)
  linarith [(abs_le.mp h).2]

theorem cost_mono {π : EndpointTable} {u v : ℝ} (hπ : IsCoupling π u v) {M N : EndpointTable}
    (h : M ≤ N) : cost π M ≤ cost π N :=
  Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_left (h i j) (hπ.nonneg i j)

/-- The largest independent endpoint cost among the leaves after `a` splits. -/
def maxLeafCost (w : EndpointTable) : ℕ → EndpointTable → ℝ
  | 0, N => cost w N
  | a+1, N => max (maxLeafCost w a (plus N)) (maxLeafCost w a (minus N))

/-- The independent endpoint bound after a finite number of splits has error
at most the original gap width divided by two at each level. -/
theorem maxLeafCost_le {w π : EndpointTable} {u v : ℝ} (hw : IsCoupling w u v)
    (hπ : IsCoupling π u v) (hu : 0 ≤ u) (a : ℕ) (N : EndpointTable) :
    maxLeafCost w a N ≤ cost π N + width N / 2^a := by
  induction a generalizing N with
  | zero => simpa [maxLeafCost] using cost_le_cost_add_width hw hπ hu N
  | succ a ih =>
    rw [maxLeafCost]
    apply max_le
    · refine (ih (plus N)).trans ?_
      rw [width_plus, pow_succ', div_div]
      exact add_le_add_left (cost_mono hπ (plus_le N)) _
    · refine (ih (minus N)).trans ?_
      rw [width_minus, pow_succ', div_div]
      exact add_le_add_left (cost_mono hπ (minus_le N)) _

theorem cost_independent (u v : ℝ) (N : EndpointTable) :
    cost (independent u v) N =
      (1-u)*(1-v)*N 0 0 + (1-u)*v*N 0 1 + u*(1-v)*N 1 0 + u*v*N 1 1 := by
  simp [Fin.sum_univ_two, cost, independent, bernoulliWeight, add_assoc]

/-- The initial gap bound follows from the two triangle inequalities for an
endpoint wire, and remains valid through all splits. -/
def GapBound (t : ℝ) (N : EndpointTable) : Prop := ∀ j, |gap N j| ≤ t

theorem GapBound.midpoint_le {N : EndpointTable} {t : ℝ} (h : GapBound t N) :
    |midpoint N| ≤ t := by
  have h0 := abs_le.mp (h 0)
  have h1 := abs_le.mp (h 1)
  unfold midpoint
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem GapBound.width_le {N : EndpointTable} {t : ℝ} (h : GapBound t N) : width N ≤ 2*t := by
  exact (abs_sub _ _).trans (by linarith [h 0, h 1])

theorem GapBound.plus {N : EndpointTable} {t : ℝ} (h : GapBound t N) : GapBound t N.plus := by
  intro j
  rw [gap_plus]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (h j)
  exact abs_le.mpr ⟨le_min hlo (abs_le.mp h.midpoint_le).1, (min_le_left _ _).trans hhi⟩

theorem GapBound.minus {N : EndpointTable} {t : ℝ} (h : GapBound t N) : GapBound t N.minus := by
  intro j
  rw [gap_minus]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (h j)
  exact abs_le.mpr ⟨hlo.trans (le_max_left _ _), max_le hhi (abs_le.mp h.midpoint_le).2⟩

/-- All actual endpoint exponents lie within the specified one-sided slack
of an ideal exponent table. -/
def BoundedBy (actual ideal : EndpointTable) (slack : ℝ) : Prop :=
  ∀ i j, actual i j ≤ ideal i j + slack

/-- Restrictions using the same endpoint and the opposite endpoint give the
plus table, up to accumulated error of the wire-dimension estimates. -/
theorem boundedBy_plus {P N Y : EndpointTable} {σ ε : ℝ} (hP : BoundedBy P N σ)
    (hsame : ∀ i j, Y i j ≤ P i j + ε)
    (hcross : ∀ j, Y 0 j ≤ P 1 j + N.midpoint + ε) : BoundedBy Y N.plus (σ+ε) := by
  intro i j
  fin_cases i
  · change Y 0 j ≤ min (N 0 j) (N 1 j + N.midpoint) + _
    rw [← min_add_add_right]
    exact le_min (by linarith [hP 0 j, hsame 0 j]) (by linarith [hP 1 j, hcross j])
  · change Y 1 j ≤ N 1 j + _
    linarith [hP 1 j, hsame 1 j]

/-- The second exterior restriction gives the minus table. -/
theorem boundedBy_minus {P N Y : EndpointTable} {σ ε : ℝ} (hP : BoundedBy P N σ)
    (hsame : ∀ i j, Y i j ≤ P i j + ε)
    (hcross : ∀ j, Y 1 j ≤ P 0 j - N.midpoint + ε) : BoundedBy Y N.minus (σ+ε) := by
  intro i j
  fin_cases i
  · change Y 0 j ≤ N 0 j + _
    linarith [hP 0 j, hsame 0 j]
  · change Y 1 j ≤ min (N 1 j) (N 0 j - N.midpoint) + _
    rw [← min_add_add_right]
    exact le_min (by linarith [hP 1 j, hsame 1 j]) (by linarith [hP 0 j, hcross j])

/-- Total mass one makes an additive uniform bound on entries transfer
without amplification to any endpoint coupling. -/
theorem IsCoupling.cost_le_of_boundedBy {w N M : EndpointTable} {u v σ : ℝ} (hw : IsCoupling w u v)
    (h : BoundedBy N M σ) : cost w N ≤ cost w M + σ := by
  have ht : (∑ i, ∑ j, w i j) = 1 := by simp [hw.row_sum, Fin.sum_univ_two, bernoulliWeight]
  calc
    cost w N ≤ ∑ i, ∑ j, w i j * (M i j + σ) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (h i j) (hw.nonneg i j)
    _ = cost w M + σ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ht,
      one_mul, cost]

variable {X : Type*}

/-- A depth-`a` path selected by retaining a child almost as large as its parent.
The ideal tables carry exact gap widths, while the actual exponents incur
at most `ε` of error per split. -/
theorem selectedPath (endpoint : X → EndpointTable) (interior : X → ℝ)
    {t ε : ℝ} (hε : 0 ≤ ε)
    (step : ∀ x N σ, GapBound t N → 0 ≤ σ → BoundedBy (endpoint x) N σ →
      ∃ (y : X) (C : EndpointTable), (C = N.plus ∨ C = N.minus) ∧
        interior x ≤ interior y + ε ∧ BoundedBy (endpoint y) C (σ+ε))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    ∃ y N, GapBound t N ∧ N ≤ M ∧ width N = width M / 2^a ∧
      interior root ≤ interior y + a*ε ∧ BoundedBy (endpoint y) N (a*ε) := by
  induction a with
  | zero =>
    exact ⟨root, M, hM, le_rfl, by simp, by simp,
      fun i j ↦ by simpa using hroot i j⟩
  | succ a ih =>
    obtain ⟨x, N, hN, hNM, hw, hv, hb⟩ := ih
    obtain ⟨y, C, hC, hxy, hy⟩ := step x N (a*ε) hN (by positivity) hb
    have hs : GapBound t C ∧ C ≤ N ∧ C.width = N.width / 2 := by
      rcases hC with rfl | rfl
      · exact ⟨hN.plus, plus_le _, width_plus _⟩
      · exact ⟨hN.minus, minus_le _, width_minus _⟩
    refine ⟨y, C, hs.1, hs.2.1.trans hNM, ?_, ?_, ?_⟩
    · rw [hs.2.2, hw, div_div, pow_succ]
    · push_cast
      linarith
    · simpa [Nat.cast_succ, add_mul] using hy

/-- Independent relocation at the selected leaf converts its two accumulated
errors (the interior value and the endpoint exponents) into an arbitrary
coupling bound for the root. -/
theorem selectedPath_coupling_bound (endpoint : X → EndpointTable) (interior : X → ℝ)
    {t ε u v : ℝ} (hε : 0 ≤ ε) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (π : EndpointTable) (hπ : IsCoupling π u v)
    (hinter : ∀ y, interior y ≤ cost (independent u v) (endpoint y))
    (step : ∀ x N σ, GapBound t N → 0 ≤ σ → BoundedBy (endpoint x) N σ →
      ∃ (y : X) (C : EndpointTable), (C = N.plus ∨ C = N.minus) ∧
        interior x ≤ interior y + ε ∧ BoundedBy (endpoint y) C (σ+ε))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    interior root ≤ cost π M + width M / 2^a + 2*a*ε := by
  obtain ⟨y, N, _, hNM, hw, hroot', hy⟩ := selectedPath endpoint interior hε step root M hM hroot a
  have hind := independent_isCoupling hu hv
  linarith [hinter y, hind.cost_le_of_boundedBy hy, cost_le_cost_add_width hind hπ hu.1 N,
    cost_mono hπ hNM]

end
end EndpointTable

end SpectralBooks
end LinearAlgebra
end OAI
