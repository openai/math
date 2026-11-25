import OAI.Geometry.Hirsch.Product

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

theorem System.isClosed_body {Space Row : Type} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] [FiniteDimensional ℝ Space] (sys : System Space Row) :
    IsClosed sys.body := by
  simp only [System.body, ofPred_forall]
  exact isClosed_iInter fun row =>
    isClosed_le continuous_const (sys.normal row).continuous_of_finiteDimensional

namespace Polygon

variable {count : ℕ}

def slope (idx : Fin count) : ℝ := 2 * idx.val - 1

def cap (count : ℕ) : ℝ := (2 * (count : ℝ)) ^ 2 + 1

def system (count : ℕ) : System (ℝ × ℝ) (Option (Fin count)) where
  normal
    | none => -LinearMap.snd ℝ ℝ ℝ
    | some idx => LinearMap.snd ℝ ℝ ℝ - slope idx • LinearMap.fst ℝ ℝ ℝ
  rhs
    | none => -cap count
    | some idx => -(slope idx)^2

theorem slope_inj : Function.Injective (slope (count := count)) := by
  intro first last he
  apply Fin.ext
  unfold slope at he
  exact_mod_cast (show (first.val : ℝ) = last.val by linarith)

theorem slope_ne_zero (idx : Fin count) : slope idx ≠ 0 := by
  intro he
  unfold slope at he
  have hh : 2 * idx.val = 1 := by exact_mod_cast (sub_eq_zero.mp he)
  omega

theorem sq_lt_cap (idx : Fin count) : slope idx ^ 2 < cap count := by
  have hh : (idx.val : ℝ) + 1 ≤ count := by exact_mod_cast idx.isLt
  have hn : (0 : ℝ) ≤ idx.val := Nat.cast_nonneg _
  unfold slope cap
  nlinarith

theorem used : (system count).used = univ := by
  apply eq_univ_of_forall
  rintro (_ | idx)
  · refine ⟨(0, cap count), ?_, rfl⟩
    rintro (_ | idx)
    · exact le_rfl
    · change -slope idx ^ 2 ≤ cap count - slope idx * 0
      nlinarith [sq_lt_cap idx]
  · refine ⟨(2 * slope idx, slope idx ^ 2), ?_, ?_⟩
    · rintro (_ | other)
      · exact neg_le_neg (sq_lt_cap idx).le
      · change -slope other ^ 2 ≤ slope idx ^ 2 - slope other * (2 * slope idx)
        nlinarith [sq_nonneg (slope other - slope idx)]
    · change slope idx ^ 2 - slope idx * (2 * slope idx) = -slope idx ^ 2
      ring

theorem compact (hc : 2 ≤ count) : IsCompact (system count).body := by
  let bound := cap count + 1
  apply (isCompact_Icc (a := (-bound, -bound)) (b := (bound, bound))).of_isClosed_subset
    (system count).isClosed_body
  intro point hp
  have hl := hp (some ⟨0, by omega⟩)
  have hr := hp (some ⟨1, by omega⟩)
  have ht := hp none
  simp [system, slope] at hl hr ht
  have hn : 0 ≤ cap count := by unfold cap; positivity
  change (-bound ≤ point.1 ∧ -bound ≤ point.2) ∧ (point.1 ≤ bound ∧ point.2 ≤ bound)
  dsimp [bound]
  constructor <;> constructor <;> linarith

theorem intersection {point : ℝ × ℝ} {first last : Fin count} (hne : first ≠ last)
    (hf : some first ∈ (system count).active point)
    (hl : some last ∈ (system count).active point) :
    point.1 = slope first + slope last ∧ point.2 < cap count := by
  change point.2 - slope first * point.1 = -slope first ^ 2 at hf
  change point.2 - slope last * point.1 = -slope last ^ 2 at hl
  have he : (slope first - slope last) * (point.1 - (slope first + slope last)) = 0 := by
    linarith
  have hx := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left
    (sub_ne_zero.mpr (slope_inj.ne hne)))
  rw [hx] at hf
  exact ⟨hx, by nlinarith [sq_lt_cap first, sq_lt_cap last, sq_nonneg (slope first - slope last)]⟩

theorem regular : (system count).Regular := by
  intro point _ values
  by_cases hex : ∃ idx, some idx ∈ (system count).active point
  swap
  · refine ⟨(0, -values none), ?_⟩
    rintro (_ | idx) hh
    · exact neg_neg _
    · exact (hex ⟨idx, hh⟩).elim
  obtain ⟨first, hf⟩ := hex
  by_cases htwo : ∃ last ≠ first, some last ∈ (system count).active point
  swap
  · refine ⟨((-values none - values (some first)) / slope first, -values none), ?_⟩
    rintro (_ | idx) hh
    · exact neg_neg _
    · have he : idx = first := by by_contra hn; exact htwo ⟨idx, hn, hh⟩
      subst idx
      change -values none - slope first * ((_ - _) / _) = _
      rw [mul_div_cancel₀ _ (slope_ne_zero first)]
      ring
  obtain ⟨last, hne, hl⟩ := htwo
  obtain ⟨hx, hy⟩ := intersection hne hl hf
  let dx := (values (some first) - values (some last)) / (slope last - slope first)
  have hd : (slope last - slope first) * dx = values (some first) - values (some last) :=
    mul_div_cancel₀ _ (sub_ne_zero.mpr (slope_inj.ne hne))
  refine ⟨(dx, values (some first) + slope first * dx), ?_⟩
  rintro (_ | idx) hh
  · exact (hy.ne (neg_inj.mp hh)).elim
  change values (some first) + slope first * dx - slope idx * dx = _
  by_cases he : idx = first
  · rw [he, add_sub_cancel_right]
  have hh' := (intersection he hh hf).1
  have heq : idx = last := slope_inj (by linarith)
  rw [heq]
  linarith

def poly (count : ℕ) (hc : 2 ≤ count) : Polytope where
  Space := ℝ × ℝ
  Coord := Unit ⊕ Unit
  basis := (Basis.singleton Unit ℝ).prod (Basis.singleton Unit ℝ)
  Row := Option (Fin count)
  sys := system count
  rationalNormal := by
    rintro (_ | idx) (coord | coord)
    · exact ⟨0, by simp [system]⟩
    · exact ⟨-1, by simp [system]⟩
    · exact ⟨-(2 * idx.val - 1), by simp [system, slope]⟩
    · exact ⟨1, by simp [system]⟩
  rationalRhs := by
    rintro (_ | idx)
    · exact ⟨-((2 * (count : ℚ)) ^ 2 + 1), by simp [system, cap]⟩
    · exact ⟨-(2 * (idx.val : ℚ) - 1)^2, by simp [system, slope]⟩
  compact := compact hc
  nonempty := by
    obtain ⟨point, hp, _⟩ := (show none ∈ (system count).used by rw [used]; trivial)
    exact ⟨point, hp⟩

end Polygon

theorem polygon (sides : ℕ) (hs : 3 ≤ sides) :
    ∃ poly : Polytope, poly.sys.Regular ∧ poly.dimension = 2 ∧ poly.facetCount = sides := by
  let poly := Polygon.poly (sides - 1) (by omega)
  have reg : poly.sys.Regular := Polygon.regular
  refine ⟨poly, reg, ?_, ?_⟩
  · rw [Polytope.dimension, reg.dim_body poly.nonempty]
    change finrank ℝ (ℝ × ℝ) = 2
    simp
  · rw [Polytope.facetCount, reg.facet_count]
    change (Polygon.system (sides - 1)).used.ncard = _
    simp [Polygon.used, Nat.sub_add_cancel (show 1 ≤ sides by omega)]

namespace Simplex

variable {size : ℕ}

def total (size : ℕ) : (Fin size → ℝ) →ₗ[ℝ] ℝ :=
  ∑ idx, LinearMap.proj idx

@[simp] theorem total_apply (point : Fin size → ℝ) : total size point = ∑ idx, point idx := by
  simp [total, LinearMap.sum_apply]

def system (size : ℕ) : System (Fin size → ℝ) (Option (Fin size)) where
  normal
    | none => -total size
    | some idx => LinearMap.proj idx
  rhs
    | none => -1
    | some _ => 0

theorem zero_mem : 0 ∈ (system size).body := by
  rintro (_ | idx) <;> simp [system]

theorem compact : IsCompact (system size).body := by
  apply (isCompact_Icc (a := (0 : Fin size → ℝ)) (b := 1)).of_isClosed_subset
    (system size).isClosed_body
  intro point hp
  have hn : ∀ idx, 0 ≤ point idx := fun idx => hp (some idx)
  have hu : ∑ idx, point idx ≤ 1 := by simpa [system] using hp none
  exact ⟨hn, fun idx => (Finset.single_le_sum (fun other _ => hn other) (Finset.mem_univ idx)).trans hu⟩

theorem used (hs : 0 < size) : (system size).used = univ := by
  apply eq_univ_of_forall
  rintro (_ | idx)
  · let first : Fin size := ⟨0, hs⟩
    refine ⟨Pi.single first 1, ?_, ?_⟩
    · rintro (_ | idx)
      · simp [system]
      · simp [system, Pi.single_apply]; split <;> norm_num
    · simp [System.active, system]
  · exact ⟨0, zero_mem, rfl⟩

theorem regular : (system size).Regular := by
  intro point _ values
  let base := fun idx => values (some idx)
  by_cases ht : none ∈ (system size).active point
  swap
  · refine ⟨base, ?_⟩
    rintro (_ | idx) hh
    · exact (ht hh).elim
    · rfl
  have hex : ∃ idx, point idx ≠ 0 := by
    by_contra! hn
    simp [System.active, system, hn] at ht
  obtain ⟨idx, hi⟩ := hex
  refine ⟨base + Pi.single idx (-values none - total size base), ?_⟩
  rintro (_ | other) hh
  · simp [system, map_add]
  · have hn : other ≠ idx := by rintro rfl; exact hi hh
    simp [system, base, hn]

def poly (size : ℕ) : Polytope where
  Space := Fin size → ℝ
  Coord := Fin size
  basis := Pi.basisFun ℝ _
  Row := Option (Fin size)
  sys := system size
  rationalNormal := by
    rintro (_ | idx) coord
    · exact ⟨-1, by simp [system, Pi.basisFun_apply]⟩
    · by_cases he : idx = coord
      · exact ⟨1, by simp [system, Pi.basisFun_apply, he]⟩
      · exact ⟨0, by simp [system, Pi.basisFun_apply, he]⟩
  rationalRhs := by
    rintro (_ | idx)
    · exact ⟨-1, by simp [system]⟩
    · exact ⟨0, by simp [system]⟩
  compact := compact
  nonempty := ⟨0, zero_mem⟩

end Simplex

theorem simplex (size : ℕ) (hs : 0 < size) :
    ∃ poly : Polytope, poly.sys.Regular ∧ poly.dimension = size ∧ poly.facetCount = size + 1 := by
  let poly := Simplex.poly size
  have reg : poly.sys.Regular := Simplex.regular
  refine ⟨poly, reg, ?_, ?_⟩
  · rw [Polytope.dimension, reg.dim_body poly.nonempty]
    change finrank ℝ (Fin size → ℝ) = _
    simp
  · rw [Polytope.facetCount, reg.facet_count]
    change (Simplex.system size).used.ncard = _
    simp [Simplex.used hs]

end OAI.Geometry.Hirsch
