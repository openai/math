import OAI.Geometry.Hirsch.Blocking
import OAI.Geometry.Hirsch.Excess

noncomputable section

open Set Module Filter

namespace OAI.Geometry.Hirsch

structure Episodes (count : ℕ) where
  left : Fin count → ℝ
  right : Fin count → ℝ
  positive : ∀ idx, 0 < left idx
  width : ∀ idx, left idx < right idx
  interior : ∀ idx, right idx < 1
  ordered : ∀ {first last}, first < last → right first < left last

def Spans (first last left right : ℝ) : Prop :=
  min first last ≤ left ∧ right ≤ max first last

def Segments {Space : Type} [AddCommGroup Space] [Module ℝ Space] (region : Set Space)
    {len : ℕ} (pts : Fin (len + 1) → Space) : Prop :=
  ∀ idx : Fin len, segment ℝ (pts idx.castSucc) (pts idx.succ) ⊆ region

def CrossingBound {Coord : Type} (region : Set (Timed Coord)) (left right : ℝ) (cost : ℕ) : Prop :=
  ∀ len (pts : Fin (len + 1) → Timed Coord), Segments region pts →
    Spans (pts 0).1 (pts (Fin.last len)).1 left right → cost ≤ len

def CrossingSeed (degree scale mult : ℕ) (eta gamma : ℝ) (episodes : Episodes scale) : Prop :=
  ∃ (Coord Row : Type) (_ : Fintype Coord) (_ : Fintype Row) (block : Blocking Coord Row),
    (Fintype.card Coord + 1 : ℕ) ≤ (scale : ℝ) ^ eta ∧
    (Fintype.card Row + 3 : ℕ) ≤ mult * (scale : ℝ) ^ (1 + eta) ∧
    let region := block.thin (⌊(scale : ℝ) ^ gamma⌋₊ + 1)
    CrossingBound region 0 1 (mult * scale ^ degree) ∧
    ∀ idx, CrossingBound region (episodes.left idx) (episodes.right idx)
      (mult * scale ^ (degree - 1) + 1)

def FiniteScale : Prop :=
  ∀ degree : ℕ, 2 ≤ degree → ∀ eta : ℝ, 0 < eta → eta < 1 →
    ∃ base : ℕ, 2 ≤ base ∧ ∃ gamma : ℝ, 0 < gamma ∧
      ∀ᶠ height : ℕ in atTop, ∀ mult : ℕ, 1 ≤ mult → ∀ episodes : Episodes (base ^ height),
        CrossingSeed degree (base ^ height) mult eta gamma episodes

def grid (scale : ℕ) (hs : 0 < scale) : Episodes scale where
  left idx := (idx.val + 1/4) / scale
  right idx := (idx.val + 3/4) / scale
  positive _ := by positivity
  width _ := by gcongr; norm_num
  interior idx := by
    apply (div_lt_one (by positivity)).mpr
    have hh : (idx.val : ℝ) + 1 ≤ scale := by exact_mod_cast idx.isLt
    linarith
  ordered := by
    intro first last hh
    apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
    have ht : (first.val : ℝ) + 1 ≤ last.val := by exact_mod_cast hh
    linarith

theorem grid_spanned {scale : ℕ} (hs : 0 < scale) {first last : ℝ}
    (hf : first ∈ Icc (-(1 / (scale : ℝ))) (1 + 1 / scale))
    (hl : last ∈ Icc (-(1 / (scale : ℝ))) (1 + 1 / scale))
    (hgap : 8 / (scale : ℝ) ≤ |first - last|) :
    ∃ idx, Spans first last ((grid scale hs).left idx) ((grid scale hs).right idx) := by
  have hp : (0 : ℝ) < scale := by positivity
  let lo := min first last * scale
  let hi := max first last * scale
  have hlow : -1 ≤ lo := by
    apply (div_le_iff₀ hp).mp
    simpa only [neg_div] using le_min hf.1 hl.1
  have hhigh : hi ≤ scale + 1 := by
    apply (le_div_iff₀ hp).mp
    simpa [add_div, hp.ne'] using max_le hf.2 hl.2
  have hdiff : 8 ≤ hi - lo := by
    rw [show hi - lo = |first - last| * scale by
      unfold hi lo; rw [← sub_mul, max_sub_min_eq_abs, abs_sub_comm]]
    exact (div_le_iff₀ hp).mp hgap
  let idx := ⌊lo + 1⌋₊
  have hle : (idx : ℝ) ≤ lo + 1 := Nat.floor_le (by linarith)
  have hlt : lo + 1 < (idx : ℝ) + 1 := Nat.lt_floor_add_one _
  have hv : idx < scale := Nat.cast_lt.mp (show (idx : ℝ) < scale by linarith)
  refine ⟨⟨idx, hv⟩, (le_div_iff₀ hp).mpr ?_, (div_le_iff₀ hp).mpr ?_⟩
  · change lo ≤ idx + 1/4
    linarith
  · change (idx : ℝ) + 3/4 ≤ hi
    linarith

theorem Polytope.Objective.gap_le_one {poly : Polytope} (obj : poly.Objective)
    (first last : poly.V) : obj.gap first last ≤ 1 := by
  apply (div_le_one (sub_pos.mpr obj.positive)).mpr
  have hf := obj.bounds _ first.property.1
  have hl := obj.bounds _ last.property.1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem cappedSeed_of_grid {degree scale mult : ℕ} {eta gamma : ℝ}
    (hd : 2 ≤ degree) (hs : 8 ≤ scale) (hg : 0 < gamma)
    (seed : CrossingSeed (degree + 1) scale mult eta gamma (grid scale (by omega))) :
    CappedSeed degree scale mult eta gamma := by
  classical
  obtain ⟨Coord, Row, ic, ir, block, hdim, hfac, _, hcross⟩ := seed
  let := ic
  let := ir
  have hp : (0 : ℝ) < scale := by exact_mod_cast (show 0 < scale by omega)
  have hge : (8 : ℝ) ≤ scale := by exact_mod_cast hs
  let margin := 1 / (scale : ℝ)
  let moves := ⌊(scale : ℝ) ^ gamma⌋₊
  have hm : 1 ≤ moves := Nat.le_floor (by simpa using Real.one_le_rpow (by linarith : (1 : ℝ) ≤ scale) hg.le)
  obtain ⟨roof, vec, hv⟩ := block.strict_witnesses (margin := margin) (by positivity)
  let sys := block.capped margin roof
  let obj := LinearMap.fst ℝ ℝ (Vec Coord)
  have hc : sys.Cost (sys.lowDim moves) obj (8 / scale) (mult * scale ^ degree) := by
    intro len pts ⟨hpts, ha⟩ hgap
    have hseg : Segments (block.thin (moves + 1)) pts := by
      intro idx pt hpt
      obtain ⟨rows, hr, hl, hu⟩ := ha idx
      have hf := (sys.isFace_locus rows).convex.segment_subset ⟨hpts _, hl⟩ ⟨hpts _, hu⟩ hpt
      exact block.thin_of_capped hf hr
    obtain ⟨idx, hi⟩ := grid_spanned (show 0 < scale by omega)
      (block.mem_capped.mp (hpts 0)).2.1 (block.mem_capped.mp (hpts (Fin.last len))).2.1 hgap
    have hb := hcross idx len pts hseg hi
    simp only [Nat.add_sub_cancel] at hb
    omega
  let basis := (Basis.singleton Unit ℝ).prod (Pi.basisFun ℝ Coord)
  obtain ⟨poly, objective, reg, hpd, hpf, hcost⟩ := rationalize basis (data := Data.ofSystem sys)
    (obj := obj) (block.compact_capped margin roof) (hv 0 (by simp)) (hv 1 (by simp))
    (by change 1 ≤ (1 : ℝ) - 0; norm_num) hm hc
  refine ⟨poly, objective, reg, ?_, ?_, ?_⟩
  · rw [hpd]
    simpa [Nat.add_comm] using hdim
  · apply le_trans (Nat.cast_le.mpr hpf)
    simpa using hfac
  intro first last
  let gap := objective.gap first last
  have hu : gap ≤ 1 := objective.gap_le_one first last
  constructor
  · intro he
    apply hcost
    rw [he]
    exact (div_le_one hp).mpr hge
  by_cases hsep : 8 / (scale : ℝ) ≤ gap
  · have hb := hcost first last hsep
    have he : max 0 ((scale : ℝ) * gap - 8) ≤ scale :=
      max_le hp.le (by nlinarith)
    calc
      _ ≤ mult * (scale : ℝ) ^ (degree - 1) * scale := mul_le_mul_of_nonneg_left he (by positivity)
      _ = (mult * scale ^ degree : ℕ) := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ degree), Nat.cast_mul, Nat.cast_pow]
      _ ≤ _ := Nat.cast_le.mpr hb
  · have hh := (lt_div_iff₀ hp).mp (lt_of_not_ge hsep)
    rw [max_eq_left (show (scale : ℝ) * objective.gap first last - 8 ≤ 0 by unfold gap at hh; linarith)]
    simp

theorem cap_of_crossing (seed : FiniteScale) : CapLemma := by
  intro degree hd eta he he'
  obtain ⟨base, hb, gamma, hg, hs⟩ := seed (degree + 1) (by omega) eta he he'
  refine ⟨base, hb, gamma, hg, ?_⟩
  filter_upwards [hs, eventually_ge_atTop 3] with height hh hheight mult hm
  have hscale : 8 ≤ base ^ height := calc
    8 = 2 ^ 3 := rfl
    _ ≤ base ^ height := by gcongr; omega
  exact cappedSeed_of_grid hd hscale hg (hh mult hm _)

theorem main_of_crossing (seed : FiniteScale) : MainTheorem := main_of_cap (cap_of_crossing seed)

theorem excess_of_crossing (seed : FiniteScale) : ExcessTheorem := excess_of_cap (cap_of_crossing seed)

theorem not_polynomialHirsch_of_crossing (seed : FiniteScale) : ¬ PolynomialHirsch :=
  not_polynomialHirsch_of_main (main_of_crossing seed)

end OAI.Geometry.Hirsch
