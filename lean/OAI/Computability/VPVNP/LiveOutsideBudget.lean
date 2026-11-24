import OAI.Computability.VPVNP.LiveEvaluatorTailCost
import OAI.Computability.VPVNP.LiveHeaderResources
import OAI.Computability.VPVNP.LiveProgramLayout
import OAI.Computability.VPVNP.LiveWordCapacity

/-!
# Choosing the physical processor count after the live preparation costs

The bound covers the header, preparation of the auxiliary inputs, the
exponent check and the evaluator tail. It bounds the tail uniformly over
all actual advice prefixes of the reserved size. The majorant substitutes
the input length for the RAM word width. For every fixed address exponent
this substitution holds eventually, so the polynomial degree in the
majorant is selected before that address exponent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.OutsideBudget

open Filter CursorBounds LiveEvaluatorTailCost

/-- A polynomial expression dominating either tail route at any raw prefix
length up to `A` and word width up to `W`. -/
def tailMajorant (A t Z M W : ℕ) :=
  let T := t*Z
  let k := 4*M+3
  let pack := 6*(W+1) + 23 + 11*(1+(A+W)*(W+1)) + 6*(1+t*(t+1))
  let init := 4 + pack + 10*(1+A) + 8*(2*T+6*Z+4) + 11*(1+T)
  8 + (10+14*(2*M+1)) + 2*k + init + 2*((W+4)*k) + 4

theorem tail_le (u : Parameters) (first last empty : Bool) {A W : ℕ}
    (hA : u.advice ≤ A) (hW : u.wordWidth ≤ W) :
    groupBound u first last empty ≤ tailMajorant A u.rows u.rowWidth u.radius W := by
  have hpack : u.prefixPackCalls ≤ 1+(A+W)*(W+1) := by
    unfold Parameters.prefixPackCalls
    have hp := Nat.div_le_self (u.advice+u.wordWidth-1) u.wordWidth
    have h := Nat.mul_le_mul (show (u.advice+u.wordWidth-1)/u.wordWidth ≤ A+W by omega)
      (Nat.succ_le_succ hW)
    simp only [Nat.succ_eq_add_one] at h
    omega
  have horder : u.orderPackCalls ≤ 1 + u.rows*(u.rows+1) := by
    unfold Parameters.orderPackCalls
    have hc : Nat.clog 2 u.rows ≤ u.rows := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have h := Nat.mul_le_mul_left u.rows (Nat.succ_le_succ hc)
    simp only [Nat.succ_eq_add_one] at h
    omega
  have hgat : (u.wordWidth+4)*u.configWords ≤ (W+4)*u.configWords :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [Parameters.configWords] at hgat
  cases first <;> cases last <;> cases empty <;>
    simp only [groupBound, tailMajorant, Parameters.lengthPackCalls, Parameters.runtimeBits,
      Parameters.transitionCost, Parameters.configWords, Parameters.exponentBits, Bool.false_eq_true,
      ite_true, ite_false] <;> omega

/-- Polynomially bounded components remain polynomially bounded under the
tail majorant, without a common degree assumption on their five functions. -/
theorem tail_polynomial {A t Z M W : ℕ → ℕ} (hA : PolynomiallyBounded A) (ht : PolynomiallyBounded t)
    (hZ : PolynomiallyBounded Z) (hM : PolynomiallyBounded M) (hW : PolynomiallyBounded W) :
    PolynomiallyBounded (fun n => tailMajorant (A n) (t n) (Z n) (M n) (W n)) := by
  let c := PolynomiallyBounded.const
  have hT := ht.mul hZ
  have hk := ((c 4).mul hM).add (c 3)
  have pack := ((((c 6).mul (hW.add (c 1))).add (c 23)).add
    ((c 11).mul ((c 1).add ((hA.add hW).mul (hW.add (c 1)))))).add
    ((c 6).mul ((c 1).add (ht.mul (ht.add (c 1)))))
  have init := ((((c 4).add pack).add ((c 10).mul ((c 1).add hA))).add
    ((c 8).mul ((((c 2).mul hT).add ((c 6).mul hZ)).add (c 4)))).add ((c 11).mul ((c 1).add hT))
  have tr := (c 10).add ((c 14).mul (((c 2).mul hM).add (c 1)))
  have first := (((c 8).add tr).add ((c 2).mul hk)).add init
  exact (first.add ((c 2).mul ((hW.add (c 4)).mul hk))).add (c 4)

/-- Raw dimensions, independent of the address exponent. -/
def dimensions (n : ℕ) : Geometry := ⟨n,n,n,n⟩

/-- Evaluate the header dimensions at the bounding geometry for input length n to estimate the
outside-stage work. -/
def upperHeader (c : Constants) (n : ℕ) := c.lengths.eval (dimensions n)

private theorem labels_polynomial (c : Constants) :
    PolynomiallyBounded (fun n => c.labels.eval (dimensions n)) := by
  let id := PolynomiallyBounded.id
  let C := PolynomiallyBounded.const
  let state := id.pow (c.circuitExponent+5)
  let pair := (id.mul id).of_le fun n => show n*(n-1)/2 ≤ n*n from
    (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  simp only [Constants.labels, Constants.grammarLabels, Constants.states, eval_add,
    PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
  exact (((state.mul id).mul (C 2)).add (((pair.mul state).mul state).mul state)).add (C c.motifLabels)

private theorem header_polynomial (c : Constants) :
    PolynomiallyBounded (fun n => LiveHeaderSchedule.costBound (upperHeader c n)) := by
  let id := PolynomiallyBounded.id
  let C := PolynomiallyBounded.const
  have h := id.pow c.chainPower
  have z := (C 2).mul h
  have rad := id.pow c.radiusPower
  have k := ((C 1).add (((C 2).mul rad).add (C 1))).add (((C 2).mul rad).add (C 1))
  apply LiveHeaderSchedule.polynomial_cost
  all_goals simp only [upperHeader, Lengths.eval, Constants.lengths, Constants.height, Constants.Z,
    Constants.configWords, Constants.radius, eval_mul, PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
  · exact h.of_le fun n => Nat.sub_le (n^c.chainPower) 1
  · exact id.pow c.deltaPower
  · exact id.pow c.advicePower
  · exact (labels_polynomial c).mul z
  · exact k.mul id

/-- Maximum number of populated words of the auxiliary header. It excludes
both unused tails of the two exterior buffers. -/
def auxWords (s : LiveHeaderSchedule.Sizes) (t : ℕ) :=
  3 + 2*(s.h+2) + s.advice + 2*((s.h+1)*s.delta) + t

/-- Header checks and all non-compression phases of a single live group.
Both route costs may be added when taking the common bound. -/
def majorant (c : Constants) (n : ℕ) :=
  let g := dimensions n
  let t := c.labels.eval g
  let Z := c.Z.eval g
  let s := upperHeader c n
  LiveHeaderSchedule.costBound s + 8 + 4*(t+1) + 100 + 16*(auxWords s t+1) + 7*(t*Z+1) +
    tailMajorant (c.prefixCapacity.eval g) t Z (c.radius.eval g) n

theorem polynomial_majorant (c : Constants) : PolynomiallyBounded (majorant c) := by
  let id := PolynomiallyBounded.id
  let C := PolynomiallyBounded.const
  have hh := (id.pow c.chainPower).of_le fun n => Nat.sub_le (n^c.chainPower) 1
  have hd := id.pow c.deltaPower
  have ha := id.pow c.advicePower
  have t := labels_polynomial c
  have z := (C 2).mul (id.pow c.chainPower)
  have aux := ((((C 3).add ((C 2).mul (hh.add (C 2)))).add ha).add
    ((C 2).mul ((hh.add (C 1)).mul hd))).add t
  have tail := tail_polynomial (id.pow c.prefixPower) t z (id.pow c.radiusPower) id
  have poly := (((((((header_polynomial c).add (C 8)).add ((C 4).mul (t.add (C 1)))).add (C 100)).add
    ((C 16).mul (aux.add (C 1)))).add ((C 7).mul ((t.mul z).add (C 1)))).add tail)
  unfold majorant auxWords
  simpa only [upperHeader, Lengths.eval, Constants.lengths, Constants.height, Constants.Z,
    Constants.configWords, Constants.radius, Constants.prefixCapacity, eval_mul, PublicExpr.eval_natPow,
    PublicExpr.eval, dimensions] using poly

/-- The group budget in the actual word geometry, with its true advice prefix
length and actual selected tail route. Compression is accounted separately. -/
def actualBound (c : Constants) (g : Geometry) (raw : ℕ) (first last empty : Bool) :=
  let s := c.lengths.eval g
  let t := c.labels.eval g
  let Z := c.Z.eval g
  LiveHeaderSchedule.costBound s + 8 + 4*(t+1) + 100 + 16*(auxWords s t+1) + 7*(t*Z+1) +
    groupBound ⟨raw,t,Z,c.radius.eval g,g.w⟩ first last empty

private theorem labels_eq (c : Constants) (g : Geometry) :
    c.labels.eval g = c.labels.eval (dimensions g.n) := by
  simp only [Constants.labels, eval_add, Constants.grammarLabels_eq, PublicExpr.eval, dimensions]

theorem actual_le (c : Constants) (g : Geometry) (raw : ℕ) (first last empty : Bool)
    (hw : g.w ≤ g.n) (hraw : raw ≤ c.prefixCapacity.eval g) :
    actualBound c g raw first last empty ≤ majorant c g.n := by
  have htail := tail_le (⟨raw,c.labels.eval g,c.Z.eval g,c.radius.eval g,g.w⟩ : Parameters)
    first last empty hraw hw
  dsimp only at htail
  have hl := labels_eq c g
  have hs : LiveHeaderSchedule.costBound (c.lengths.eval g) ≤
      LiveHeaderSchedule.costBound (upperHeader c g.n) := by
    simp only [upperHeader, Lengths.eval, Constants.lengths, Constants.height, Constants.Z, Constants.configWords,
      Constants.radius, eval_mul, PublicExpr.eval_natPow, PublicExpr.eval, dimensions,
      LiveHeaderSchedule.costBound, LiveHeaderSchedule.callBound]
    rw [hl]
    gcongr
    exact le_rfl
  have haux : auxWords (c.lengths.eval g) (c.labels.eval g) =
      auxWords (upperHeader c g.n) (c.labels.eval (dimensions g.n)) := by
    simp only [auxWords, upperHeader, Lengths.eval, Constants.lengths, Constants.height,
      PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
    rw [hl]
    rfl
  unfold actualBound majorant
  dsimp only
  have hz : c.Z.eval g = c.Z.eval (dimensions g.n) := by
    simp only [Constants.Z, Constants.height, eval_mul, PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
  have hr : c.radius.eval g = c.radius.eval (dimensions g.n) := by
    simp only [Constants.radius, PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
  have hp : c.prefixCapacity.eval g = c.prefixCapacity.eval (dimensions g.n) := by
    simp only [Constants.prefixCapacity, PublicExpr.eval_natPow, PublicExpr.eval, dimensions]
  rw [hl, hz, hr, hp] at htail
  rw [haux, hl, hz, hr]
  omega

private theorem pow_le_R (B n : ℕ) : n^B ≤ processorCount B n := by
  calc
    _ ≤ (2^Nat.clog 2 n)^B := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) B
    _ = _ := by rw [← pow_mul, Nat.mul_comm]; rfl

/-- The choice of B precedes the eventual threshold and applies uniformly
to the physical word widths and all bounded group inputs. -/
theorem eventually_budget (c : Constants) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop,
      majorant c n < processorCount B n ∧ CursorBounds.wordBits B n ≤ n := by
  obtain ⟨A,d,N,hm⟩ := polynomial_majorant c
  refine ⟨d+1, fun B hB => ?_⟩
  filter_upwards [eventually_ge_atTop (max N (A+1)), BurstRAM.eventually_word_stage_le B 0] with n hn hw
  have hN := (le_max_left N (A+1)).trans hn
  have hA := (le_max_right N (A+1)).trans hn
  have hn0 : 0 < n := by omega
  have hmod : CursorBounds.wordBits B n ≤ n :=
    (hw _ 0 (Nat.mul_le_mul_left B (BurstRAM.clog_le_log2_succ n)) (by simp)).1
  refine ⟨(hm n hN).trans_lt ?_, hmod⟩
  calc
    A*n^d < n*n^d := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos hn0)
    _ = n^(d+1) := (pow_succ' ..).symm
    _ ≤ n^B := Nat.pow_le_pow_right hn0 hB
    _ ≤ processorCount B n := pow_le_R B n

/-- One eventual threshold works for every physical group, every eligible
advice string and every choice of the tail route. -/
theorem eventually_actual (c : Constants) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ∀ᶠ n : ℕ in atTop, ∀ (H raw : ℕ) (first last empty : Bool),
      let g := paperGeometry B (fun _ => H) n
      raw ≤ c.prefixCapacity.eval g → actualBound c g raw first last empty < processorCount B n := by
  obtain ⟨B₀, h⟩ := eventually_budget c
  refine ⟨B₀, fun B hB => ?_⟩
  filter_upwards [h B hB] with n hn
  intro H raw first last empty
  dsimp only
  intro hr
  exact (actual_le c (paperGeometry B (fun _ => H) n) raw first last empty hn.2 hr).trans_lt hn.1

end LiveProgram.OutsideBudget

end VPVNP
end Computability
end OAI
