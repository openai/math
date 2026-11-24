import OAI.Computability.VPVNP.MacaulayPairBounds
import OAI.Computability.VPVNP.MacaulayPairEntries
import OAI.Computability.VPVNP.MacaulayRowDispatch

/-! # A common word width for the physical matrix readers

The input row counts include both original equations and pins. The field
size can be bounded before the prime is chosen. The same width covers all
legal rows and columns, label shifts and Frobenius target comparisons.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open PolynomiallyBounded
open RankQuery.Stack

/-- Counts and upper bounds used to choose a single word width for Macaulay reads across the
allowed fields, rows and target operations. -/
structure ReaderPlan where
  /-- Number of variables in the slice equations and their monomials. -/
  arity : ℕ
  /-- Number of original equations before the affine pin rows. -/
  equations : ℕ
  /-- Number of affine pin equations added to form the slice. -/
  pins : ℕ
  /-- Upper bound supplied for the degrees of the defining equations. -/
  degree : ℕ
  /-- Upper bound supplied for the number of geometric points in the slice. -/
  points : ℕ
  /-- Upper bound on the cardinality of the finite ground field. -/
  order : ℕ

namespace ReaderPlan

/-- Degree bound for target monomials obtained by multiplying by a variable or applying
Frobenius. -/
def target (P : ReaderPlan) := (P.points+1)*P.order
/-- Uniform effective Nullstellensatz degree bound using the plan's equation and target
degrees. -/
def certificate (P : ReaderPlan) := (2*max P.degree (P.target+1))^(4*(P.arity+3))
/-- Upper bound on the Frobenius power used in radical membership queries. Its exponent is the
ceiling binary logarithm of the certificate bound. -/
def power (P : ReaderPlan) := P.order^(Nat.clog 2 P.certificate)
/-- Degree allowance for monomials multiplying the equations, including the powered target
degree. -/
def multiplier (P : ReaderPlan) := P.certificate + P.power*P.target
/-- Degree allowance for the coefficient columns of all products of a multiplier with a
defining equation. -/
def column (P : ReaderPlan) := P.multiplier + P.degree
/-- Common degree bound for source monomials in both equation multiples and the appended
monomial rows. -/
def source (P : ReaderPlan) := max P.points P.multiplier
/-- Common upper bound on exponent scaling for ordinary, powered and Frobenius-target reads. -/
def scale (P : ReaderPlan) := max 1 (P.power*P.order)
/-- Word width sufficient for the pair scan using the plan's largest source degree, column
degree, scale and marked coordinate. -/
def pairWidth (P : ReaderPlan) := ExponentISA.entryWidth P.arity P.source P.column P.scale P.arity 0

/-- The dimensions can be bounded by the raw address ranges even though
the physical caller uses dense ordinals. -/
def addressLimit (P : ReaderPlan) :=
  (P.equations+P.pins)*rawSize P.arity P.multiplier + rawSize P.arity P.points +
    rawSize P.arity P.column + P.equations + P.pins + rawSize P.arity P.multiplier + 1

/-- Bit width obtained by taking the ceiling binary logarithm of the plan's address limit. -/
def addressBits (P : ReaderPlan) := Nat.clog 2 P.addressLimit

/-- Common register width covering the input addresses, the row decoder's intermediate values
and the exponent scan. -/
def wordWidth (P : ReaderPlan) :=
  2 + P.addressBits + MacaulayRowDispatch.requiredWidth P.addressBits + P.pairWidth

variable {K : Type*}

/-- The slice query has field order at least two and fits the plan's bounds on field order,
equation degree and number of points. -/
structure Covers (P : ReaderPlan) (S : QueryData P.arity (P.equations+P.pins) K) : Prop where
  order_two : 2 ≤ S.fieldOrder
  order_le : S.fieldOrder ≤ P.order
  degree_le : S.degreeBound ≤ P.degree
  points_le : S.pointBound ≤ P.points

theorem Covers.degrees {P : ReaderPlan} {S : QueryData P.arity (P.equations+P.pins) K} (h : P.Covers S) :
    S.power ≤ P.power ∧ S.multiplierDegree ≤ P.multiplier ∧ S.columnDegree ≤ P.column := by
  have hR : S.targetDegree ≤ P.target := Nat.mul_le_mul (Nat.add_le_add_right h.points_le 1) h.order_le
  have hH : S.certificateDegree ≤ P.certificate :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (max_le_max h.degree_le (Nat.add_le_add_right hR 1))) _
  have hP : S.power ≤ P.power :=
    (Nat.pow_le_pow_left h.order_le _).trans (Nat.pow_le_pow_right ((by decide : 0 < 2).trans_le (h.order_two.trans h.order_le))
      ((Nat.clog_anti_left (by decide) h.order_two).trans (Nat.clog_mono_right _ hH)))
  have hL : S.multiplierDegree ≤ P.multiplier := Nat.add_le_add hH (Nat.mul_le_mul hP hR)
  exact ⟨hP,hL,Nat.add_le_add hL h.degree_le⟩

theorem raw_mono (t : ℕ) {a b : ℕ} (h : a ≤ b) : rawSize t a ≤ rawSize t b :=
  Nat.mul_le_mul (Nat.succ_le_succ h) (Nat.pow_le_pow_left (Nat.succ_le_succ h) t)

private theorem size_le_raw_of_le (t : ℕ) {a b : ℕ} (h : a ≤ b) : size t a ≤ rawSize t b := by
  rw [size_eq_card]
  exact (card_boundedMonomial_le t a).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (raw_mono t h))

theorem Covers.dispatch {P : ReaderPlan} {S : QueryData P.arity (P.equations+P.pins) K} (h : P.Covers S)
    (i : Fin ((P.equations+P.pins)*size P.arity S.multiplierDegree + size P.arity S.pointBound))
    (j : Fin (size P.arity S.columnDegree)) (a : Fin 8) :
    MacaulayRowDispatch.inputs i j P.equations P.pins (size P.arity S.multiplierDegree) a < 2^P.addressBits := by
  have hm := size_le_raw_of_le P.arity h.degrees.2.1
  have hc := size_le_raw_of_le P.arity h.degrees.2.2
  have hn := size_le_raw_of_le P.arity h.points_le
  have hi := i.isLt.trans_le (Nat.add_le_add (Nat.mul_le_mul_left _ hm) hn)
  have hj := j.isLt.trans_le hc
  apply Nat.lt_of_lt_of_le _ (Nat.le_pow_clog (by decide : 1<2) P.addressLimit)
  fin_cases a <;> simp [MacaulayRowDispatch.inputs, addressLimit] <;> omega

theorem dispatchWidth (P : ReaderPlan) :
    MacaulayRowDispatch.requiredWidth P.addressBits ≤ P.wordWidth ∧ P.addressBits ≤ P.wordWidth ∧ 2 ≤ P.wordWidth := by
  dsimp [wordWidth]; omega

private theorem pairWidth_mono {t L L' D D' s s' m m' : ℕ} (hl : L ≤ L') (hd : D ≤ D')
    (hs : s ≤ s') (hm : m ≤ m') :
    ExponentISA.entryWidth t L D s m 0 ≤ ExponentISA.entryWidth t L' D' s' m' 0 := by
  apply Nat.add_le_add_left
  apply Nat.clog_mono_right
  have r₁ := raw_mono t hl
  have r₂ := raw_mono t hd
  have l₁ := Nat.mul_le_mul_left t hl
  have l₂ := Nat.mul_le_mul_left t hd
  have l₃ := Nat.mul_le_mul hs (Nat.add_le_add_right hl 1)
  omega

theorem pairWidth_le (P : ReaderPlan) (d : PairCall.Inputs) (ht : d.arity = P.arity)
    (hl : d.degree false ≤ P.source) (hd : d.degree true ≤ P.column) (hs : d.scale ≤ P.scale)
    (hm : d.mark ≤ P.arity) : PairCall.requiredWidth d ≤ P.wordWidth := by
  have h : PairCall.requiredWidth d ≤ P.pairWidth := by
    unfold PairCall.requiredWidth pairWidth
    rw [ht]
    exact pairWidth_mono hl hd hs hm
  dsimp only [wordWidth]; omega

theorem Covers.targetParams {P : ReaderPlan} {S : QueryData P.arity (P.equations+P.pins) K}
    (h : P.Covers S) (op : QueryData.Operation P.arity) :
    PairCall.targetScale S op ≤ P.scale ∧ PairCall.targetMark op ≤ P.arity := by
  have hp := h.degrees.1
  have hq := h.order_le
  have hpos := h.order_two
  have hm := Nat.mul_le_mul hp hq
  have hs : S.power ≤ S.power*S.fieldOrder := Nat.le_mul_of_pos_right _ (by omega)
  cases op with
  | label i => exact ⟨(hs.trans hm).trans (le_max_right ..), i.isLt⟩
  | frobenius => exact ⟨hm.trans (le_max_right ..), Nat.zero_le _⟩

private theorem polyClogMax {f g : ℕ → ℕ} (hf : PolynomiallyBounded (fun n => Nat.clog 2 (f n)))
    (hg : PolynomiallyBounded (fun n => Nat.clog 2 (g n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (max (f n) (g n))) :=
  (clog_add hf hg).of_le fun _ => Nat.clog_mono_right _ (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

theorem degree_bounds (P : ℕ → ReaderPlan) (ht : PolynomiallyBounded (fun n => (P n).arity))
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (P n).degree))
    (hn : PolynomiallyBounded (fun n => Nat.clog 2 (P n).points))
    (hq : PolynomiallyBounded (fun n => Nat.clog 2 (P n).order)) :
    PolynomiallyBounded (fun n => Nat.clog 2 (P n).multiplier) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (P n).column) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (P n).source) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (P n).scale) := by
  have h1 := clog (PolynomiallyBounded.const 1)
  have hR := clog_mul (clog_add hn h1) hq
  have hH := clog_pow (clog_mul (clog (PolynomiallyBounded.const 2)) (polyClogMax hd (clog_add hR h1)))
    ((PolynomiallyBounded.const 4).mul (ht.add (PolynomiallyBounded.const 3)))
  have hP := clog_pow hq hH
  have hL := clog_add hH (clog_mul hP hR)
  have hD := clog_add hL hd
  have hsource := polyClogMax hn hL
  have hscale := polyClogMax h1 (clog_mul hP hq)
  exact ⟨hL,hD,hsource,hscale⟩

/-- The physical word width is bounded independently of the varying row
and column ordinals and the operation being queried. -/
theorem width_polynomial (P : ℕ → ReaderPlan) (ht : PolynomiallyBounded (fun n => (P n).arity))
    (he : PolynomiallyBounded (fun n => Nat.clog 2 (P n).equations))
    (hi : PolynomiallyBounded (fun n => Nat.clog 2 (P n).pins))
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (P n).degree))
    (hn : PolynomiallyBounded (fun n => Nat.clog 2 (P n).points))
    (hq : PolynomiallyBounded (fun n => Nat.clog 2 (P n).order)) :
    PolynomiallyBounded (fun n => (P n).wordWidth) := by
  have h1 := clog (PolynomiallyBounded.const 1)
  obtain ⟨hL,hD,hsource,hscale⟩ := degree_bounds P ht hd hn hq
  have hp : PolynomiallyBounded (fun n => (P n).pairWidth) :=
    ExponentISA.entryWidth_polynomial ht hsource hD hscale (clog ht) (clog (PolynomiallyBounded.const 0))
  have hl := bounded_rawSize ht hL
  have hbits : PolynomiallyBounded (fun n => (P n).addressBits) :=
    clog_add (clog_add (clog_add (clog_add (clog_add (clog_add (clog_mul (clog_add he hi) hl)
      (bounded_rawSize ht hn)) (bounded_rawSize ht hD)) he) hi) hl) h1
  exact (((PolynomiallyBounded.const 2).add hbits).add
    ((hbits.add (PolynomiallyBounded.const 1)).mul (PolynomiallyBounded.const _))).add hp

end ReaderPlan
end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
