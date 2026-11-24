import OAI.Computability.VPVNP.MacaulayReaderWidth

/-! # Uniform budgets for both physical scans and all target operations -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.ReaderPlan

open PolynomiallyBounded RankQuery.Stack

/-- The two largest advised degrees, irrespective of the selected row or field. -/
def envelope (P : ReaderPlan) : PairCall.Inputs :=
  ⟨P.arity,fun b => if b then P.column else P.source,fun _ => 0,P.scale,P.arity⟩

/-- A common tick bound for both monomial scans. It includes ordinal decoding, residual packing
or powered comparison, and cleanup. -/
def scanTime (P : ReaderPlan) (w B : ℕ) :=
  (PairCall.scanClock w B P.envelope + PairCall.packClock P.arity w B + PairCall.clearCost w) +
    (PairCall.scanClock w B P.envelope + PairCall.powerClock P.arity w B + PairCall.clearCost w)

/-- A common bound on stack lengths for an equation scan and a powered-row scan at the plan's
maximum degrees. -/
def scanSpace (P : ReaderPlan) (w B : ℕ) :=
  PairCall.equationSpace w B P.envelope + PairCall.poweredSpace w B

private theorem ordinal_mono (w B t : ℕ) {a b : ℕ} (h : a ≤ b) :
    PairCall.ordinalClock w B t a ≤ PairCall.ordinalClock w B t b := by
  unfold PairCall.ordinalClock
  gcongr
  exact raw_mono t h

/-- Applies to an equation or pin multiplier, an appended monomial and
either a label multiplication or a Frobenius target row. -/
theorem scan_bounds (P : ReaderPlan) (w B : ℕ) (d : PairCall.Inputs)
    (ht : d.arity=P.arity) (hL : d.degree false ≤ P.source) (hD : d.degree true ≤ P.column) :
    (PairCall.scanClock w B d + PairCall.packClock d.arity w B + PairCall.clearCost w ≤ P.scanTime w B) ∧
    (PairCall.scanClock w B d + PairCall.powerClock d.arity w B + PairCall.clearCost w ≤ P.scanTime w B) ∧
    PairCall.equationSpace w B d ≤ P.scanSpace w B ∧ PairCall.poweredSpace w B ≤ P.scanSpace w B := by
  have hc : PairCall.scanClock w B d ≤ PairCall.scanClock w B P.envelope := by
    unfold PairCall.scanClock
    rw [ht]
    exact Nat.add_le_add (ordinal_mono w B P.arity hL) (ordinal_mono w B P.arity hD)
  have he : PairCall.equationSpace w B d = PairCall.equationSpace w B P.envelope := by
    simp [PairCall.equationSpace, envelope, ht]
  rw [ht,he]
  unfold scanTime scanSpace
  omega

theorem resources (P : ℕ → ReaderPlan) {w B : ℕ → ℕ} (hw : PolynomiallyBounded w) (hB : PolynomiallyBounded B)
    (ht : PolynomiallyBounded (fun n => (P n).arity)) (hd : PolynomiallyBounded (fun n => Nat.clog 2 (P n).degree))
    (hn : PolynomiallyBounded (fun n => Nat.clog 2 (P n).points))
    (hq : PolynomiallyBounded (fun n => Nat.clog 2 (P n).order)) :
    PolynomiallyBounded (fun n => (P n).scanSpace (w n) (B n)) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 ((P n).scanTime (w n) (B n))) ∧
    PolynomiallyBounded (fun n => MacaulayRowDispatch.ticks (w n)) := by
  obtain ⟨_,hD,hL,_⟩ := degree_bounds P ht hd hn hq
  obtain ⟨hs,hp,he,hq⟩ := PairCall.resources (fun n => (P n).envelope) hw hB ht (fun b => by
    cases b <;> first | exact hD | exact hL)
  exact ⟨hs.add hp,clog_add he hq,(PolynomiallyBounded.const _).mul
    ((PolynomiallyBounded.const 100).mul ((hw.add (PolynomiallyBounded.const 1)).pow 2))⟩

end RadicalCertificate.MonomialIndex.ReaderPlan

end VPVNP
end Computability
end OAI
