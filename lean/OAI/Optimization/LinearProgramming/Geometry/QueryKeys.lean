import OAI.Optimization.LinearProgramming.Geometry.Query
import OAI.Optimization.LinearProgramming.Geometry.CanonicalMinorQuery

/-! Route the requests of the geometric label routine to canonical nonzero minors. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix

namespace MinorQuery
variable {κ ι α : Type*}

/-- Route a key to the minor service. Invalid or zero minors are assigned zero
without issuing a request. The pivot routine itself only requests nonzero minors. -/
def rekey (index : κ → Option ι) : MinorQuery κ α → MinorQuery ι α
  | .done a => .done a
  | .query k next =>
    match index k with
    | none => rekey index (next 0)
    | some u => .query u (fun q => rekey index (next q))

theorem eval_rekey (index : κ → Option ι) (f : ι → ℚ) (p : MinorQuery κ α) :
    eval f (rekey index p) = eval (fun k => (index k).elim 0 f) p := by
  induction p with
  | done => rfl
  | query k next ih =>
    cases hk : index k with
    | none => simpa only [rekey, hk, eval, Option.elim_none] using ih 0
    | some u => simpa only [rekey, hk, eval, Option.elim_some] using ih (f u)

theorem bounded_rekey (index : κ → Option ι) (p : MinorQuery κ α) {b : ℕ}
    (h : Bounded p b) : Bounded (rekey index p) b := by
  induction b generalizing p with
  | zero => cases p <;> simp_all [Bounded, rekey]
  | succ b ih =>
    cases p with
    | done => exact True.intro
    | query k next =>
      cases hk : index k with
      | none =>
        simp only [rekey, hk]
        exact bounded_mono (ih _ (h 0)) (by omega)
      | some u =>
        simp only [rekey, hk, Bounded]
        exact fun q => ih _ (h q)
end MinorQuery

variable {r s n : ℕ}

/-- The checked lower-level decoder for the original prefix minor. -/
abbrev checkedPrimalMinor (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (key : PivotKey n) : Option (Compression.NonzeroPairMinor D E) :=
  Canonical.checkedPrimalMinor D E key

theorem checkedPrimalMinor_value (D : Matrix (Fin r) (Fin n) ℚ)
    (E : Matrix (Fin s) (Fin n) ℚ) (f : Compression.NonzeroPairMinor D E → ℚ) (key : PivotKey n) :
    (checkedPrimalMinor D E key).elim 0 f = prefixAssignment D E f key :=
  Canonical.checkedPrimalMinor_value D E f key

/-- Proposition 2.1's designated-query algorithm using only requests for actual
nonzero minors of the input pair, including early aborts and rank zero. -/
def geometricLabel (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (t : Fin n → ℚ) (i : Fin n) : MinorQuery (Compression.NonzeroPairMinor D E) Bool :=
  MinorQuery.rekey (checkedPrimalMinor D E) (geometricMinorLabel D t i)

theorem geometricLabel_eval (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (f : Compression.NonzeroPairMinor D E → ℚ) (t : Fin n → ℚ) (i : Fin n) :
    MinorQuery.eval f (geometricLabel D E t i) =
      MinorQuery.eval (prefixAssignment D E f) (geometricMinorLabel D t i) := by
  simp only [geometricLabel, MinorQuery.eval_rekey, checkedPrimalMinor_value]

theorem geometricLabel_bounded (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (t : Fin n → ℚ) (i : Fin n) : (geometricLabel D E t i).Bounded (r*n) :=
  MinorQuery.bounded_rekey _ _ (geometricMinorLabel_bounded ..)

theorem geometricLabel_run_length (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (t : Fin n → ℚ) (i : Fin n) {log out} (hrun : MinorQuery.Run (geometricLabel D E t i) log out) :
    log.length + MinorQuery.restartCost out ≤ r*n := hrun.call_bound (geometricLabel_bounded ..)

end Geometry
end LinearProgramming
end Optimization
end OAI
