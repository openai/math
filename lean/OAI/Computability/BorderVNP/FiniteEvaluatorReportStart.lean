import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse

/-! # Public input of the finite field report program

The input records the six-word owned-cell headers, the locations and sizes of
the output arrays, and the separation needed to read all headers in order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA

/-- The initial words and address bounds read by the scalar report preparer. -/
structure Start {w : ℕ} (pub : Arg → Word w) (m : Memory w) (l : Layout) (rows : List Row) : Prop where
  ptr : (pub 0).val = l.frame
  seed : l.Seed rows.length (readings m)
  frame : l.frame+92 < 2^w
  control : l.control+27 < 2^w
  endHeaders : l.headers+6*rows.length < 2^w
  headers : ∀ i : Fin rows.length, rows[i].Stored (l.headers+6*i.val) (readings m)
  rooms : ∀ i : Fin rows.length, rows[i].Fits l w (l.headers+6*i.val)
  apart : ∀ i j : Fin rows.length, i < j → ∀ k : Fin 3, rows[i].Outside l (l.headers+6*j.val+k.val)

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
