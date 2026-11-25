import OAI.Computability.BorderVNP.ParseBatchChildren
import OAI.Computability.BorderVNP.ParseBatchVerifierTreesPadding

/-!
# The Boolean verifier for all guessed preorder trees in Lemma 2.3

For arbitrary assignments to the raw ports, the circuit accepts precisely the
tuple of parses of the queried monomials. The preparation and sorting circuits
use no auxiliary private guesses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchTrees

open VPVNP VPVNP.VerifierNetwork BorderVNP.ParseRecords BorderVNP.ParseBatchChildren

variable {m g n r : ℕ}

/-- Concrete one-tree verifier, including all format, interval, root, child and leaf
checks. -/
noncomputable def treeFrame (m : ℕ) (d : Fin n) (h : Fin g) : Frame (TreePins m g n d) Unit :=
  checkTree d (childFrame m d h)

/-- Acceptance of a guessed tree block has exactly the manuscript's intended
parse and leaf multiplicities. -/
theorem treeFrame_eval (d : Fin n) (h : Fin g) (hm : m = d.val+1) (x : Fin m → Bool)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    (treeFrame m d h).eval (Sum.elim x (fun ij => bs ij.1 ij.2)) () = true ↔ CheckedBits d h x bs :=
  checkTree_eval d h hm _ (childFrame_eval d h) x bs

/-- The complete, unconditional batched tree-verification circuit. The external query
ports and raw record guesses are its only inputs. The gate bound is linear in the
number of query bits times a cubic logarithm. -/
theorem exists_acceptFrame (d : Fin n) (h : Fin g) (hm : m = d.val+1) (hr : 0 < r)
    (hw : max m (max g n)+1 ≤ 2*m*r) :
    ∃ f : Frame (BatchPins m g n r d) Unit,
      f.size ≤ 1000607*(m*r)*(Nat.clog 2 (2*m*r)+3)^3 ∧
      ∀ x bs, f.eval (batchInput d x bs) () = true ↔ ParseBatch.Accepted d h x bs := by
  let J := 2*d.val+1
  let a := workingWidth m g n
  let b := TwoReads.sortBits J
  have hc : (childFrame m d h).size ≤ 10000 * childWork J a b :=
    (childFrame_size m d h).trans (child_layout_le J a b)
  have hcap : (childFrame m d h).size ≤ 1000000*m*(Nat.clog 2 (2*m*r)+3)^3 :=
    hc.trans ((Nat.mul_le_mul_left 10000 (childWork_le d hm hr hw)).trans_eq (by ring))
  exact exists_acceptFrame_of_shape d h hm hr hw _ (childFrame_eval d h) 1000000 3 hcap

end ParseBatchTrees

end BorderVNP
end Computability
end OAI
