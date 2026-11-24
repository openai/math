import OAI.Computability.VPVNP.LiveEvaluatorGroup
import OAI.Computability.VPVNP.LiveEvaluatorRAMSegment
import OAI.Computability.VPVNP.LiveGroupContraction

/-!
# Path counts of the literal scheduled tail-group program

A complete native RAM segment includes the preparing call, each cell call
on both tapes, and the final acceptance of the cursor. Its accepting paths
on the two decoded cut configurations have exactly the local multiplicity
used in the live chain contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory ActualPaths)
open UniversalMachine (Program)
open LiveEvaluatorEncoding (Code)
open LiveEvaluatorRAM (ConfigAt PrepLayout)
open LiveEvaluatorRAM.Schedule (Pub nativeProgram callFuel actualPathEquiv)
open LiveEvaluatorStep (nextCode)
open scoped Classical

variable {M w : ℕ} {p : Program} {pub : Pub → Word w} {m : Memory w} {old out : Code p.extra M}

/-- Every successful native RAM path has one semantic branch choice and
conversely. Deterministic calls use the empty choice stream. -/
noncomputable def nativeGroupEquiv (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True) ≃
      {bit : Bool // nextCode p old bit = some out ∧ out ≠ .rejected} :=
  (actualPathEquiv p pub m hl.radius (calls_fit hl).le).trans (streamEquiv hl ho hz).symm

theorem card_nativeGroup (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    Nat.card (ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True)) =
      ∑ bit : Bool, if nextCode p old bit = some out ∧ out ≠ .rejected then 1 else 0 := by
  rw [Nat.card_congr (nativeGroupEquiv hl ho hz), Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.sum_boole]
  simp

/-- For any two successfully decoded boundaries of a tail group, its factor
in the contraction is the number of accepted segments of the compiled table. -/
theorem tailCount_eq_native {h Δ : ℕ} (layout : LiveEvaluatorTail.Layout p.extra M w Δ)
    (init : Code p.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2 ^ h))
    (ha : LiveEvaluatorTail.boundary layout init bits i.castSucc = some old)
    (hb : LiveEvaluatorTail.boundary layout init bits i.succ = some out)
    (hl : PrepLayout p pub M) (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    ChainAssignments.tailCount p layout init bits i =
      Nat.card (ActualPaths (nativeProgram p pub) (callFuel p) 0 m (fun _ => True)) := by
  rw [card_nativeGroup hl ho hz]
  simp [ChainAssignments.tailCount, ha, hb]

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
