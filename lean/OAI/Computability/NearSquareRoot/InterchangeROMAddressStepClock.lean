import OAI.Computability.NearSquareRoot.InterchangeROMAddressStep
import OAI.Computability.NearSquareRoot.InterchangeROMAddressMajorant

/-! # A common, frozen local price for mixed address programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication.Code InterchangeROMAddress

def Clocks.maxCoefficient (c : Clocks) := max c.width.coefficient c.gather.coefficient
def Clocks.maxScale (c : Clocks) := max c.width.scale c.gather.scale
def Clocks.maxDegree (c : Clocks) := max (max c.width.degree c.gather.degree) c.pivotDegree

/-- A larger common exponent can also pay for the header saved by the enclosing word. -/
theorem cost_le_perOp_of_degree (c : Clocks) {j : ℕ} (hj : c.maxDegree ≤ j)
    (b n : ℕ) (o : Opcode.Op) (h : Header) (N : ℕ) (src dst : Tree) :
    cost c b n o h N src dst ≤
      perOp c.maxCoefficient c.maxScale c.pivotSize j b n o * geometry j h N src dst := by
  unfold cost
  split
  · exact scan_le_perOp (le_max_left ..) (le_max_left ..)
      (((le_max_left ..).trans (le_max_left ..)).trans hj) b n false o h N src dst
  split
  · exact scan_le_perOp (le_max_right ..) (le_max_right ..)
      (((le_max_right ..).trans (le_max_left ..)).trans hj) b n true o h N src dst
  · exact pivot_le_perOp le_rfl ((le_max_right ..).trans hj) b n o h N src dst

theorem cost_le_perOp (c : Clocks) (b n : ℕ) (o : Opcode.Op) (h : Header)
    (N : ℕ) (src dst : Tree) :
    cost c b n o h N src dst ≤ perOp c.maxCoefficient c.maxScale c.pivotSize c.maxDegree b n o *
      geometry c.maxDegree h N src dst :=
  cost_le_perOp_of_degree c le_rfl b n o h N src dst

/-- Sum the actual local clocks with distinct input and output streams at
every position. A word can visit the same opcode more than once. -/
theorem mixed_cost_sum (c : Clocks) {j : ℕ} (hj : c.maxDegree ≤ j) (b n : ℕ)
    (h : Header) (N G : ℕ) (trace : List (Opcode.Op × Tree × Tree))
    (hg : ∀ p ∈ trace, geometry j h N p.2.1 p.2.2 ≤ G) :
    (trace.map (fun p => cost c b n p.1 h N p.2.1 p.2.2)).sum ≤
      perWord c.maxCoefficient c.maxScale c.pivotSize j b n (trace.map Prod.fst) * G := by
  apply word_le_of_forall₂
  induction trace with
  | nil => exact .nil
  | cons a tail ih =>
    exact .cons ((cost_le_perOp_of_degree c hj b n a.1 h N a.2.1 a.2.2).trans
      (Nat.mul_le_mul_left _ (hg a List.mem_cons_self)))
      (ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)))

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
