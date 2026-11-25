import OAI.Hierarchy.ProtocolRAMCalendarStripPublicROM

namespace OAI
/-! # One physical endpoint for the score, port and chronological scalar-price header -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripDirectory
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

def priceTable (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh)
    (finish : ℝ) (price : PhasePrice) :=
  let ports := portTable s (JointHeader.stop b z N k (DeadlineROM.count c))
  DeadlineROM.table c finish price ports.stop (GlobalTests.kinds N k) (b.cap*b.width+1)

def headerFactor (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh) : ℕ :=
  JointHeader.coefficient N k (DeadlineROM.count c) b.steps+
  (12*((PurchaseFrozen.count z d k*s.sampler.degree^depth)*D)+8)+
  DeadlineROM.count c*(2*(GlobalTests.kinds N k+1))

theorem header_bound (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh)
    (finish : ℝ) (price : PhasePrice) (width : b.cap*b.width+1≤2^z) :
    (priceTable s b c finish price).stop≤b.initial+headerFactor s b c*2^z := by
  let n := DeadlineROM.count c
  let scores := JointHeader.stop b z N k n
  let ports := portTable s scores
  let prices := priceTable s b c finish price
  have high := JointHeader.stop_linear b z N k n width
  have port := portTable_linear s scores
  have stride : prices.stride=b.cap*b.width+1 := rfl
  have low := prices.size_le z 1 (by rw [stride,one_mul]; exact width)
  change scores≤b.initial+JointHeader.coefficient N k n b.steps*2^z at high
  change ports.stop≤ scores+(12*((PurchaseFrozen.count z d k*s.sampler.degree^depth)*D)+8)*2^z at port
  change prices.stop≤ports.stop+(n*(2*((GlobalTests.kinds N k)*1+1)))*2^z at low
  simp only [Nat.mul_one] at low
  change prices.stop≤b.initial+(JointHeader.coefficient N k n b.steps+
    (12*((PurchaseFrozen.count z d k*s.sampler.degree^depth)*D)+8)+n*(2*(GlobalTests.kinds N k+1)))*2^z
  rw [Nat.add_mul,Nat.add_mul]
  omega

/-- The full high slab can start above an already-mounted core catalogue. -/
theorem header_word_room (s : Boards z d k q depth) (b : JointHeader.Board) (c : Mesh)
    (finish : ℝ) (price : PhasePrice) (core : ℕ) (width : b.cap*b.width+1≤2^z)
    (initial : b.initial≤heapEnd z d copies+core*2^z)
    (sufficient : core+headerFactor s b c+1≤2^z) :
    (priceTable s b c finish price).stop<2^(wordBits z d copies) := by
  apply (header_bound s b c finish price width).trans_lt
  apply lt_of_le_of_lt _ (append_room sufficient)
  rw [Nat.add_mul]
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
