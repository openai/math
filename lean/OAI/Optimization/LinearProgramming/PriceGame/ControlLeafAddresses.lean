import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdRanges

/-! The terminal row needs at most `2N²` addresses, even if the binary level
parameter is inconsistent with the trial. Generate that range in unary and
test a candidate by shifting its binary address back to depth zero. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def leafAddresses (N l : ℕ) : List ℕ := List.range (min (2*(N*N)) (N*2^l))

theorem leafAddresses_eq {N l : ℕ} (h : l ≤ States.Mass.depth N) :
    leafAddresses N l = List.range (N*2^l) := by
  by_cases hN : N = 0
  · simp [leafAddresses,hN]
  · have fit := States.Mass.card_vertices_le N l (Nat.pos_of_ne_zero hN) h
    have bound : N*2^l ≤ 2*(N*N) := by
      simpa only [States.Mass.card_vertices,pow_two,Nat.mul_comm N (2^l)] using fit
    rw [leafAddresses,Nat.min_eq_right bound]

/-- A uniform finite bit program, with polynomial cost in the unary dimension
and the actual bit length of the level. In particular no machine loop runs
for `2 ^ l` steps when `l` lies outside the source recursion. -/
noncomputable def leafAddressesP :
    Procedure (prodCode unaryCode Nat.bits) (listCode Nat.bits)
      (fun x : ℕ × ℕ => leafAddresses x.1 x.2) := by
  let inp := prodCode unaryCode Nat.bits
  let dim := first unaryCode Nat.bits
  let level := second unaryCode Nat.bits
  let sq := unaryMul.comp (dim.pair dim)
  let bound := unaryMul.comp ((constant inp unaryCode 2).pair sq)
  let addresses := addressRangeP.comp bound
  let ctx := prodCode Nat.bits Nat.bits
  let publicData := first ctx Nat.bits
  let address := second ctx Nat.bits
  let n := (first Nat.bits Nat.bits).comp publicData
  let k := (second Nat.bits Nat.bits).comp publicData
  let test := binaryLt.comp ((Learning.BitMachine.rootAddressP.comp (address.pair k)).pair n)
  let valid := Learning.BitMachine.filterWithP 0 test
  apply (valid.comp (addresses.pair ((unaryToBits.comp dim).pair level))).congrFun
  rintro ⟨N,l⟩
  change (List.range (2*(N*N))).filter (fun i => decide ((i >>> l) < N)) = leafAddresses N l
  simpa only [leafAddresses,Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (by positivity : 0<2^l)]
    using Cold.filter_range_lt (2*(N*N)) (N*2^l)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
