import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloAuto
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryBudget
import OAI.Computability.NearSquareRoot.InterchangeBeadConvert
import OAI.Computability.NearSquareRoot.InterchangeFatRecursion

/-! # A canonical native request for each binary interchange packet -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Ticket

open IntegerMultiplication Code Strip Strip.Dims Loom Adic
open NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request

open private halo_len from OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloAuto

noncomputable section

def recordTree (k : ℕ) (x : Ticket) (a : DenseKey x) :=
  send (InterchangeBeadConvert.padded (pad k x) (x.bits a))

def recordSize (k : ℕ) (x : Ticket) := 4*(pad k x+x.w+1)

theorem recordTree_size (k : ℕ) (x : Ticket) (a : DenseKey x) :
    (recordTree k x a).count ≤ recordSize k x := by
  simpa only [recordTree,recordSize,x.exactWidth] using InterchangeBeadConvert.size_padded (pad k x) (x.bits a)

/-- The request has the native field radix, width and canonical numerical
alphabet. A missing halo position receives a copy of a genuine record. -/
def request (k : ℕ) (x : Ticket) : Request x.b :=
  ⟨x.P,x.G,x.B,x.e,pad k x+x.w,x.extendFirst (recordTree k x)⟩

theorem request_volume (k : ℕ) (x : Ticket) :
    (x.request k).recordVolume = x.total*(pad k x+x.w+1) := by
  change x.haloStock.count * _ = _
  rw [halo_len]
  rfl

theorem request_valid (k : ℕ) {p : ℕ} (hp : 2 ≤ p) (x : Ticket) :
    Packed (fun z : ZMod p => InterchangeROMTable.numeral z.val) (x.request k) ∧ Thick k (x.request k) := by
  refine ⟨⟨fun d hd => ⟨(x.admissible d hd).1,(x.admissible d hd).2.trans x.large⟩,
    (width_bounds x.radix_ok x.n).1,?_⟩,?_⟩
  · intro a
    apply x.extendFirst_prop (recordTree k x) (record _ (pad k x+x.w)) _ a
    intro i
    simpa only [recordTree,x.exactWidth] using InterchangeBeadConvert.record_padded hp (pad k x) (x.bits i)
  · change (Nat.log 2 x.haloStock.count+1)^k ≤ pad k x+x.w+1
    rw [halo_len]
    have := pad_thick k x
    omega

def rawMass (t : ℕ) (x : Ticket) := ⌈mass regime total (fun x => x.w) t x⌉₊

end
end InterchangeROMBinary.Ticket

end NearSquareRoot
end Computability
end OAI
