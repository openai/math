import OAI.Computability.BorderVNP.TransmissionPinSlots

/-! # Physical link reads of the wired signed contraction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Pins

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

/-- A surviving processor input in the true RAM image reads exactly the common
summation variable at the queried partner and flat link position. -/
theorem Wiring.read_exterior (u v : Fin (R + 1)) (hd : u ≠ v) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) (m : Memory w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (pos : Fin (r * link)) :
    m (physicalBitAddress u.val (R + 1) (G.program.length + t) link v.val pos.val) =
      TeamTapeInputEmit.word w (ext (blockOf u v hd, pos.divNat, pos.modNat)).toNat := by
  have hn : v.val ≠ u.val := fun h => hd (Fin.ext h.symm)
  exact (physical.exterior v.val pos.val u.isLt v.isLt hn pos.isLt).trans
    (exteriorRows_word w u v hd pos.divNat pos.modNat (assignments ext (fun _ (_ : Edge) => false)))

/-- At every positive machine word width the bit read by the routing ISA is its
ordinary Boolean value, with no modular truncation. -/
theorem Wiring.read_exterior_val (hw : 0 < w) (u v : Fin (R + 1)) (hd : u ≠ v)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (m : Memory w) (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (pos : Fin (r * link)) :
    readings m (physicalBitAddress u.val (R + 1) (G.program.length + t) link v.val pos.val) =
      (ext (blockOf u v hd, pos.divNat, pos.modNat)).toNat := by
  rw [readings, G.read_exterior u v hd pin ext ibase hbase starbase m physical pos]
  change _ % 2 ^ w = _
  apply Nat.mod_eq_of_lt
  have htwo : 1 < 2 ^ w := Nat.one_lt_pow hw.ne' (by decide)
  cases ext (blockOf u v hd, pos.divNat, pos.modNat) with
  | false => exact Nat.two_pow_pos w
  | true => exact htwo

/-- Opposite team memories at the two ends of the same physical link contain
equal words, even with different scratch bases and subsequent scratch states. -/
theorem Wiring.read_exterior_swap (u v : Fin (R + 1)) (hd : u ≠ v) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (iu hu su iv hv sv : ℕ) (mu mv : Memory w)
    (pu : (G.processorFields u pin ext iu hu su).ContainsInput mu)
    (pv : (G.processorFields v pin ext iv hv sv).ContainsInput mv)
    (pos : Fin (r * link)) :
    mu (physicalBitAddress u.val (R + 1) (G.program.length + t) link v.val pos.val) =
      mv (physicalBitAddress v.val (R + 1) (G.program.length + t) link u.val pos.val) := by
  rw [G.read_exterior u v hd pin ext iu hu su mu pu pos,
    G.read_exterior v u hd.symm pin ext iv hv sv mv pv pos, blockOf_swap u v hd]

end TeamContraction

end BorderVNP
end Computability
end OAI
