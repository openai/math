import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.RAM.TickWordBounds
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Word addressability for the mounted layout at the paper parameters -/

namespace ThreeFlat.RAM.TickPhysicalABI
open Computability.VPVNP.BurstRAM Contraction BitLayout Diagonal.ApproximateImage Diagonal.TickWorkspace
open TickActiveROM

variable {F : Type*} [Field F] [Fintype F] {u a teams cap q nt ns np H J : ℕ}

theorem word_bounds (hu : 16 ≤ u)
    (pins : 2+pinCount q nt ns np a ≤ 2^(u^10))
    (hidden : H ≤ 2^(u^10)) (cells : J ≤ 2^(u^10))
    (field : Fintype.card F * Fintype.card F ≤ 2^(u^10))
    (fit : Fits (TickWeightedBank.shape F (pinCount q nt ns np a) H J) (16*u^10)) :
    WordBounds (mounted u a teams cap q nt ns np) fit := by
  let V := 2^(u^10)
  have vp : 16 ≤ V := by
    have le := Nat.le_self_pow (by decide : 10≠0) u
    exact hu.trans (le.trans Nat.lt_two_pow_self.le)
  have vr : 16*V ≤ stride u := by
    change 16*V ≤ V^4
    nlinarith [Nat.mul_le_mul_left V vp,Nat.pow_le_pow_right (by omega : 0<V) (by decide : 2≤4)]
  have chunk : a ≤ V := by dsimp [V]; unfold pinCount at pins; omega
  have cell : J ≤ V := cells
  have pin : pinCount q nt ns np a ≤ V := by dsimp [V]; omega
  have low := low_frame hu pin hidden cells field
  have f : footprint (TickWeightedBank.shape F (pinCount q nt ns np a) H J) < stride u := low
  have near (i : ℕ) (hi : i≤11) : base u i+stride u < 2^(16*u^10) :=
    word_space (by omega) (by omega)
  have seq (i : ℕ) : base u i + stride u ≤ base u (i+1) := apart (by omega)
  have first := lower u 0
  have top := near 9 (by decide)
  have lowAddr := near 0 (by decide)
  have endReq := near 3 (by decide)
  have auxRoom := seq 1
  have previous := seq 0
  have lowMeta := lower u 9
  have lowLut := lower u 10
  have first2 := lower u 2
  have raw : 2+q+nt+ns+np+4*a ≤ V := by dsimp [V]; unfold pinCount at pins; omega
  constructor
  · omega
  · exact (Nat.add_le_add_left (by omega : 4 ≤ stride u) _).trans (seq 0)
  · exact (Nat.add_le_add_left (by omega : 4 ≤ stride u) _).trans (seq 1)
  · exact (Nat.add_le_add_left (by omega : 4 ≤ stride u) _).trans (seq 2)
  · change base u 3 + 8*a < _
    omega
  · change 2+q+nt+ns+np+a ≤ base u 2
    omega
  · change 2+q+nt+ns+np+a+a ≤ base u 2
    omega
  · change 2+q+nt+ns+np+2*a+a ≤ base u 2
    omega
  · change 2+q+nt+ns+np+3*a+a ≤ base u 2
    omega
  · exact f.le.trans lowMeta
  · exact f.le.trans lowLut
  · change base u 9+4*J ≤ _
    omega
  · exact f.trans_le (first.trans (by omega))

end ThreeFlat.RAM.TickPhysicalABI

end OAI
