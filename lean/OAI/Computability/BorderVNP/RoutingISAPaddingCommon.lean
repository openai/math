import OAI.Computability.BorderVNP.RoutingISABroadcastModel
import OAI.Computability.BorderVNP.RoutingISAPartnerLoop
import OAI.Computability.BorderVNP.RoutingISAPaddingScan

/-! # Memory conditions for incident padding and unit-branch scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Registers held across the scan of incident partner blocks. -/
def partnerInv {w : ℕ} (f : BroadcastFrame) (base : ℕ) (s : Bank w) : Prop :=
  f.Stable (readings s) ∧ (s 19).val = base

/-- First padding position, computed from both oriented loads at the actual table base. -/
def BroadcastFrame.paddingFrom (f : BroadcastFrame) (mem : ℕ → ℕ) (base i : ℕ) : ℕ :=
  f.header + mem (pairIndex base f.teams f.team i) + mem (pairIndex base f.teams i f.team)

/-- All physical words in the suffix of the designated partner block are zero. -/
def BroadcastFrame.ZeroFrom (f : BroadcastFrame) (mem : ℕ → ℕ) (start i : ℕ) : Prop :=
  ∀ j, start ≤ j → j < f.capacity → mem (f.addr i j) = 0

/-- Preserving the header and table-base registers preserves the invariant. -/
theorem partnerInv_of_preserves {w : ℕ} {f : BroadcastFrame} {base : ℕ} {s t : Bank w}
    (h : partnerInv f base s) (pres : ∀ i : Reg, i.val ≤ 9 ∨ i = 14 ∨ i = 19 →
      (t i).val = (s i).val) : partnerInv f base t := by
  rcases h with ⟨⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h14⟩,h19⟩
  exact ⟨⟨(pres 0 (by decide)).trans h0, (pres 1 (by decide)).trans h1,
    (pres 2 (by decide)).trans h2,(pres 3 (by decide)).trans h3,
    (pres 4 (by decide)).trans h4,(pres 5 (by decide)).trans h5,
    (pres 6 (by decide)).trans h6,(pres 7 (by decide)).trans h7,
    (pres 8 (by decide)).trans h8,(pres 9 (by decide)).trans h9,
    (pres 14 (by decide)).trans h14⟩,(pres 19 (by decide)).trans h19⟩

/-- Changing the partner register preserves the loaded header and table data. -/
theorem partnerRegs {w : ℕ} (f : BroadcastFrame) (base : ℕ) :
    PartnerRegs f.teams f.team (partnerInv (w := w) f base) where
  values s h := ⟨h.1.2.1,h.1.2.2.1,h.1.2.2.2.1⟩
  counter s h v := partnerInv_of_preserves h fun i hi => by
    have hn : i ≠ 11 := by rintro rfl; rcases hi with hi | hi | hi <;> norm_num at hi
    rw [Function.update_of_ne hn]

/-- A scan uses the same input addresses as the initialized broadcast frame. -/
theorem scanAddr_eq {f : BroadcastFrame} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (image : f.At pub mem) (i j : ℕ) : zeroScanAddr pub mem i j = f.addr i j := by
  rcases image with ⟨h0,h1,_,h3,h4,_,_⟩
  simp only [zeroScanAddr,BroadcastFrame.addr,h0,h1,h3,h4]

/-- The fitted allocation bounds all scratch operands and physical input addresses
throughout one suffix scan, for every incident partner. -/
theorem scanRoom {w : ℕ} {f : BroadcastFrame} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (image : f.At pub mem) (fit : f.Fits w (pub 0)) {i : ℕ}
    (hi : i < f.teams) (hne : i ≠ f.team) (start : ℕ) :
    ZeroScanRoom w pub mem i start f.capacity := by
  have img := image
  rcases img with ⟨h0,h1,_,h3,h4,_,_⟩
  have hpow : pub 0+4 < 2^w := by have := fit.frame; have := fit.out; omega
  have hstride : f.stride ≤ f.processors*f.stride := Nat.le_mul_of_pos_left _ fit.procs
  constructor
  · exact hpow
  · rw [h1]; have := fit.three; omega
  · rw [h4]; exact fit.width
  · rw [h0]; exact hne
  · rw [h3,h1,h4]
    change f.stride < _
    have := fit.input
    omega
  · intro j _ hj
    rw [scanAddr_eq image]
    exact (f.addr_lt_input fit hi hne hj).trans_le (fit.input.trans (by omega))

end RoutingISA

end BorderVNP
end Computability
end OAI
