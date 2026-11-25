import OAI.Computability.BorderVNP.RoutingISAExternalSeedModel
import OAI.Computability.BorderVNP.RoutingISAChecked

/-! # Checked reverse-addressed boundary word reads -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ExternalSeed

open VPVNP.BurstRAM DiagonalResidueRAM Packing.Directory.ISA

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Caller registers preserved across the complete prefix preparation. -/
def Preserved (r : Reg) : Prop := (2 ≤ r.val ∧ r.val ≤ 5) ∨ 10 ≤ r.val

/-- Persistent frame, including the caller's saved store cursor and all untouched registers. -/
structure Frame (initial : Bank w) (src n : ℕ) (z : NatState) : Prop where
  /-- Zero word. -/
  zero : z.reg 0 = 0
  /-- Unit word. -/
  one : z.reg 1 = 1
  /-- Address-ordered external bank. -/
  source : z.reg 3 = src
  /-- Number of external bits. -/
  length : z.reg 4 = n
  /-- Saved caller store cursor. -/
  saved : z.reg 7 = (initial 20).val
  /-- Other stable registers retain their original values. -/
  keep : ∀ r, Preserved r → r ≠ 20 → z.reg r = (initial r).val

/-- These registers are untouched by the checked read. -/
private theorem Frame.transport {initial : Bank w} {src n : ℕ} {z y : NatState}
    (f : Frame initial src n z)
    (keep : ∀ r : Reg, r ≠ 6 → r ≠ 8 → r ≠ 9 → y.reg r = z.reg r) :
    Frame initial src n y := by
  constructor
  · exact (keep 0 (by decide) (by decide) (by decide)).trans f.zero
  · exact (keep 1 (by decide) (by decide) (by decide)).trans f.one
  · exact (keep 3 (by decide) (by decide) (by decide)).trans f.source
  · exact (keep 4 (by decide) (by decide) (by decide)).trans f.length
  · exact (keep 7 (by decide) (by decide) (by decide)).trans f.saved
  · intro r hr h20
    have diff (k : Reg) (hk : ¬ Preserved k) : r ≠ k := fun e => hk (e ▸ hr)
    exact (keep r (diff 6 (by unfold Preserved; decide)) (diff 8 (by unfold Preserved; decide))
      (diff 9 (by unfold Preserved; decide))).trans (f.keep r hr h20)

/-- Read one actual boundary bit, with the checked address and increment evaluated without wrap. -/
theorem read_run {initial s : Bank w} {m : Memory w} {src n i : ℕ} (b : Bool)
    (h : Frame initial src n (.ofWords s m)) (hi : i < n) (index : (s 6).val = i)
    (room : src+n ≤ 2^w) (value : (m (src+(n-i-1))).val = b.toNat) :
    ∃ es t, Runs pub macros read s m es t m ∧ traceCost es ≤ read.slots ∧
      Frame initial src n (.ofWords t m) ∧ (t 6).val = i+1 ∧ t 9 = word w b.toNat ∧ t 20 = s 20 := by
  have hz : readings s 0 = 0 := h.zero
  have ho : readings s 1 = 1 := h.one
  have hs : readings s 3 = src := h.source
  have hn : readings s 4 = n := h.length
  have hi' : readings s 6 = i := index
  have hb : readings m (src+(n-i-1)) = b.toNat := value
  have fit : n < 2^w := hn.symm.trans_lt (s 4).isLt
  let reg := Function.update (Function.update (Function.update (readings s) 8 (src+(n-i-1)))
    9 b.toNat) 6 (i+1)
  have eval : read.evalNat (readings pub) (readings m) (readings s) = reg := by
    cases b <;> simp (config := {decide := true}) [read, requireEq, Code.block, Code.evalNat, addressOp,
      hz, ho, hs, hn, hi', hb, reg]
  have safe : read.safeReadOnly w (readings pub) (readings m) (readings s) := by
    cases b <;> simp (config := {decide := true}) [read, requireEq, Code.block, Code.evalNat, addressOp,
      Code.safeReadOnly, addressOpFits, hz, ho, hs, hn, hi', hb] <;> omega
  obtain ⟨es,t,r,ct,eq⟩ := read.runReadOnly pub macros m s safe
  rw [eval] at eq
  have atReg (j : Reg) : (t j).val = reg j := congrFun eq j
  have keep (j : Reg) (j6 : j ≠ 6) (j8 : j ≠ 8) (j9 : j ≠ 9) : (t j).val = (s j).val := by
    simpa [reg, Function.update_of_ne, j6, j8, j9, readings] using atReg j
  refine ⟨es,t,r,ct,h.transport keep,?_,?_,Fin.ext (keep 20 (by decide) (by decide) (by decide))⟩
  · simpa [reg] using atReg 6
  · apply Fin.ext
    rw [word_val _ _ (value ▸ (m (src+(n-i-1))).isLt)]
    simpa (config := {decide := true}) [reg] using atReg 9

/-- The rejecting guard is enforced by the real word machine: successful reads require
zero or one at the addressed source position. -/
theorem read_binary {initial s : Bank w} {m : Memory w} {src n i : ℕ}
    (h : Frame initial src n (.ofWords s m)) (hi : i < n) (index : (s 6).val = i)
    (room : src+n ≤ 2^w) {es t mt} (r : Runs pub macros read s m es t mt) :
    (m (src+(n-i-1))).val ≤ 1 := by
  have hz : readings s 0 = 0 := h.zero
  have ho : readings s 1 = 1 := h.one
  have hs : readings s 3 = src := h.source
  have hn : readings s 4 = n := h.length
  have hi' : readings s 6 = i := index
  have fit : n < 2^w := hn.symm.trans_lt (s 4).isLt
  by_contra! bad
  have bad' : 1 < readings m (src+(n-i-1)) := bad
  have h0 : readings m (src+(n-i-1)) ≠ 0 := by omega
  have h1 : readings m (src+(n-i-1)) ≠ 1 := by omega
  have safe : read.relaxReject.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [read, requireEq, Code.block, Code.evalNat, addressOp,
      Code.relaxReject, Code.safeReadOnly, addressOpFits, hz, ho, hs, hn, hi', h0, h1]
    omega
  have checked := r.checked (by decide) safe
  simp (config := {decide := true}) [read, requireEq, Code.block, Code.evalNat, addressOp,
    Code.safeReadOnly, addressOpFits, hz, ho, hs, hn, hi', show readings m (src+(n-i-1)) ≠ 0 by omega,
    show readings m (src+(n-i-1)) ≠ 1 by omega] at checked

end RoutingISA.ExternalSeed

end BorderVNP
end Computability
end OAI
