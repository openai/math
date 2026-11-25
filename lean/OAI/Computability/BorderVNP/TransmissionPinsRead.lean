import OAI.Computability.BorderVNP.TransmissionPinsLayout

/-! # Native initialization and addressing of the secondary pins -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

private theorem readFrameSafe {w : ℕ} (d : Reg) (f : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w pub mem s ↔ pub 0 + f.val < 2^w := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.safeReadOnly, Code.evalNat,
    addressOpFits]
  omega

set_option maxRecDepth 5000 in
set_option maxHeartbeats 2000000 in
/-- Pin setup loads the frame and computes every persistent register without wrapping. -/
theorem pinSetup_run {w : ℕ} (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (h : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) :
    ∃ es t, Runs pub macros pinSetup s m es t m ∧ traceCost es ≤ pinSetup.slots ∧ Ready L 0 t := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hframe
  have safe : pinSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := { decide := true }) [pinSetup, Code.block, Code.safeReadOnly, readFrameSafe,
      readFrameFixed, Code.evalNat, addressOp, addressOpFits, h.teams, h.link, h.literal,
      h.processors]
    unfold Layout.stride Layout.offset at hs
    unfold Layout.count at hc
    omega
  obtain ⟨es, t, run, cost, agree⟩ := pinSetup.runReadOnly pub macros m s safe
  refine ⟨es, t, run, cost, ?_⟩
  constructor <;>
    simp (config := { decide := true }) [agree, pinSetup, Code.block, readFrameFixed, Code.evalNat,
      addressOp, h.team, h.teams, h.processors, h.literal, h.link, h.width, h.ibase, h.hbase,
      h.starbase, Layout.offset, Layout.stride, Layout.count]

/-- The processor stride and pin-field offset give the physical address used by the reader. -/
theorem livePinAddress_layout (L : Layout) (x : ℕ) :
    livePinAddress L.teams L.literal L.link x =
      x / L.literal * L.stride + L.offset + x % L.literal := by
  unfold livePinAddress Layout.stride Layout.offset
  rw [show 2 * L.literal + (L.teams-1)*L.link =
    L.literal + (L.teams-1)*L.link + L.literal by omega]

/-- Every valid flat cursor addresses a word inside the physical processor region. -/
theorem livePinAddress_lt (L : Layout) {x : ℕ} (hx : x < L.count) :
    livePinAddress L.teams L.literal L.link x < L.processors * L.stride := by
  change x < L.processors * L.literal at hx
  have hl : 0 < L.literal := Nat.pos_of_ne_zero (by
    intro h
    simp [h] at hx)
  have hq : x / L.literal < L.processors := (Nat.div_lt_iff_lt_mul hl).2 hx
  rw [livePinAddress_layout]
  calc
    _ < x / L.literal * L.stride + L.stride := by
      have hr := Nat.mod_lt x hl
      unfold Layout.stride
      omega
    _ = (x / L.literal + 1) * L.stride := by rw [Nat.add_mul, one_mul]
    _ ≤ L.processors * L.stride := Nat.mul_le_mul_right _ hq

/-- Reading a secondary pin returns the word at its physical address and preserves the cursor. -/
theorem fetchLivePin_run {w : ℕ} (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (h : Ready L x s)
    (hl : 0 < L.literal) (ha : livePinAddress L.teams L.literal L.link x < 2^w) :
    ∃ es t, Runs pub macros fetchLivePin s m es t m ∧ traceCost es ≤ fetchLivePin.slots ∧
      Ready L x t ∧ readings t 14 = readings m (livePinAddress L.teams L.literal L.link x) := by
  rw [livePinAddress_layout] at ha ⊢
  have safe : fetchLivePin.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := { decide := true }) [fetchLivePin, Code.block, Code.safeReadOnly, Code.evalNat,
      addressOp, addressOpFits, h.cursor, h.literal, h.stride, h.offset, hl]
    omega
  obtain ⟨es, t, run, cost, agree⟩ := fetchLivePin.runReadOnly pub macros m s safe
  refine ⟨es, t, run, cost, h.congr (fun i hi ↦ ?_), ?_⟩
  · rw [agree]
    exact fetchLivePin.evalNat_protected _ _ _ (by decide : fetchLivePin.protects 12 = true) i hi
  · simp (config := { decide := true }) [agree, fetchLivePin, Code.block, Code.evalNat, addressOp,
      h.cursor, h.literal, h.stride, h.offset]

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
