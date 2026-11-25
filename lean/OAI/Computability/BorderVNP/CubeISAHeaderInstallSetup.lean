import OAI.Computability.BorderVNP.CubeISAHeaderInstallModel

/-! # Loading frame scalars and calculating the dense cube bank addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM

/-- Load every primary input before modifying shared memory. Registers 21–33 hold the
thirteen output fields, in address order. The widths and volume are filled later. -/
def setup : Code := .block [readFrame 20 62 63 63, readFrame 34 62 63 59,
  readFrame 25 62 63 60, readFrame 28 62 63 109, readFrame 30 62 63 110,
  readFrame 33 62 63 111, .constant 1 1, .constant 26 0, .constant 37 2,
  .binary .mul 35 34 34, .binary .mul 23 35 25, .constant 21 13,
  .binary .add 21 20 21, .binary .add 22 21 23, .binary .add 24 22 23,
  .binary .add 29 24 25, .binary .sub 36 35 34, .binary .div 36 36 37,
  .binary .mul 40 37 28, .constant 27 0, .copy 45 25]

/-- Register contents for the entries which survive both size computations. -/
structure Static (l : Inputs) (r : Reg → ℕ) : Prop where
  /-- Cursor increment. -/
  one : r 1 = 1
  /-- Initial output cursor. -/
  header : r 20 = l.header
  /-- Computed rows. -/
  actual : r 21 = l.header+13
  /-- Declared rows. -/
  claimed : r 22 = l.header+13+l.entries
  /-- Length of each row array. -/
  entries : r 23 = l.entries
  /-- Start of the directional totals. -/
  totals : r 24 = l.header+13+2*l.entries
  /-- Direction count. -/
  a : r 25 = l.a
  /-- Initial coordinate value. -/
  chosen : r 26 = 0
  /-- Number of blocks. -/
  blocks : r 28 = l.blocks
  /-- Packet-bank base. -/
  bank : r 29 = l.packetBase
  /-- Geometry prefix. -/
  profile : r 30 = l.profile
  /-- Declaration cap. -/
  cap : r 33 = l.cap

/-- Scratch registers are outside the static output fields. -/
theorem Static.congr {l : Inputs} {r s : Reg → ℕ} (hs : Static l r)
    (keep : ∀ j : Reg, j.val ≤ 33 → j ≠ 27 → j ≠ 31 → j ≠ 32 → s j = r j) : Static l s := by
  rcases hs with ⟨h1,h20,h21,h22,h23,h24,h25,h26,h28,h29,h30,h33⟩
  constructor <;> first | exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans (by assumption)

set_option maxHeartbeats 1800000 in
/-- The physical reads return the bank layout and initialize both accumulators. -/
theorem setup_run {w n bits : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Inputs) (loaded : l.Loaded (readings pub) (readings m))
    (fit : l.Fits w n bits (readings pub 0)) :
    BoundedRun pub mac setup s m setup.slots (fun z => Static l z.reg ∧ z.reg 40 = 2*l.blocks ∧
      z.reg 36 = l.d.choose 2 ∧ z.reg 27 = 0 ∧ z.reg 45 = l.a ∧ z.mem = readings m) := by
  rcases loaded with ⟨hh,hd,ha,hb,hp,hc⟩
  simp only [frameField] at hh hd ha hb hp hc
  have sz : l.d ≤ l.d*l.d := Nat.le_mul_self l.d
  have sub : l.d*l.d-l.d = l.d*(l.d-1) := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have pair : 2*l.blocks < 2^w := (show 2*l.blocks ≤ 2*l.blocks*max 1 ((l.d.choose 2)^n) by
    exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..))).trans_lt fit.packets
  have hbank := fit.bank
  simp only [Inputs.packetBase,Inputs.entries] at hbank
  have ff (dst : Reg) (f : Word 8) (st : NatState) (bound : f.val ≤ 111) :
      (readFrame dst 62 63 f).fixedSafe w (readings pub) st :=
    readFrame_fixedSafe _ _ _ _ _ (lt_of_le_of_lt (Nat.add_le_add_left bound _) fit.primary)
  have square := fit.square
  apply (Code.runFixed setup pub mac s m ?_).mono le_rfl
  · rintro _ rfl
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · constructor <;> simp (config := {decide := true}) [setup,Code.block,readFrame_fixedEval,
        Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,hh,hd,ha,hb,hp,hc,
        Inputs.entries,Inputs.packetBase,two_mul,Nat.add_assoc]
    all_goals simp (config := {decide := true}) [setup,Code.block,readFrame_fixedEval,Code.fixedEval,
      Code.evalNat,addressOp,NatState.ofWords,hh,hd,ha,hb,hp,hc,sub,Nat.choose_two_right]
  · simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOp,addressOpFits,readFrame_fixedEval,NatState.ofWords,hh,hd,ha,hb,hp,hc,
      ff _ _ _ (by decide : (63 : Word 8).val ≤ 111),ff _ _ _ (by decide : (59 : Word 8).val ≤ 111),
      ff _ _ _ (by decide : (60 : Word 8).val ≤ 111),ff _ _ _ (by decide : (109 : Word 8).val ≤ 111),
      ff _ _ _ (by decide : (110 : Word 8).val ≤ 111),ff _ _ _ (by decide : (111 : Word 8).val ≤ 111),
      square,sz,pair]
    have hw : w ≠ 0 := by rintro rfl; simp at hbank
    omega

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
