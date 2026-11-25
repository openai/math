import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # Arithmetic fit at the physical routing addresses

These tests refer to the sizes of the public tables and the physical memory
positions, and do not quantify over machine traces.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

private theorem readFrameSafe {w : ℕ} (d : Reg) (f : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w pub mem s ↔ pub 0 + f.val < 2^w := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.safeReadOnly, Code.evalNat,
    addressOpFits]
  omega

/-- Fitting the stride, the frame, and the final physical address suffices for
every intermediate arithmetic operation and the positive link divisor. -/
theorem physicalAddress_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (frameRoom : pub 0 + 4 < 2^w) (teamsPos : 0 < frameField pub mem 1)
    (linkPos : 0 < frameField pub mem 4) (distinct : s 30 ≠ frameField pub mem 0)
    (strideRoom : 2 * frameField pub mem 3 + (frameField pub mem 1 - 1) * frameField pub mem 4 < 2^w)
    (addrRoom : physicalBitAddress (frameField pub mem 0) (frameField pub mem 1) (frameField pub mem 3)
      (frameField pub mem 4) (s 30) (s 31) < 2^w) :
    physicalAddress.safeReadOnly w pub mem s := by
  have nonzero : w ≠ 0 := by rintro rfl; simp at frameRoom
  by_cases side : s 30 < frameField pub mem 0 <;>
    simp (config := { decide := true }) [physicalAddress, Code.block, Code.safeReadOnly, readFrameSafe,
      readFrameFixed, Code.evalNat, addressOp, addressOpFits, side] <;>
    simp only [physicalBitAddress, side, ite_true, ite_false] at addrRoom <;>
    rw [Nat.mul_comm 2, Nat.add_comm (frameField pub mem 3 * 2)] at strideRoom addrRoom <;>
    omega

/-- Physical word-space assumptions for a single two-hop table lookup. -/
structure LegRoom (w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) (u v y q : ℕ) : Prop where
  /-- The frame contains the ordered-leg total directory field. -/
  frame : pub 0 + 18 < 2^w
  /-- At least one team. -/
  teamsPos : 0 < frameField pub mem 1
  /-- Positive processor exterior width. -/
  linkPos : 0 < frameField pub mem 4
  /-- The partner computed for this call differs from the local team. -/
  distinct : (if frameField pub mem 0 = u then v else u) ≠ frameField pub mem 0
  /-- The two literal-width fields and all exterior fields fit in one word. -/
  stride : 2 * frameField pub mem 3 + (frameField pub mem 1 - 1) * frameField pub mem 4 < 2^w
  /-- Address of the accessed prefix table entry. -/
  triple : tripleIndex (frameField pub mem 17) (frameField pub mem 1) u v y < 2^w
  /-- Address of the accessed reverse total if this is the reverse orientation. -/
  pair : v < u → pairIndex (frameField pub mem 18) (frameField pub mem 1) v u < 2^w
  /-- The bit offset including broadcast, direction and preceding partners. -/
  position : legPosition pub mem u v y q < 2^w
  /-- The final word address in actual processor initialization memory. -/
  address : routedAddress pub mem u v y q < 2^w

/-- Physical array space, the fitted block position and fitted final address give
all no-wrap and division checks in the compiled leg address program. -/
theorem legAddress_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (room : LegRoom w pub mem (s 32) (s 33) (s 34) (s 35)) :
    legAddress.safeReadOnly w pub mem s := by
  obtain ⟨frame,teamsPos,linkPos,distinct,stride,triple,pair,position,address⟩ := room
  have mulBound : s 32 * frameField pub mem 1 + s 33 ≤
      (s 32 * frameField pub mem 1 + s 33) * frameField pub mem 1 :=
    Nat.le_mul_of_pos_right _ teamsPos
  by_cases reverse : s 33 < s 32 <;> by_cases localEnd : frameField pub mem 0 = s 32 <;>
    simp (config := { decide := true }) [legAddress, Code.block, readFrameSafe, readFrameFixed,
      Code.safeReadOnly, Code.evalNat, pairAddress, tripleAddress, addressOpFits, addressOp, reverse, localEnd] <;>
    simp only [tripleIndex, pairIndex, legPosition, routedAddress, reverse, localEnd, ite_true, ite_false,
      add_zero, true_implies, false_implies] at distinct triple pair position address
  all_goals repeat' first | apply physicalAddress_safe | apply And.intro
  all_goals first | assumption | omega | (simp (config := { decide := true }); first | assumption | rwa [localEnd])

/-- The positive relay period and fitted team count keep the quotient and both
ordinal skips in range. The selected leg then satisfies its own space checks. -/
theorem endpointAddress_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (teams : 2 < frameField pub mem 1) (fits : frameField pub mem 1 < 2^w)
    (room : LegRoom w pub mem (frameField pub mem 0)
      (endpointRelay (frameField pub mem 1) (frameField pub mem 0) (s 30) (s 31)) (s 30)
      (s 31 / (frameField pub mem 1 - 2))) :
    endpointAddress.safeReadOnly w pub mem s := by
  have frame := room.frame
  have nonzero : w ≠ 0 := by rintro rfl; simp at frame
  have modBound := Nat.mod_lt (s 31) (by omega : 0 < frameField pub mem 1 - 2)
  by_cases side : frameField pub mem 0 < s 30
  · by_cases first : s 31 % (frameField pub mem 1 - 2) < frameField pub mem 0 <;>
      by_cases second : Routing.skip (frameField pub mem 0) (s 31 % (frameField pub mem 1 - 2)) < s 30 <;>
      simp only [Routing.skip, first, ite_true, ite_false] at second <;>
      simp (config := { decide := true }) [endpointAddress, Code.block, readFrameSafe, readFrameFixed,
        Code.evalNat, Code.safeReadOnly, skipRegister, addressOp, addressOpFits, side, first, second] <;>
      simp only [endpointRelay, min_eq_left side.le, max_eq_right side.le, Routing.skip, first, second,
        ite_true, ite_false] at room
    all_goals repeat' first | apply legAddress_safe | apply And.intro
    all_goals first | omega | simpa (config := { decide := true }) using room
  · by_cases first : s 31 % (frameField pub mem 1 - 2) < s 30 <;>
      by_cases second : Routing.skip (s 30) (s 31 % (frameField pub mem 1 - 2)) < frameField pub mem 0 <;>
      simp only [Routing.skip, first, ite_true, ite_false] at second <;>
      simp (config := { decide := true }) [endpointAddress, Code.block, readFrameSafe, readFrameFixed,
        Code.evalNat, Code.safeReadOnly, skipRegister, addressOp, addressOpFits, side, first, second] <;>
      simp only [endpointRelay, min_eq_right (le_of_not_gt side), max_eq_left (le_of_not_gt side), Routing.skip,
        first, second, ite_true, ite_false] at room
    all_goals repeat' first | apply legAddress_safe | apply And.intro
    all_goals first | omega | simpa (config := { decide := true }) using room

end RoutingISA

end BorderVNP
end Computability
end OAI
