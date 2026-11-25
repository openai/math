import OAI.Computability.BorderVNP.PackedDirectoryISA
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # Register semantics of the placement directory's candidate calculation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA

/-- Immutable loop registers loaded from the common public frame. -/
structure Prepared (d : Layout) (privateBase liveBase : ℕ) (s : Reg → ℕ) : Prop where
  /-- The zero, one and two registers. -/
  constants : s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 2
  /-- Scalar fields in registers 3–10. -/
  sizes : s 3 = d.teams ∧ s 4 = d.processors ∧ s 5 = d.literal ∧ s 6 = d.link ∧
    s 7 = d.sites ∧ s 8 = d.block ∧ s 9 = d.description ∧ s 10 = d.fields
  /-- Public array bases. -/
  bases : s 11 = privateBase ∧ s 12 = liveBase
  /-- Cached candidate counts and input strides. -/
  derived : s 13 = 2*d.entries ∧ s 14 = d.literal/d.block+2 ∧ s 15 = d.literal/2 ∧
    s 16 = d.stride ∧ s 17 = d.literal+(d.teams-1)*d.link ∧ s 18 = d.candidates

/-- Decode the public scalar parameters installed by the layout stage. -/
def frameLayout (pub : Arg → ℕ) (mem : ℕ → ℕ) : Layout :=
  let f := frameField pub mem
  ⟨f 1, f 2, f 3, f 4, f 67, f 68, f 69, f 66, f 70 + 1⟩

/-- The read-only setup computes all the loop sizes and points the writer at the
public output bank. Its starting candidate is zero. -/
theorem setup_eval (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    let t := setup.evalNat pub mem s
    Prepared (frameLayout pub mem) (frameField pub mem 64) (frameField pub mem 65) t ∧
      t 19 = 0 ∧ t 20 = frameField pub mem 8 ∧ t 21 = frameField pub mem 8 := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩ <;>
    simp (config := { decide := true }) [setup, Code.block, Code.evalNat, readFrameFixed, addressOp,
      frameLayout, Layout.stride, Layout.candidates, Nat.mul_comm]

/-- Read the pair of words at the indexed placement entry. -/
def placement (mem : ℕ → ℕ) (base j : ℕ) : ℕ × ℕ :=
  (mem (base + j*2), mem (base + j*2 + 1))

/-- The seven native result registers in their wire order. -/
def result (s : Reg → ℕ) : Row := ⟨s 32,s 33,s 34,s 35,s 36,s 37,s 38⟩

/-- The overlap fragment returns the actual start, end and saturated width. -/
theorem intersect_eval (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    let i := s 22/s 24+s 25
    let left := i*s 24
    let lo := max (s 22) left
    let hi := min (s 22+s 23) (left+s 24)
    intersection.evalNat pub mem s =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update s 26 i) 27 left) 28 lo) 30 (left+s 24)) 29 hi) 38
          (if hi < lo then s 0 else hi-lo) := by
  dsimp only
  by_cases left : s 22 < (s 22/s 24+s 25)*s 24 <;>
    by_cases right : (s 22/s 24+s 25)*s 24+s 24 < s 22+s 23 <;>
    simp (config := { decide := true }) [intersection, Code.block, Code.evalNat, addressOp,
      left, right, max_def_lt, min_def_lt', Function.update_comm (show (29 : Reg) ≠ 30 by decide),
      Function.update_idem] <;> split <;> simp_all

/-- Every seven-word candidate calculated by the public machine agrees with the
corresponding private-tail or live-site intersection, including zero-width candidates. -/
theorem candidate_eval {d : Layout} {p l : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (h : Prepared d p l s) :
    result (candidate.evalNat pub mem s) = d.row (placement mem p) (placement mem l) (s 19) := by
  rcases h with ⟨⟨h0,h1,h2⟩,⟨h3,h4,h5,h6,h7,h8,h9,h10⟩,⟨h11,h12⟩,⟨h13,h14,h15,h16,h17,h18⟩⟩
  by_cases priv : s 19 < 2*d.entries <;>
    simp (config := { decide := true }) [candidate, Code.block, Code.evalNat, privateCandidate,
      liveCandidate, intersect_eval, getPlacement, addressOp, result, Layout.row, Layout.privateRow,
      Layout.liveRow, placement, slice, priv, h0,h1,h2,h4,h5,h7,h8,h9,h10,h11,h12,h13,
      h14,h15,h16,h17] <;> omega

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
