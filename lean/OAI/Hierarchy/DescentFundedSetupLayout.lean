import OAI.Hierarchy.DescentDatedSignedArea
import OAI.Hierarchy.DescentOverlapTables
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentFundedCensusLayout

namespace OAI
/-! # One preceding funded channel and the shared incoming-port table -/
namespace Hierarchy.DescentFundedCensus
open DescentGLPacked.BankImage DescentGLControlCode DescentSIMDLookup

structure Setup where
  hosts : ℕ
  oldGroups : ℕ
  blocks : ℕ
  oldLanes : ℕ
  gatherLanes : ℕ
  precision : ℕ
  high : ℕ
  low : ℕ
  cut : ℕ
  degree : ℕ
  capacity : ℕ
  outputLanes : ℕ

namespace Setup
variable (s : Setup)
def donors := 2^(s.high+s.low-s.cut)
def stripSpan := Overlap.endAddress 0 s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision
def stripEnd (base : ℕ) := base+s.blocks*s.stripSpan
def matrix (base : ℕ) := s.stripEnd base+s.blocks*(2*2^((s.precision*s.blocks+s.precision)*s.gatherLanes))
def signedEnd (base : ℕ) := SignedFields.stop (s.matrix base) 1 s.hosts s.high s.low s.precision
def flagWidth := (DescentSignedCableCodec.width s.degree s.capacity*s.donors)*s.outputLanes
def roof (base : ℕ) := s.signedEnd base+2^s.flagWidth

theorem shift (base : ℕ) : s.roof base=base+s.roof 0 := by
  simp only [roof,signedEnd,SignedFields.stop,Dated.extent,matrix,stripEnd,Nat.zero_add,Nat.add_assoc]
theorem order (base : ℕ) : base≤ s.stripEnd base ∧ s.stripEnd base≤ s.matrix base ∧
    s.matrix base≤ s.signedEnd base ∧ s.signedEnd base≤ s.roof base :=by
  exact ⟨Nat.le_add_right ..,Nat.le_add_right ..,Dated.origin_le_endAddress ..,Nat.le_add_right ..⟩
theorem room (base : ℕ) : base≤ s.roof base := by rw [s.shift];exact Nat.le_add_right ..
end Setup
end Hierarchy.DescentFundedCensus

end OAI
