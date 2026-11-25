import OAI.Hierarchy.DescentResetStemProject
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentSignedCableFields

namespace OAI
/-! The public shape of an ordinary mark pass on the incoming physical SIMD pitch. -/
namespace Hierarchy.DescentOrdinaryMarkProject
open DescentDyadicSpan DescentSIMDLookup

structure Shape where
  paths : ℕ
  priorBlocks : ℕ
  cap : ℕ
  degree : ℕ
  oldHosts : ℕ
  hosts : ℕ
  groups : ℕ
  blocks : ℕ
  oldLanes : ℕ
  lanes : ℕ

namespace Shape
variable (s : Shape)

def slots := s.priorBlocks*s.cap*11
def sourceRows := s.oldHosts*chunks (s.groups*s.blocks) s.oldLanes
def pitch := span (1+s.oldHosts+s.sourceRows)
def portWords := (s.paths+2)*s.pitch
def markStart (floor : ℕ) := floor+s.portWords
def fieldStart (floor : ℕ) := s.markStart floor+4*2^(DescentSignedCableCodec.width s.degree s.cap*s.oldLanes)
def groupEnd (floor : ℕ) :=
  DescentResetStemProject.endAddress (s.fieldStart floor) (s.paths*s.slots) s.oldHosts s.groups s.blocks 1 s.oldLanes s.lanes
def endAddress (floor : ℕ) := s.groupEnd floor+span (s.hosts*chunks s.groups s.lanes)

theorem translated (floor : ℕ) : s.endAddress floor=floor+s.endAddress 0 := by
  unfold endAddress groupEnd
  rw [DescentResetStemProject.extent (s.fieldStart floor),DescentResetStemProject.extent (s.fieldStart 0)]
  simp only [fieldStart,markStart,Nat.zero_add,Nat.add_assoc]

theorem low (floor : ℕ) : floor≤ s.endAddress floor := by
  rw [s.translated]
  exact Nat.le_add_right ..

end Shape
end Hierarchy.DescentOrdinaryMarkProject

end OAI
