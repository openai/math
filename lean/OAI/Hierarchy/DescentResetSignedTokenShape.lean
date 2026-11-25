import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentVenueShape

namespace OAI
/-! # The dimensions, banks, and addresses of the signed-token upload -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSIMDLookup ProtocolRAM
noncomputable section
structure Layout where
  hosts : ℕ
  groups : ℕ
  sourceLanes : ℕ
  targetLanes : ℕ
  k : ℕ
  degree : ℕ
  cap : ℕ
  short : ℕ

namespace Layout
variable (s : Layout)
def slots := 2^s.k*(2*s.cap)
abbrev Slot := Fin (2^s.k) × Fin (2*s.cap)
def bits := DescentSignedCableCodec.width s.degree s.cap
def venue : DescentVenueSlabs.Shape := ⟨s.slots,s.hosts,s.groups,s.sourceLanes,s.targetLanes,s.bits⟩
def inputs (pages : s.Slot → Bank) (j : Fin s.slots) := pages (finProdFinEquiv.symm j)
def rows := s.hosts*chunks s.groups s.targetLanes
/-- The complete signed word remains present alongside its marked-sender token. -/
def raw (base : ℕ) (slot : s.Slot) := DescentVenueSlabs.page s.venue base (finProdFinEquiv slot).val
def dictionary (base : ℕ) : Bank := ⟨DescentVenueSlabs.endAddress s.venue base,s.bits*s.targetLanes⟩
def start (base : ℕ) := (s.dictionary base).base+(s.dictionary base).size
def bank (base : ℕ) (slot : s.Slot) : Bank := ⟨s.start base+(finProdFinEquiv slot).val*s.rows,Nat.clog 2 s.rows⟩
def endAddress (base : ℕ) := s.start base+s.slots*s.rows+2^Nat.clog 2 s.rows

end Layout
end
end Hierarchy.DescentResetSignedTokens

end OAI
