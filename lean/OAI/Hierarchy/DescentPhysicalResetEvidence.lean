import OAI.Hierarchy.DescentDatedCandidateFront
import OAI.Hierarchy.DescentResetPeerRawTables

namespace OAI
/-! # The original packed stem keys and the four lookup tables used before peer detection -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetPeerUnionRAM DescentResetStemKey ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (v : CandidateFront)
local notation "p₀" => v.peer
structure Evidence where
  n : ℕ
  oldPorts : ℕ
  rootBits : ℕ
  depth : ℕ
  board : NonlinearExpanders.Graph n oldPorts
  decode : Decoder (p₀).oldDegree v.stemField
  sides : Fin v.oldKeysCount→Bool
  source : Fin v.oldKeysCount→Fin ((p₀).oldDegree+2)→Expr
  template : Bool→Fin v.oldTicketCount→Option (Fin (p₀).shapes×Fin (p₀).shapes)

def rawTables (base : ℕ) : RawTables.Layout :=
  ⟨v.oldKeys base,(p₀).oldHosts,(p₀).shapes,(p₀).oldDegree,v.oldGroups,v.oldLanes,v.wireCap,
    v.privateBits,v.stemField+2,(p₀).bits⟩
variable (a : v.Evidence) (base : ℕ)
local notation "T" => v.rawTables base

def originalEvidence (w : ℕ) :=
  (Columns.code a.decode a.sides a.source base v.oldLanes (p₀).oldHosts v.oldGroups w).seq
    (RawTables.program a.board a.rootBits a.depth T a.template w)
def evidenceClock :=
  Columns.ticks a.decode a.sides a.source base v.oldLanes (p₀).oldHosts v.oldGroups+(T).ticks
def evidenceImage {w : ℕ} (m : Memory w) :=
  RawTables.image a.board a.rootBits a.depth T a.template
    (Columns.output a.decode a.sides a.source base v.oldLanes (p₀).oldHosts v.oldGroups m)

/-- The raw chips consume old lanes, up to the last byte of the public evidence region. -/
theorem tables_end (oldLanes : v.oldLanes=(p₀).evidenceLanes) :
    (T).endAddress=v.rawTablesEnd base := by
  unfold RawTables.Layout.endAddress RawTables.Layout.trunk RawTables.Layout.second RawTables.Layout.first
    RawTables.Layout.trunkWords RawTables.Layout.stemWords RawTables.Layout.privateWords
  unfold rawTablesEnd PeerAperture.chipEnd negativeStem positiveStem privateChip
    DescentResetStemPeerChip.endAddress DescentResetStemPeerChip.start PrivateEvidence.endAddress
  dsimp only [rawTables]
  simp only [oldLanes,Nat.add_assoc]

theorem evidence_any {w : ℕ} (m : Memory w) (fit : ∀q i,(a.source q i).Fits w base)
    (oldLanes : v.oldLanes=(p₀).evidenceLanes) (room : v.rawTablesEnd base<2^w) :
    (v.originalEvidence a base w).Exec m (v.evidenceImage a base m) (v.evidenceClock a base) ∧
    (∀x,x<base ∨ v.rawTablesEnd base≤x → v.evidenceImage a base m x=m x) ∧ CheapCode (v.originalEvidence a base w) := by
  have stop:=(T).end_eq
  have eqn:=v.tables_end base oldLanes
  have lo:base≤v.oldKeys base:=by dsimp [oldKeys,Columns.stop,Columns.start];omega
  have hi:v.oldKeys base≤v.rawTablesEnd base:=by rw [←eqn,stop];exact Nat.le_add_right ..
  have first:=Columns.any_full a.decode a.sides a.source base m fit (hi.trans_lt room)
  have second:=RawTables.any a.board a.rootBits a.depth T a.template
    (Columns.output a.decode a.sides a.source base v.oldLanes (p₀).oldHosts v.oldGroups m)
    (eqn.trans_lt room)
  refine ⟨Procedure.Exec.then first.1 second.1,?_,cheap_seq first.2.2 second.2.1⟩
  rintro i (low|high)
  · exact (second.2.2.2 i (.inl (low.trans_le lo))).trans (first.2.1 i (.inl low))
  · exact (second.2.2.2 i (.inr (eqn.le.trans high))).trans (first.2.1 i (.inr (hi.trans high)))

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
