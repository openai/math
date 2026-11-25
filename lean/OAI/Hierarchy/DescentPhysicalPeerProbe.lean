import OAI.Hierarchy.DescentPhysicalResetSceneRead
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The genuine reset peer catalogue is read after the subsequent public passes -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentResetPeerUnionRAM DescentResetStemKey DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable (v : CandidateFront) (base : ℕ) (s : v.Scene) {w : ℕ} (safe : v.SceneRoom base s w)
local notation "A" => v.contactLayout base
local notation "L" => v.rawTables base
local notation "P" => v.peer
local notation "E" => s.evidence
local notation "U" => s.peers
local notation "T" => v.peers base

def probeStart (m : Memory w) :=
  Columns.output (E).decode (E).sides (E).source base v.oldLanes (P).oldHosts v.oldGroups m

def probeProgram : Procedure w :=
  (((RawTables.program (E).board (E).rootBits (E).depth L (E).template w).seq
    (v.donorPhase base s safe).program).seq (v.contactPhase base s safe).program).seq
    (Program.program w T (P).oldHosts (P).shapes (P).oldDegree (P).bits (P).evidenceLanes
      (P).evidenceGroups (U).old (U).test (U).src)

def probeMemory (m : Memory w) :=
  Program.output T (P).oldHosts (P).shapes (P).oldDegree (P).bits (P).evidenceLanes
    (P).evidenceGroups (U).old (U).test (U).src (v.prePeers base s safe m)

theorem probe_exec (m : Memory w) :
    ∃ticks,(v.probeProgram base s safe).Exec (v.probeStart base s m) (v.probeMemory base s safe m) ticks := by
  have range:=v.tables_end base safe.sameLanes
  have raw:=RawTables.any (E).board (E).rootBits (E).depth L (E).template
    (v.probeStart base s m) (range.trans_lt safe.evidenceFit)
  have donor:=v.donor.any (v.donorStart base) s.donor safe.donor (v.preDonors base s safe m)
  have contact:=(A).any s.rotor s.boardReads (v.sensor base s) safe.contact (v.preContacts base s safe m)
  have heard:=Program.any (U).old (U).test (U).src safe.peers.old (v.prePeers base s safe m)
  exact ⟨_,Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then raw.1 donor.1) contact.1) heard.1⟩

/-- Equality concerns only the two fixed procedures, so determinism identifies the native
image of the issued catalogue even if its successful run is stated at a different clock. -/
theorem observed_peers (m out : Memory w) {code : Procedure w} {ticks : ℕ}
    (program : code=v.probeProgram base s safe)
    (observed : code.Exec (v.probeStart base s m) out ticks)
    (property : (Fin (P).hosts→Fin 3→Option (Fin (P).hosts))→Prop)
    (values : ∃rows,(∀(h : Fin (P).hosts) (j : Fin 3),out ((P).rawPeers T+j.val*(P).hosts+h.val)=
       (DescentPackedExchange.target (rows h j):Word w)) ∧ property rows) :
    ∃rows,(∀(h : Fin (P).hosts) (j : Fin 3),v.preScalar base s safe m ((P).rawPeers T+j.val*(P).hosts+h.val)=
      (DescentPackedExchange.target (rows h j):Word w)) ∧ property rows := by
  subst code
  obtain ⟨_,ran⟩:=v.probe_exec base s safe m
  have same:=exec_unique _ _ _ _ observed ran
  subst out
  exact v.preScalar_peers base s safe m property values

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
