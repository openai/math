import OAI.Hierarchy.DescentDatedBeforeSignedMaterial
import OAI.Hierarchy.DescentDatedSignedInput
import OAI.Hierarchy.DescentDatedOrdinaryMark

namespace OAI
/-! # Equal instructions and exact clocks on a common ordinary signed program -/
namespace Hierarchy.DescentDatedAddressBook.SignedProgram
open DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section

def prepared (v : SignedProgram) (parts adj : Bank) (w : ℕ) : NativePhase w :=
  let s:=v.signed
  (PriorHeader.phase v.priorHosts s.groups s.lanes s.degree v.entry adj w).seq
    (v.material.materialAt v.beginAt parts (PriorHeader.reverseRank v.priorHosts s.groups s.lanes s.degree v.entry) w)

def markedPhase (v : SignedProgram) (args : Dated.Operands) (w : ℕ) : NativePhase w :=
  let s:=v.signed
  PhysicalOrdinary.markNative v.marked v.afterPeers
    (PriorHeader.visited v.priorHosts s.groups s.lanes s.degree v.entry) args v.material.setup.hostPitch w

/-- All three instruction sequences, their exact clocks and the returned memory
functions are deterministic functions of the original numerical program and input pointers. -/
theorem signed_eq {v v' : SignedProgram} (same : v=v') (c : v.Chart) (c' : v'.Chart) (w : ℕ) :
    v.signedPhase c w=v'.signedPhase c' w :=by cases same;rfl

end
end Hierarchy.DescentDatedAddressBook.SignedProgram

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem observed_public (floor : ℕ) (parts adj : Bank) (args : Dated.Operands) (w : ℕ) (c : v.SignedChart) :
    let q:=v.signedProgram floor
    v.beforeSignedMaterial floor parts adj w=q.prepared parts adj w ∧
    v.mark floor args w=q.markedPhase args w ∧
    v.signedPhase floor c w=q.signedPhase (v.publicSignedChart floor c) w ∧
    v.signedEnd floor=q.endAddress :=⟨rfl,rfl,rfl,rfl⟩

theorem same_signed_program {F' P' : Type} [Field F'] (other : PhysicalOrdinary F' P')
    (floor floor' : ℕ) (same : v.signedProgram floor=other.signedProgram floor')
    (parts adj : Bank) (args : Dated.Operands) (w : ℕ) (c : v.SignedChart) (c' : other.SignedChart) :
    v.beforeSignedMaterial floor parts adj w=other.beforeSignedMaterial floor' parts adj w ∧
    v.mark floor args w=other.mark floor' args w ∧ v.signedPhase floor c w=other.signedPhase floor' c' w ∧
    v.signedEnd floor=other.signedEnd floor' := by
  obtain ⟨a,b,d,e⟩:=v.observed_public floor parts adj args w c
  obtain ⟨a',b',d',e'⟩:=other.observed_public floor' parts adj args w c'
  exact ⟨a.trans ((congrArg (fun q:SignedProgram=>q.prepared parts adj w) same).trans a'.symm),
    b.trans ((congrArg (fun q:SignedProgram=>q.markedPhase args w) same).trans b'.symm),
    d.trans ((SignedProgram.signed_eq same _ _ w).trans d'.symm),
    e.trans ((congrArg SignedProgram.endAddress same).trans e'.symm)⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
