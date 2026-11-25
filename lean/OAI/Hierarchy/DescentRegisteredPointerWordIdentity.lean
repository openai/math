import OAI.Hierarchy.DescentRegisteredPointerOrigins
import OAI.Hierarchy.DescentOperandLaneRead

namespace OAI
/-! Resolution is determined by the numeral on the native operand shelf. -/
namespace Hierarchy.DescentSixParty.Reached
open Chronology DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentPacking
open DescentDatedAddressBook DescentOperandStateBanks DescentDatedPriorOperand DescentPackedOperand
open DescentLocalPrivateNames Computability.BorderVNP.Crossing
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {dim k i z D wire hist p R:ℕ} {bits:P→ℕ} {U:MarkedWorld F dim P bits}
    {G:PoweredGadget F} {q ε:ℝ} {S:DescentCompiler.AtomSchedule}
    (r:Reached U G q ε S k i z D wire hist) (cpu:PhysicalOrdinary F P)
    (B:BitDescription U) (number:Local B) (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
    (jobs:Fin cpu.resolver.jobs→DescentDatedPriorOperand.Source cpu.resolver)
/-- Two source descriptions read through the same packed register yield the same
resolved key in every valid lane, including all five key fields. -/
theorem PointerSites.of_same_words
    {w:ℕ} (floor:ℕ) (m:Memory w)
    {other:Fin cpu.resolver.jobs→DescentDatedPriorOperand.Source cpu.resolver}
    (left:∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((jobs j).compiled h g)) cpu.resolver.lanes m)
    (right:∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((other j).compiled h g)) cpu.resolver.lanes m)
    (width:outputWidth cpu.resolver.size*cpu.resolver.lanes≤w) (positive:0<cpu.resolver.lanes)
    (from_:PointerSites r cpu B number shape hp pin jobs) : PointerSites r cpu B number shape hp pin other:=by
  have readKeys (j:Fin cpu.resolver.jobs) h g :
      resolve ((other j).compiled h g)=resolve ((jobs j).compiled h g):=by
    let addr:=(Banks.wordBank cpu.resolver floor j).base
    have one:=DescentOperandStateBanks.Reset.lane_read addr _ m (left j) width positive h g
    have two:=DescentOperandStateBanks.Reset.lane_read addr _ m (right j) width positive h g
    have same:=two.symm.trans one
    apply Key.fields_injective
    funext f
    exact (word_read _ f).symm.trans ((congrArg (digit (cpu.resolver.size+4) f.val) same).trans (word_read _ f))
  intro u block host group hx hh hg nodes args
  obtain ⟨⟨hidden,keys⟩,cable,port⟩:=from_ u block host group hx hh hg nodes args
  have same (j):resolve (cpu.issuedFragment other block host group j)=resolve (cpu.issuedFragment jobs block host group j):=
    readKeys _ host group
  refine ⟨⟨hidden,⟨?_,keys.privateTag,?_⟩⟩,?_,?_⟩
  · intro slot a read
    exact (same _).trans (keys.privateRead slot a read)
  · intro slot vacant
    exact (same _).symm ▸ keys.publicTag slot vacant
  · intro n j e a enough found
    exact (congrArg (Pointer.ofKey 0) (same _)).trans (cable n j e a enough found)
  · intro n j e a enough found
    exact (same _).trans (port n j e a enough found)

/-- A native reader may use any descriptions which have actually produced the
same numeric keys at the same hardware addresses. -/
theorem PointerSites.from_words {w:ℕ} {floor:ℕ} {m:Memory w} {Q:Prop}
    (emit:PointerSites r cpu B number shape hp pin jobs→Q)
    (printed:∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((jobs j).compiled h g)) cpu.resolver.lanes m)
    (width:cpu.resolver.lanes*DescentPackedOperand.unit cpu.resolver.size≤w/2) (positive:0<cpu.resolver.lanes)
    (source:∃other:Fin cpu.resolver.jobs→DescentDatedPriorOperand.Source cpu.resolver,
      (∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((other j).compiled h g)) cpu.resolver.lanes m) ∧
      PointerSites r cpu B number shape hp pin other) : Q:=by
  obtain ⟨other,written,known⟩:=source
  have digits:outputWidth cpu.resolver.size≤DescentPackedOperand.unit cpu.resolver.size:=by unfold outputWidth DescentPackedOperand.unit;omega
  have packed:outputWidth cpu.resolver.size*cpu.resolver.lanes≤w:=
    (Nat.mul_le_mul_right _ digits).trans (by simpa only [Nat.mul_comm] using width.trans (Nat.div_le_self w 2))
  exact emit (PointerSites.of_same_words r cpu B number shape hp pin other floor m written printed packed positive known)

private theorem samePointerModel {old new : PhysicalOrdinary F P} (eqn : old = new)
    {left : Fin old.resolver.jobs → DescentDatedPriorOperand.Source old.resolver}
    {right : Fin new.resolver.jobs → DescentDatedPriorOperand.Source new.resolver}
    (same : HEq left right) (ready : PointerSites r old B number shape hp pin left) :
    PointerSites r new B number shape hp pin right := by
  subst new
  have eqJobs : left = right := eq_of_heq same
  subst right
  exact ready

theorem PointerSites.from_signed_words {w:ℕ} {floor:ℕ} {m:Memory w} {Q:Prop}
    (emit:PointerSites r cpu B number shape hp pin jobs→Q)
    (printed:∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((jobs j).compiled h g)) cpu.resolver.lanes m)
    (width:cpu.resolver.lanes*DescentPackedOperand.unit cpu.resolver.size≤w/2) (positive:0<cpu.resolver.lanes)
    (fixed:cpu.withIssuedSigned=cpu)
    (source:∃other:Fin cpu.resolver.jobs→DescentDatedPriorOperand.Source cpu.resolver,
      (∀j,Reads (Banks.wordBank cpu.resolver floor j) (fun h g=>word ((other j).compiled h g)) cpu.resolver.lanes m) ∧
      PointerSites r cpu.withIssuedSigned B number shape hp pin other) : Q:=by
  obtain ⟨other,read,known⟩:=source
  apply PointerSites.from_words r cpu B number shape hp pin jobs emit printed width positive
  refine ⟨other,read,?_⟩
  exact samePointerModel r B number shape hp pin fixed HEq.rfl known

end
end Hierarchy.DescentSixParty.Reached

end OAI
