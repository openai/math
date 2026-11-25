import OAI.Hierarchy.DescentResetEmittedArgument
import OAI.Hierarchy.DescentResetEmittedFirstCable

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite


open DescentResetSignedScan DescentNextSignedWindow DescentNextSignedWindow.Native DescentOperandStateBanks
open DescentSharedCableNames
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

def faceCable (v : B.reblock.result.graph.Site) (host : Host) (face : Roster.Face A ord (blocks B) host)
    (home : (if face.val.2 then (coarse).graph.dst face.val.1 else (coarse).graph.src face.val.1)=(hop).symm v) :
    Incident (coarse).graph ((hop).symm v) := ⟨face.val.1,by
  cases sign : face.val.2
  · exact Or.inl (by simpa [sign] using home)
  · exact Or.inr (by simpa [sign] using home)⟩

/-- The actual live candidate selected by the authored gate is the pointer of
its original indexed operand after reblocking and renaming. -/
theorem registered_face_pointer (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (j : ℕ)
    (host : Host) (face : Roster.Face A ord (blocks B) host) (word : ℕ)
    (fits : (word+1)*p≤(coarse).graph.width face.val.1) (inside : word/unit<(blocks B).count face.val.1)
    (home : (if face.val.2 then (coarse).graph.dst face.val.1 else (coarse).graph.src face.val.1)=(hop).symm x.1)
    (read : (((installed).sites ((hop).symm x.1)).keys x.2)[j]?=
      some (.inl ⟨.inl (faceCable B x.1 host face home),word,fits⟩)) :
    let u:=referencedUnit B host face unit word inside
    let child:=Stage.live A ord S B.next.valid (fieldNames B) host (DescentParallelBase.GrainPorts.port A ord (blocks B) host u)
    let chunk:=if face.val.1∈(coarse).core then word%unit else word
    Reached.argumentPointer B.next next_ rank after_ hp pin args x j=
      Pointer.cable child.neighbor.val (child.wire.val-child.within.val) chunk :=by
  intro u child chunk
  obtain ⟨e,fit,emitted,atSite,same⟩:=emitted_argument B hp one pos whole wide a sh rank pin args x j
    (faceCable B x.1 host face home) word fits inside read face.val.2 home
  exact same.trans (emitted_first_cable B hp host u x.1 e chunk fit emitted atSite).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
