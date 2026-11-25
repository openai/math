import OAI.Hierarchy.DescentClosedDeviceArgumentKeys
import OAI.Hierarchy.DescentResetRegisteredFacePointer

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

open DescentResetFreshWires DescentResetLocalNodes DescentOrderedWords
local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x:arg => NodeOrder.followNames B.reblock pre_ x

open DescentLaneGates

open DescentSharedCableNames
open DescentResetSignedScan DescentNextSignedWindow DescentNextSignedWindow.Native DescentOperandStateBanks
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "A₀" => B.next.placement
local notation "ord₀" => B.next.order.trans Fin.valEmbedding

/-- At the face printed by the socket, the named pointer is the registered
neighbor, first wire number, and reblocked chunk of the same original word. -/
theorem keyed_face_pointer (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (slot : ℕ)
    (host : Host) (face : Roster.Face A₀ ord₀ (blocks B) host) (word : ℕ)
    (fit : (word+1)*p≤(coarse).graph.width face.val.1) (inside : word/unit<(blocks B).count face.val.1)
    (home : (if face.val.2 then (coarse).graph.dst face.val.1 else (coarse).graph.src face.val.1)=(hop).symm x.1)
    (issued : keyCable installed (middle_ x) slot=some (face.val.1,word)) :
    let u:=referencedUnit B host face unit word inside
    let child:=Stage.live A₀ ord₀ S B.next.valid (fieldNames B) host (DescentParallelBase.GrainPorts.port A₀ ord₀ (blocks B) host u)
    Reached.argumentPointer B.next next_ rank after_ hp pin args x slot=
      Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
        (if face.val.1∈(coarse).core then word%unit else word) :=by
  exact registered_face_pointer B hp one pos whole wide a sh rank pin args x slot host face word fit inside home
    (keyCable_read installed (middle_ x) slot (faceCable B x.1 host face home) word fit issued)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
