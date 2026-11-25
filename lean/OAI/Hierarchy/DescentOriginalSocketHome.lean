import OAI.Hierarchy.DescentRegisteredSocketKeys
import OAI.Hierarchy.DescentClosedLocalRoster

namespace OAI
/-! # Recovering the original site of a reached socket using the paid host and block -/
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
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse

open DescentSharedCableNames DescentParallelBase DescentNextSignedWindow DescentOperandStateBanks
local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "present" x => (installed).sites ((hop).symm x.1)
local notation "result" rank pin args x j => Reached.argumentPointer B.next next_ rank after_ hp pin args x j

local notation "before_" => BitDescription.granular W B.count (z*G.b) B.fit a.bit
local notation "pre_" => (before_).batchedReset B.reset B.terminals birth unit p hp splitEq (resetMenu B)
local notation "middle_" x => NodeOrder.followNames B.reblock pre_ x
open DescentSIMDLookup DescentOperandCandidateLookup DescentDatedAddressBook.ResetOutput DescentResetOperandComponents
local notation "pubCfg" b q l bat nd ar gr => publicOperandConfig B b q l bat unit nd ar gr

/-- A face of the original roster recovers the unrenamed endpoint from its physical home. -/
theorem PublicSocket.original_site {h₀ : Host} {word number : ℕ} {tag : Bool}
    {units : ℕ} (socket : PublicSocket B h₀ units word tag number)
    (y : B.reblock.result.graph.Site) (live : h₀=DescentSharedCableNames.Stage.home B.next.placement y) :
    (if socket.face.val.2 then (coarse).graph.dst socket.face.val.1 else (coarse).graph.src socket.face.val.1)=(hop).symm y:=by
  apply same_site B
  apply Eq.trans ?_ (congrArg (DescentSharedCableNames.Stage.home B.next.placement) ((hop).apply_symm_apply y)).symm
  have actual:=socket.face.property.2.trans live
  cases side:socket.face.val.2 <;>simp only [side,Bool.false_eq_true,ite_false,ite_true] at actual ⊢ <;>exact actual

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
