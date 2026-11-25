import OAI.Hierarchy.DescentResetOriginRangeShape
import OAI.Hierarchy.DescentPrivateLocalRoster
import OAI.Hierarchy.DescentResetPeerOldSelfWord

namespace OAI
/-! # The old host and remixed root of any newly installed operation -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (resetMenu b)
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "oldId" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "who" => (fun t=>(b.reset.homeTicket b.terminals oldId t).trans Fin.valEmbedding)
local notation "prior" => (fun v=>(earlier v).toEmbedding.trans Fin.valEmbedding)
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open DescentSIMDLookup DescentResetActorClass DescentCommonHost
open scoped Fin.CommRing
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "residual" => (Z).k-(T).commonDepth
local notation "view" => bankNode (Z).placement (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d
local notation "raw" => W.granular b.count (z*G.b) b.fit


open DescentSixParty.ClosedReset.Window DescentSharedCableNames DescentIssuedFallbackPanel
open DescentResetStemWord DescentResetStemCompactOrder DescentDenseHostOrder

/-- Both physical coordinates come from the installed bank at the very site retained
by the origin classifier.  This applies to gates on empty or padded public columns. -/
theorem fresh_bank_location (x : NodeOrder.All next) (donor : NodeOrder.Global prog)
    (owned : names x=.inr (.inr donor)) :
    receiverRoot b (Stage.home b.next.placement x.1)=
      ((Z).rootVertex T donor.1.1.2,(Z).rootBlock T donor.1.1.2) :=by
  let st:=chosenOwner b hp whole a (.inr (.inr donor))
  have site:=reached_node_site b hp whole a x
  rw [owned] at site
  rw [←site]
  exact ((congrArg (receiverRoot b) (named_home b st)).trans (receiverRoot_site b st)).trans
    (root_at_bank_site b donor.1)

/-- On the actual occupied compact actor row, the old self word names the
preceding vertex of the installed bank. Its address uses the returned node site. -/
theorem fresh_bank_self {H₁ : ℕ} (pad : Fintype.card b.next.V≤H₁)
    (x : NodeOrder.All next) (donor : NodeOrder.Global prog) (owned : names x=.inr (.inr donor)) :
    let u:=(b.next.placement.pos x.1).2
    let v:=b.frame.host.symm ((Z).rootVertex T donor.1.1.2)
    stemSelfDigit b (originalTrunkRack b) ((b.next.vertex u).castLE pad)=
      hostCode (compress (hostDomain cap.placement cap.vertex v) (cap.vertex v).val)
        (decide (v∉cap.placement.near v)) :=by
  let u:=(b.next.placement.pos x.1).2
  have active : ((b.next.vertex u).castLE pad).val<Fintype.card b.next.V:=(b.next.vertex u).isLt
  have rack : originalTrunkRack b ((b.next.vertex u).castLE pad)=some u:=by
    simp only [originalTrunkRack, active, ↓reduceDIte]
    exact congrArg some ((denseOrder b).symm_apply_apply u)
  have whereOld:=congrArg Prod.fst (fresh_bank_location b hp whole a x donor owned)
  change position (Z).graph u.val=(Z).rootVertex T donor.1.1.2 at whereOld
  change stemSelfDigit b (originalTrunkRack b) ((b.next.vertex u).castLE pad) = _
  unfold stemSelfDigit
  rw [rack]
  simp only [Option.elim_some,stemOldHost,whereOld]

/-- The printed 'group times radix plus block' is literally the coarse prefix
of this bank. All numeric groups include the original final partial group. -/
theorem fresh_bank_coarse (x : NodeOrder.All next) (donor : NodeOrder.Global prog)
    (owned : names x=.inr (.inr donor)) :
    (b.next.placement.pos x.1).1.val*2^k+(b.next.placement.block x.1).val=
      ((Z).rootBlock T donor.1.1.2).val :=by
  have res:=congrArg (fun z=>z.2.val) (fresh_bank_location b hp whole a x donor owned)
  change (b.next.placement.block x.1).val+2^k*(b.next.placement.pos x.1).1.val=_ at res
  simpa only [Nat.add_comm, Nat.mul_comm] using res

end
end Hierarchy.DescentPrimitivePalette

end OAI
