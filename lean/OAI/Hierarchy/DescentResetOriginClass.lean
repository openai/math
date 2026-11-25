import OAI.Hierarchy.DescentResetOriginRank
import OAI.Hierarchy.DescentResetHeaderPlacement
import OAI.Hierarchy.DescentResetActorClassIssued

namespace OAI
/-! # Class of the genuine primary, relay, or bank operand on the reached reset -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
set_option quotPrecheck false
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

/-- The operation's class is a function of its installed rotor or fallback site
for a fresh bank. Retained primitive and relay records have dedicated classes. -/
def originClass : (NodeOrder.All a.bit ⊕ ((raw).graph.Edge⊕NodeOrder.Global prog))→Cell (indexBits (Z).n residual)
  | .inl _=>1
  | .inr (.inl _)=>2
  | .inr (.inr bank)=>DescentResetActorClass.indexed (Z).graph residual (view bank.1)

private theorem reached_owner_host (s : ((Z).orderedReentry T key).graph.Site) :
    (b.next.placement.pos (b.reblock.destination s)).2=(Z).placed T s:=by
  exact congrArg (fun v=>v.1.2) (ClosedReset.Window.named_home b s)

theorem installed_origin_class (j : NodeOrder.All a.bit ⊕ ((raw).graph.Edge⊕NodeOrder.Global prog)) :
    DescentResetActorClass.indexed (Z).graph residual (b.next.placement.pos (b.reblock.destination (chosenOwner b hp whole a j))).2.val=
      originClass b hp whole a j:=by
  refine (congrArg (fun v : b.next.V => DescentResetActorClass.indexed (Z).graph residual v.val)
    (reached_owner_host b (chosenOwner b hp whole a j))).trans ?_
  let decode := Sum.elim (fun st : Bool × (Z).Fallback =>
    Node.trunk st.1 (DescentRelativeContacts.shortName (T).commonDepth ((T).code st.2))) view
  have named (t : (Bool × (Z).Fallback) ⊕ (Z).bank.Site) :
      ((Z).placed T (((Z).resetNames T).symm t)).val = decode t :=
    congrArg decode (((Z).resetNames T).apply_symm_apply t)
  rcases j with donor | relay | bank
  · exact congrArg (DescentResetActorClass.indexed (Z).graph residual)
      (named (.inl (false,(T).home donor.1)))
  · exact congrArg (DescentResetActorClass.indexed (Z).graph residual)
      (named (.inl (true,DescentResetTrunks.moved (raw).graph (T).home relay)))
  · exact congrArg (DescentResetActorClass.indexed (Z).graph residual) (named (.inr bank.1))

theorem origin_index (x : NodeOrder.All next) :
    DescentResetActorClass.indexed (Z).graph residual ((b.next.placement.pos x.1).2).val=originClass b hp whole a (names x):=by
  exact (congrArg (fun v=>DescentResetActorClass.indexed (Z).graph residual (b.next.placement.pos v).2.val)
    (reached_node_site b hp whole a x)).symm.trans (installed_origin_class b hp whole a (names x))

/-- The numerical actor directory used by the real checkpoint contains this
operation's class at the operation's own dense host. -/
theorem checkpoint_origin_index {H : ℕ} (fitHosts : Fintype.card b.next.V≤H) (x : NodeOrder.All next) :
    (ClosedReset.Window.paidActorAt b ((b.next.vertex (b.next.placement.pos x.1).2).castLE fitHosts)).elim 0
      (fun v=>DescentResetActorClass.indexed (Z).graph residual v.val)=originClass b hp whole a (names x):=by
  rw [ClosedReset.Window.paidActorAt_known b fitHosts]
  exact origin_index b hp whole a x

end
end Hierarchy.DescentPrimitivePalette

end OAI
