import OAI.Hierarchy.DescentResetOriginClass
import OAI.Hierarchy.DescentResetRecordedPrimary
import OAI.Hierarchy.DescentResetSpanDispatch

namespace OAI
/-! # The source classification of the physically retained primary at a reached node -/
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
open scoped Classical Fin.CommRing
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "residual" => (Z).k-(T).commonDepth
local notation "view" => bankNode (Z).placement (Z).graph (T).commonDepth (T).code (Z).positive (Z).pay (Z).circuit d
local notation "raw" => W.granular b.count (z*G.b) b.fit

theorem retained_local_ordinal (x : NodeOrder.All next) (y : NodeOrder.All a.bit)
    (owned : names x=Sum.inl y) :
    (order x.1 x.2).val=(oldOrder (fun u : Fibre (T).home ((T).home y.1)=>((split).recipe u.val).Node)
      (who ((T).home y.1)) (fun u=>prior u.val) ⟨⟨y.1,rfl⟩,y.2⟩).val := by
  have rank:=reached_node_rank b hp whole a earlier x
  rw [owned] at rank
  exact rank

theorem fresh_local_ordinal (x : NodeOrder.All next) (donor : NodeOrder.Global prog)
    (owned : names x=Sum.inr (Sum.inr donor)) :
    (order x.1 x.2).val=(fresh donor.1 donor.2).val := by
  have rank:=reached_node_rank b hp whole a earlier x
  rw [owned] at rank
  exact rank

private theorem owner_node (t : (Bool × (Z).Fallback) ⊕ (Z).bank.Site) :
    (b.next.placement.pos (b.reblock.destination (((Z).resetNames T).symm t))).2.val =
      Sum.elim (fun st : Bool × (Z).Fallback =>
        Node.trunk st.1 (DescentRelativeContacts.shortName (T).commonDepth ((T).code st.2))) view t := by
  let site := ((Z).resetNames T).symm t
  have placed : (b.next.placement.pos (b.reblock.destination site)).2=(Z).placed T site :=
    congrArg (fun v=>v.1.2) (ClosedReset.Window.named_home b site)
  exact (congrArg Subtype.val placed).trans (congrArg (Sum.elim (fun st : Bool × (Z).Fallback =>
    Node.trunk st.1 (DescentRelativeContacts.shortName (T).commonDepth ((T).code st.2))) view)
    (((Z).resetNames T).apply_symm_apply t))

theorem retained_shape (x : NodeOrder.All next) (y : NodeOrder.All a.bit)
    (owned : names x=Sum.inl y) : ∃label,((Z).localShape T (b.next.placement.pos x.1).2).val=.trunk false label := by
  have vertex:=reached_node_site b hp whole a x
  rw [owned] at vertex
  rw [←vertex]
  exact ⟨_, congrArg (DescentDenseHostOrder.shape (Z).graph)
    (owner_node b (.inl (false, (T).home y.1)))⟩

theorem fresh_shape (x : NodeOrder.All next) (donor : NodeOrder.Global prog)
    (owned : names x=Sum.inr (Sum.inr donor)) :
    ((Z).localShape T (b.next.placement.pos x.1).2).val=DescentDenseHostOrder.shape (Z).graph (view donor.1) := by
  have vertex:=reached_node_site b hp whole a x
  rw [owned] at vertex
  rw [←vertex]
  exact congrArg (DescentDenseHostOrder.shape (Z).graph) (owner_node b (.inr donor.1))

theorem fresh_excludes_primary (x : NodeOrder.All next) (donor : NodeOrder.Global prog)
    (owned : names x=Sum.inr (Sum.inr donor)) (key₀) :
    ((Z).localShape T (b.next.placement.pos x.1).2).val≠.trunk false key₀ := by
  rw [fresh_shape b hp whole a x donor owned]
  rcases donor with ⟨⟨⟨side,l|r⟩,vtx⟩,node⟩ <;> simp [bankNode,DescentDenseHostOrder.shape]

end
end Hierarchy.DescentPrimitivePalette

end OAI
