import OAI.Hierarchy.DescentMeasuredBankLocation
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentPaidResidentCensus

namespace OAI
/-! # The physical bank actor badge at original and padded gate ordinals -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
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


local notation "nativeSite" site:arg => b.reblock.destination (((Z).resetNames T).symm (.inr site))
local notation "atSite" site:arg => (b.next.placement.pos (nativeSite site)).2

/-- Read the already installed site itself. This continues to identify the host and actor
badge when a requested numeric gate does not exist on that site's program. -/
theorem original_bank_actor (site : (Z).bank.Site) :
    (atSite site).val=view site ∧
    position (Z).graph (atSite site).val=(Z).rootVertex T site.1.2 ∧
    ((Z).localShape T (atSite site)).val=shape (Z).graph (view site) :=by
  have loc:=congrArg (fun t=>t.1.2) (ClosedReset.Window.named_home b (((Z).resetNames T).symm (.inr site)))
  change atSite site=(Z).placed T (((Z).resetNames T).symm (.inr site)) at loc
  rw [loc]
  have at_:=(ClosedReset.Window.root_at_bank_site b site)
  have val₀ : ((Z).placed T (((Z).resetNames T).symm (.inr site))).val=view site:=by
    let read : (Bool×(Z).Fallback) ⊕ (Z).bank.Site → _ := Sum.elim
      (fun st => Node.trunk st.1 (DescentRelativeContacts.shortName (T).commonDepth ((T).code st.2))) view
    exact congrArg read (((Z).resetNames T).apply_symm_apply (.inr site))
  exact ⟨val₀,congrArg Prod.fst at_,congrArg (shape (Z).graph) val₀⟩

open DescentPaidResidentCount

/-- The original compact inverse table decodes the old host and the actual local shape;
its active bit is set at every occupied site even when the gate ordinal is padding. -/
theorem bank_actor_badge {H H₁ : ℕ} (hosts : Fintype.card cap.V≤H) (after : Fintype.card b.next.V≤H₁)
    (site : (Z).bank.Site) (host : Fin H₁) (group : Fin (S.groupCount (i+1))) (block : DescentColonies.Block k)
    (here : occupies b.next.placement (Equiv.refl _) (b.next.vertex.trans (Fin.castLEEmb after)) host group block (nativeSite site)) :
    let rank:=b.frame.host.symm.toEmbedding.trans (cap.vertex.trans (Fin.castLEEmb hosts))
    let uv:=atSite site
    ∃hv : host.val<Fintype.card b.next.V,
      host.val=(b.next.vertex uv).val ∧ actualBit b after host group block=1 ∧
      (Z).rawAtIndex T rank ⟨host.val,hv⟩=finProdFinEquiv ((Z).hostFields T rank uv) ∧
      (Z).localShape T uv=⟨shape (Z).graph (view site),by rw [←(original_bank_actor b site).2.2];exact ((Z).localShape T uv).property⟩ :=by
  dsimp only
  obtain ⟨located,group_,block_⟩:=here
  have at_ : host.val=(b.next.vertex (atSite site)).val:=(congrArg Fin.val located).symm
  have fits : host.val<Fintype.card b.next.V:=by rw [at_];exact (b.next.vertex (atSite site)).isLt
  refine ⟨fits,at_,ite_eq_left ⟨nativeSite site,located,group_,block_⟩,?_,Subtype.ext (original_bank_actor b site).2.2⟩
  let rank:=b.frame.host.symm.toEmbedding.trans (cap.vertex.trans (Fin.castLEEmb hosts))
  have badge : (⟨host.val,fits⟩:Fin (Fintype.card b.next.V))=(Z).denseHostRank T rank (atSite site):=
    Fin.ext (at_.trans (dense_physical b hosts (atSite site)).symm)
  exact (congrArg ((Z).rawAtIndex T rank) badge).trans ((Z).rawAtIndex_at T rank (atSite site))

end
end Hierarchy.DescentPrimitivePalette

end OAI
