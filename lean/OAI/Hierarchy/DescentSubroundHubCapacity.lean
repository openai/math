import OAI.Hierarchy.DescentSaturatedHubLedger

namespace OAI
/-! # The saturated external coefficient in the literal next-subround graph -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentColonies DescentHostDirectory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d k a g : ℕ} {I C P V : Type} [Fintype I] [DecidableEq V]
variable {bits : P→ℕ} (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (pick : I×Fin 2 ↪ W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k) (hub : V→Bool)
variable (inc : HubIncidence W (hub ∘ pos)) (picked : ∀t,pick t∈W.core)
variable (packed : ∀u v,pack u=pack v→(hub ∘ pos) u=(hub ∘ pos) v)
local notation "sel" => W.selected G pick z hz fit pack p
local notation "mark" => selectedHub W G pick z hz fit pack p (hub ∘ pos) inc picked packed
local notation "loc" => (fun u : W.graph.Site=>newSite W.graph pick (bestLayout (branchWidth G z p)) pack (Sum.inl u))
variable (key : (W.selected G pick z hz fit pack p).graph.Site → Key V)
local notation "coarse" => coalesced sel key hub k g
variable (q : ℕ)
variable (m : (coalesced (W.selected G pick z hz fit pack p) key hub k g).graph.Edge → ℕ)
variable (cuts : ∀ e : (coalesced (W.selected G pick z hz fit pack p) key hub k g).graph.Edge,
  e ∈ (coalesced (W.selected G pick z hz fit pack p) key hub k g).core →
    (coalesced (W.selected G pick z hz fit pack p) key hub k g).graph.width e = m e * q)
local notation "post" => pieces coarse q m cuts
local notation "postHub" => coalescedHub sel key hub k g

/-- Each actual hub in the graph after installing the selected motifs, grouping the external
stacks, and splitting all marked cables has the full next capacity. Only the identities of
its pre-merge address and old load enter the proof; its final incident cables are counted. -/
theorem selected_coalesced_pieces_hub {Aty Bty : Type*}
    (old : W.graph.Site→List Aty) (after : (post).graph.Site→List Bty) (wire β hist B : ℕ)
    (oldEmpty : ∀u,hub (pos u)=true→ old u=[]) (newEmpty : ∀u,postHub u=true→after u=[])
    (same : ∀v,hub (key v).1=mark v)
    (row : ∀u,hub (pos u)=true→(key (loc u)).1=pos u)
    (prefixKey : ∀u,hub (pos u)=true→(key (loc u)).2.1=(k-a,group (k-a) (ix u)))
    (ag : a≤g) (gk : g≤k)
    (filled : ∀v,hub v=true→∀j,StarKeys.blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) old wire β hist) v j=B)
    (v : (post).graph.Site) (yes : postHub v=true) :
    (post).siteUnits postHub after wire β hist v=2^g*B := by
  classical
  let image := address sel key hub k g
  let dest : W.graph.Site→(post).graph.Site := fun u=>image (loc u)
  have native := selectedTethers W G pick z hz fit pack p (hub ∘ pos) inc picked packed
  have selectedInc := selected_hubs W G pick z hz fit pack p (hub ∘ pos) inc picked packed
  have merge := coalescedTethers sel key hub k g mark selectedInc same
  have coarseInc := coalesced_hubs sel key hub k g mark selectedInc same
  have postInc := pieces_hubs coarse q m cuts postHub coarseInc
  have path : TetherImage W post dest := (native.comp merge).comp (piecesTethers coarse q m cuts)
  have sameHub (u : W.graph.Site) : hub (dest u).val.1 = hub (pos u) := by
    exact (coalesced_at_hub sel key hub k g (loc u)).trans (same (loc u))
  have sameKey (u : W.graph.Site) (hu : hub (pos u)=true) :
      (dest u).val = (pos u,(k-g,group (k-g) (ix u)),0) := by
    have h : hub (key (loc u)).1=true := (same (loc u)).trans hu
    have out := coalesced_hub_address sel key hub k g ag gk (loc u) h (ix u) (prefixKey u hu)
    exact out.trans (congrArg (fun w=>(w,(k-g,group (k-g) (ix u)),0)) (row u hu))
  have realized : ∃ u, dest u=v := by
    obtain ⟨t,_,eqn⟩ := Finset.mem_image.mp v.property
    obtain ⟨u,rfl⟩ := old_surjective W.graph pick (bestLayout (branchWidth G z p)) pack t
    exact ⟨u,Subtype.ext eqn⟩
  exact path.saturated_hub pos ix hub (fun t=>t.val) Subtype.val_injective inc postInc
    old after wire β hist B oldEmpty newEmpty sameHub gk sameKey filled v yes realized

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
