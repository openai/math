import OAI.Hierarchy.DescentExteriorTokenLedger
import OAI.Hierarchy.DescentSubroundHubCapacity
import OAI.Hierarchy.DescentStageReindex

namespace OAI
/-! # Invariance of the real original exterior fibres on a selected physical subround -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentColonies DescentHostDirectory Computability.BorderVNP.Crossing DescentResetTrunks
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d k a g : ℕ} {I C P V : Type} [Fintype I] [Fintype P] [DecidableEq V]
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


theorem selected_exterior_balance (old : W.HubExterior (hub∘pos)) (same : ∀v,hub (key v).1=mark v) :
    (post).HubExterior postHub := by
  classical
  let image := address sel key hub k g
  let dest : W.graph.Site→(post).graph.Site := fun u=>image (loc u)
  have native := selectedTethers W G pick z hz fit pack p (hub ∘ pos) inc picked packed
  have selectedInc := selected_hubs W G pick z hz fit pack p (hub ∘ pos) inc picked packed
  have merge := coalescedTethers sel key hub k g mark selectedInc same
  have coarseInc := coalesced_hubs sel key hub k g mark selectedInc same
  have postInc := pieces_hubs coarse q m cuts postHub coarseInc
  have path : TetherImage W post dest := (native.comp merge).comp (piecesTethers coarse q m cuts)
  apply HubExterior.map W old inc postInc dest path
  · intro u
    exact (coalesced_at_hub sel key hub k g (loc u)).trans (same (loc u))
  · intro pin
    rfl

omit [Fintype P] in
theorem selected_exterior_owners (owns : ∀pin,hub (pos (W.graph.attach pin))=true)
    (same : ∀v,hub (key v).1=mark v) (pin : P) :
    postHub ((post).graph.attach pin)=true := by
  exact (coalesced_at_hub sel key hub k g (loc (W.graph.attach pin))).trans
    ((same _).trans (owns pin))



end
end Hierarchy.DescentSixParty.MarkedWorld

namespace Hierarchy.DescentSixParty.PhysicalRename
open DescentResetTrunks MarkedWorld
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F d P bits) (s : Equiv.Perm A.graph.Site) (e : Equiv.Perm A.graph.Edge)
omit [Field F] in
theorem hub_balance (h : A.graph.Site→Bool) (old : A.HubExterior h) : (world A s e).HubExterior (h∘s.symm) := by
  rintro v hv
  obtain ⟨u,rfl⟩:=s.surjective v
  have live : h u=true := (congrArg h (s.symm_apply_apply u)).symm.trans hv
  have price := siteUnits A s e h (fun _=>([] : List Unit)) 1 256 0 u
  have amount : (world A s e).exteriorWidth (s u)=A.exteriorWidth u := by
    unfold exteriorWidth bin
    apply Finset.sum_congr rfl
    intro pin _
    change (if s (A.graph.attach pin)=s u then _ else _)=_
    rw [s.injective.eq_iff]
  rw [amount,←old u live]
  exact price

end
end Hierarchy.DescentSixParty.PhysicalRename

end OAI
