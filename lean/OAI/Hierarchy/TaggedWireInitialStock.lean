import OAI.Hierarchy.TaggedWirePayload
import OAI.Hierarchy.TaggedWireMatching
import OAI.Hierarchy.TaggedWireBoardLayout

namespace OAI
/-! # Initial payload and catalyst stock on the literal core-board endpoints -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe TaggedPrune Tagged Catalyst WireTelescope
open scoped Classical BigOperators

variable {h d k w K : ℕ} {b : Fin k → ℕ}

def reserveAt (column : Wire b → Columns h d) (v : Wire b) : Columns h d × Fin k :=
  (column v,v.1)

def initialReserve (column : Wire b → Columns h d) (c : Columns h d × Fin k) :=
  Fintype.card {v : Wire b // reserveAt column v=c}

def initialGoods (h d k w : ℕ) : Commodity (Fin (2^h)) (Stages h d) k → ℕ :=
  Sum.elim (fun _=>w) (fun _=>0)

def initialSite (place : Site h d k → Fin K) (column : Wire b → Columns h d) :
    RoutingPin h w b → Fin K
  | .inl ((i,_),false) => place (.inl i,none)
  | .inl ((i,_),true) => place (.inr (.inr i),none)
  | .inr (v,side) => place (column v,some (v.1,side))

theorem outer_routing (place : Site h d k → Fin K) (column : Wire b → Columns h d) :
    outerPort (w:=w) place column ∘ routingPort = initialSite place column := by
  funext pin
  rcases pin with ⟨⟨i,j⟩,s⟩|⟨v,s⟩
  · cases s <;> simp [Function.comp_apply,routingPort,outerPort,initialSite]
  · rfl

private theorem sum_allocated {I J : Type} [Fintype I] [Fintype J] (owner : I → J)
    (term : J → Widths K) :
    (∑ i,term (owner i)) = ∑ j,Fintype.card {i : I // owner i=j} • term j := by
  simpa only [Finset.sum_const, Finset.card_univ] using
    (Fintype.sum_fiberwise' owner term).symm

theorem initial_width (p : Equiv.Perm (Row h)) (place : Site h d k → Fin K) (column : Wire b → Columns h d) :
    (matchGraph p (initialSite (w:=w) place column)).chordWidths (fun _=>1) =
      (commodityGraph p.symm place).chordWidths (initialGoods h d k w) +
        (catalystGraph place).chordWidths (initialReserve column) := by
  simp only [PortGraph.chordWidths,Fintype.sum_sum_type,chordWidth_scaled,one_smul,initialGoods,
    Sum.elim_inl,Sum.elim_inr,zero_smul,Finset.sum_const_zero,add_zero]
  congr 1
  · let wire (i : Row h) := w • pairWidth (place (.inl i,none)) (place (.inr (.inr (p.symm i)),none))
    have equal := Equiv.sum_comp p wire
    rw [Fintype.sum_prod_type]
    simpa [wire,commodityGraph,commodityEnds,matchEnd,matchGraph,initialSite] using equal
  · exact sum_allocated (reserveAt column) (fun c=>pairWidth ((catalystGraph place).tail c) ((catalystGraph place).head c))

/-- Each source bit has precisely one path to its target. In the routing
tensor the permutation is read target-to-source, so the core-board path
uses its inverse. Reserve counts are exact fiber cardinalities on the
actual axis and the column of each public exposed catalyst bit. -/
theorem initial_stock {F : Type*} [Field F] [Nonempty (Fin K)]
    (p : Equiv.Perm (Row h)) (place : Site h d k → Fin K) (column : Wire b → Columns h d) :
    ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (initialSite (w:=w) place column)).Restricts
      (raw F ((commodityGraph p.symm place).chordWidths (initialGoods h d k w) +
        (catalystGraph place).chordWidths (initialReserve column))) := by
  rw [←initial_width (w:=w) p place column]
  exact matching_restricts p _


/-- Exact public starting stock for the calendar's uniform reserve. -/
theorem initial_uniform {F : Type*} [Field F] [Nonempty (Fin K)]
    (p : Equiv.Perm (Row h)) (place : Site h d k → Fin K) (R w : ℕ) :
    let column := fun v : ReserveBits h d k R=>(reserveLocation h d k R v).1
    ((CorrectionProducts.raw (routingMatch (F:=F) p)).group
      (initialSite (b:=fun _ : Fin k=>Fintype.card (Columns h d)*R) (w:=w) place column)).Restricts
      (raw F ((commodityGraph p.symm place).chordWidths (initialGoods h d k w) +
        (catalystGraph place).chordWidths (fun _=>R))) := by
  let column := fun v : ReserveBits h d k R=>(reserveLocation h d k R v).1
  have fiber : initialReserve (b:=fun _ : Fin k=>Fintype.card (Columns h d)*R) column = fun _=>R := by
    funext c
    change Fintype.card {v : ReserveBits h d k R // reserveLocation h d k R v=c}=R
    exact reserve_fiber h d k R c
  have init := initial_stock (F:=F) (w:=w) (b:=fun _ : Fin k=>Fintype.card (Columns h d)*R) p place column
  simpa only [fiber] using init

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
