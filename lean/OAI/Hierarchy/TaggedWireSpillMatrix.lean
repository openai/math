import OAI.Hierarchy.TaggedWireSpillRowOrder
import OAI.Hierarchy.TaggedWireCoreMatrix
import OAI.Hierarchy.TaggedWireReportOrder
import OAI.Hierarchy.TaggedWireWidthRebase
import OAI.Hierarchy.TaggedWireRepairStock

namespace OAI
/-! # The deterministic equality gates for the cap and escrow transfer -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : PurchaseSampler} {h d k K edges r : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)

namespace Mount

include inj in
theorem spill_off_loop (bits : Commodity (Fin (2^h)) (Stages h d) k→ℕ) (e : Fin edges)
    (loop : B.actual.tail e=B.actual.head e) : routeLoad B.ordinary bits e=0 := by
  unfold routeLoad
  apply Finset.sum_eq_zero
  intro i _
  have absent : e ∉ B.ordinary i := by
    rintro mem
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp mem
    rw [B.tail,B.head] at loop
    exact inj.ne (different π a) loop
  simp [List.count_eq_zero.mpr absent]

def onlySpill (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges))) :
    SiteMatrix (State ((commodityGraph π place).chordWidths spill))
      (State (B.actual.chordWidths (routeLoad B.ordinary spill))) F := by
  let L := B.datedLayout inj pad
  have root : installedWidths L.family (L.bits spill)=(commodityGraph π place).chordWidths spill := L.installed spill
  have tally : routeLoad L.routes (L.bits spill)=routeLoad B.ordinary spill := funext (L.measured spill)
  have paid : installedWidths L.edge (routeLoad L.routes (L.bits spill))=
      B.actual.chordWidths (routeLoad B.ordinary spill) := by
    rw [tally]
    exact filled_width _ pad _ (B.spill_off_loop inj spill)
  exact rebase root paid (L.operator spill (L.nativeOrder enum))

theorem onlySpill_action (spill : Commodity (Fin (2^h)) (Stages h d) k→ℕ)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (v : ∀s,State ((commodityGraph π place).chordWidths spill) s) :
    (raw F _).coeff v=SiteMatrix.act (B.onlySpill inj pad spill enum) (raw F _).coeff v := by
  unfold onlySpill
  apply rebase_action
  intro z
  apply chordRouter_action

end Mount

namespace LedgerStep
variable {I : Type} [Fintype I] (G : PortGraph (Fin K) I)

theorem held_split (old active held kept spill : I→ℕ)
    (balanced : ∀i,old i+active i=held i+kept i+spill i) :
    G.chordWidths old+G.chordWidths active=(G.chordWidths held+G.chordWidths kept)+G.chordWidths spill := by
  simp only [←chordWidths_add]
  exact congrArg G.chordWidths (funext balanced)

variable {A B : Widths K} (R : SiteMatrix (State A) (State B) F)
  (rewrite : ∀v,(raw F A).coeff v=SiteMatrix.act R (raw F B).coeff v)

def carry (other : Widths K) := productTable (SiteMatrix.identity (F:=F) (State other)) R

include rewrite in
theorem carry_action (other : Widths K) (v : ∀s,State (other+A) s) :
    (raw F (other+A)).coeff v=SiteMatrix.act (carry R other) (raw F (other+B)).coeff v := by
  let left (i : Fin K) : State other i := (splitPortState other A i (v i)).1
  let right (i : Fin K) : State A i := (splitPortState other A i (v i)).2
  let keep := SiteMatrix.identity (F:=F) (State other)
  calc
    _ = (raw F other).coeff left*(raw F A).coeff right := raw_add_coeff F other A v
    _ = SiteMatrix.act keep (raw F other).coeff left*SiteMatrix.act R (raw F B).coeff right :=
      congrArg₂ (·*·) (SiteMatrix.act_id (B:=State other) (raw F other).coeff left).symm (rewrite right)
    _ = _ := productTable_action keep R v

/-- All stored payload, half-inventory, and carried installed rows remain
physical identities. Only the clipped excess is routed over its fixed walk. -/
def matrix (carried : Widths K) (old active held kept spill : I→ℕ)
    (balanced : ∀i,old i+active i=held i+kept i+spill i)
    (R : SiteMatrix (State (G.chordWidths spill)) (State B) F) :
    SiteMatrix (State (carried+G.chordWidths old+G.chordWidths active))
      (State ((carried+G.chordWidths held+G.chordWidths kept)+B)) F :=
  let one := held_split G old active held kept spill balanced
  let eqn : (carried+G.chordWidths held+G.chordWidths kept)+G.chordWidths spill=
      carried+G.chordWidths old+G.chordWidths active := by
    simpa only [add_assoc] using congrArg (carried+·) one.symm
  rebase eqn rfl (carry R (carried+G.chordWidths held+G.chordWidths kept))

theorem action (carried : Widths K) (old active held kept spill : I→ℕ)
    (balanced : ∀i,old i+active i=held i+kept i+spill i)
    (R : SiteMatrix (State (G.chordWidths spill)) (State B) F)
    (route : ∀v,(raw F _).coeff v=SiteMatrix.act R (raw F B).coeff v)
    (v : ∀s,State (carried+G.chordWidths old+G.chordWidths active) s) :
    (raw F _).coeff v=SiteMatrix.act (matrix G carried old active held kept spill balanced R) (raw F _).coeff v :=
  rebase_action _ rfl _ (carry_action R route _) v

end LedgerStep
end Hierarchy.ProbeStage.CoreBoard

end
end OAI
