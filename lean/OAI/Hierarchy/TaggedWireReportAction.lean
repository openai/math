import OAI.Hierarchy.TaggedWireWidthRebase
import OAI.Hierarchy.ProtocolRAMPruneUnordered
import OAI.Hierarchy.TaggedWireCoreMatrix
import OAI.Hierarchy.TaggedWireReportOrder

namespace OAI
/-! # The specific core routing gates on the actually emitted terminal link rows -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators

theorem reported_words {K n : ℕ} {F : Type*} [Field F] {A : Fin K→Type} {V : Widths K}
    (E : Fin n→Chord K) (bits : Fin n→ℕ) (same : installedWidths E bits=V)
    (M : SiteMatrix A (State V) F) (x : ∀i,A i) :
    SiteMatrix.act M (raw F V).coeff x=∑d : ∀e,Fin (2^bits e),∏s,M s (x s)
      (cast (congrArg (fun U=>State U s) same) (readEdges E bits d s)) := by
  subst V
  exact act_edge_words E bits M x

end Hierarchy.WireTelescope

namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope ProtocolRAMEmit
open scoped Classical BigOperators

section
variable {S : PurchaseSampler} {F : Type*} [Field F] {h k d w edges r M den : ℕ} {b : Fin k→ℕ}
    {D : TaggedPrune.Layout h w b} {π : Equiv.Perm (Tagged.Row h)} {place : Site h d k→Fin (D.last+1)}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord (D.last+1))
    (fixed : Fin edges→ℕ) (stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ) (reserved used : Columns h d×Fin k→ℕ)
    {rows : Fin edges→ProtocolRAMEmit.Row} (G : Geometry D M den rows)

structure MatrixReceipt where
  report : ∀e,(rows e).width=fixed e+routeLoad B.ordinary stock e+
    routeLoad B.centers (fun c=>reserved c-used c) e
  ends : ∀i : ActiveRows rows,
    (B.actual.tail i.val=(rows i.val).leftSite (G.fits i) ∧ B.actual.head i.val=(rows i.val).rightSite (G.fits i)) ∨
    (B.actual.tail i.val=(rows i.val).rightSite (G.fits i) ∧ B.actual.head i.val=(rows i.val).leftSite (G.fits i))

end
namespace MatrixReceipt
variable {S : PurchaseSampler} {F : Type*} [Field F] {h k d w edges r M den : ℕ} {b : Fin k→ℕ}
    {D : TaggedPrune.Layout h w b} {π : Equiv.Perm (Tagged.Row h)} {place : Site h d k→Fin (D.last+1)}
    {B : Mount (S:=S) π place edges} {fixed : Fin edges→ℕ}
    {stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ} {reserved used : Columns h d×Fin k→ℕ}
    {rows : Fin edges→ProtocolRAMEmit.Row} {G : Geometry D M den rows}
    (H : MatrixReceipt B fixed stock reserved used G) (inj : Function.Injective place) (pad : Chord (D.last+1))

include H

theorem dropped (e : Fin edges) (loop : B.actual.tail e=B.actual.head e) : (rows e).width=0 := by
  by_contra nz
  let i : ActiveRows rows := ⟨e,Nat.pos_of_ne_zero nz⟩
  rcases H.ends i with ⟨t,h⟩|⟨t,h⟩
  · exact G.distinct i (congrArg Fin.val (t.symm.trans (loop.trans h)))
  · exact G.distinct i (congrArg Fin.val (h.symm.trans (loop.symm.trans t)))

theorem old_width :
    let layout := B.matrixLayout inj pad
    installedWidths layout.family (SettledMatrix.Layout.bits fixed stock reserved used)=
      B.actual.chordWidths fixed+(commodityGraph π place).chordWidths stock+
        (catalystGraph place).chordWidths (fun c=>reserved c-used c) := by
  have left : installedWidths (filledChord B.actual pad) fixed=B.actual.chordWidths fixed := by
    apply filled_width
    intro e loop
    have nil := H.dropped e loop
    rw [H.report e] at nil
    omega
  exact ((B.matrixLayout inj pad).installed fixed stock reserved used).trans
    (congrArg (fun t => t+(commodityGraph π place).chordWidths stock+
      (catalystGraph place).chordWidths (fun c=>reserved c-used c)) left)

theorem native_width :
    let layout := B.matrixLayout inj pad
    routeLoad layout.routes (SettledMatrix.Layout.bits fixed stock reserved used) = fun e=>(rows e).width := by
  funext e
  exact ((B.matrixLayout inj pad).measured fixed stock reserved used e).trans (H.report e).symm

theorem reported_width :
    installedWidths (filledChord B.actual pad) (fun e=>(rows e).width)=installedWidths G.links.ends G.links.bits :=
  (filled_width B.actual pad _ H.dropped).trans (G.installedWidths_eq_flip B.actual H.ends).symm

theorem new_width :
    let layout := B.matrixLayout inj pad
    installedWidths layout.edge (routeLoad layout.routes (SettledMatrix.Layout.bits fixed stock reserved used)) =
      installedWidths G.links.ends G.links.bits := by
  exact (congrArg (installedWidths (B.matrixLayout inj pad).edge) (H.native_width inj pad)).trans
    (H.reported_width pad)

include inj pad

def matrix (enum : Fin r≃RouteOccurrence B.ordinary B.centers) :
    SiteMatrix (State (B.actual.chordWidths fixed+(commodityGraph π place).chordWidths stock+
      (catalystGraph place).chordWidths (fun c=>reserved c-used c))) (State (installedWidths G.links.ends G.links.bits)) F :=
  let layout := B.matrixLayout inj pad
  rebase (H.old_width inj pad) (H.new_width inj pad)
    (layout.operator fixed stock reserved used (layout.nativeOrder enum))

theorem action (enum : Fin r≃RouteOccurrence B.ordinary B.centers)
    (x : ∀i,State (B.actual.chordWidths fixed+(commodityGraph π place).chordWidths stock+
      (catalystGraph place).chordWidths (fun c=>reserved c-used c)) i) :
    (raw F _).coeff x=SiteMatrix.act (H.matrix inj pad enum) (raw F (installedWidths G.links.ends G.links.bits)).coeff x := by
  let layout := B.matrixLayout inj pad
  apply rebase_action
  intro z
  exact chordRouter_action layout.family layout.edge layout.routes (SettledMatrix.Layout.bits fixed stock reserved used)
    (layout.nativeOrder enum) (fun i=>layout.paths _) z

theorem native_contraction (enum : Fin r≃RouteOccurrence B.ordinary B.centers)
    (x : ∀i,State (B.actual.chordWidths fixed+(commodityGraph π place).chordWidths stock+
      (catalystGraph place).chordWidths (fun c=>reserved c-used c)) i) :
    (raw F _).coeff x=∑a : ∀e : Fin edges,Fin (2^(rows e).width),∏s,H.matrix inj pad enum s (x s)
      (cast (congrArg (fun U=>State U s) (H.reported_width pad)) (readEdges (filledChord B.actual pad) _ a s)) :=
  (H.action inj pad enum x).trans (reported_words _ _ (H.reported_width pad) _ _)

end MatrixReceipt
end Hierarchy.ProbeStage.CoreBoard
end

end OAI
