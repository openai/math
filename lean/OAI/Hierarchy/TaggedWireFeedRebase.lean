import OAI.Hierarchy.TaggedWireFeedAction
import OAI.Hierarchy.TaggedWireWidthRebase

namespace OAI
/-! # One deterministic feed matrix on the original chronological width functions -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope AdaptiveProbe
open scoped Classical BigOperators

variable {h d k K edges : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
  {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges)
local notation "Goods" => Data h d k
local notation "Axes" => Columns h d×Fin k

def ledger (graph : PortGraph (Fin K) (Fin edges)) (paid : Fin edges→ℕ) (goods : Goods→ℕ) (axes : Axes→ℕ) :=
  graph.chordWidths paid+(commodityGraph π place).chordWidths goods+(catalystGraph place).chordWidths axes

/-- Geometry matters precisely on rows carrying earlier paid bits. -/
theorem paid_geometry (G H : PortGraph (Fin K) (Fin edges)) (bits : Fin edges→ℕ)
    (ends : ∀e,0<bits e→G.tail e=H.tail e ∧ G.head e=H.head e) :
    G.chordWidths bits=H.chordWidths bits := by
  classical
  unfold PortGraph.chordWidths
  apply Finset.sum_congr rfl
  intro e _
  by_cases live : 0<bits e
  · obtain ⟨left,right⟩:=ends e live
    simp only [PortGraph.chordWidth,left,right]
  · have zero : bits e=0:=Nat.eq_zero_of_not_pos live
    simp only [zero,chordWidth_scaled,zero_smul]

def passWidth (oldPaid : Fin edges→ℕ) (passive : Goods→ℕ) (axes : Axes→ℕ) :=
  ledger (π:=π) (place:=place) B.actual oldPaid passive axes

theorem input_ledger (G : PortGraph (Fin K) (Fin edges)) (oldPaid : Fin edges→ℕ)
    (passive original : Goods→ℕ) (axes : Axes→ℕ) (T : Transfer h d k)
    (geometry : G.chordWidths oldPaid=B.actual.chordWidths oldPaid)
    (bits : ∀i,original i=passive i+T.old i+T.active i) :
    input (π:=π) (place:=place) (passWidth B oldPaid passive axes) T=
      ledger (π:=π) (place:=place) G oldPaid original axes := by
  unfold input passWidth ledger
  rw [geometry,funext bits]
  simp only [chordWidths_add]
  abel

theorem output_ledger (oldPaid newPaid : Fin edges→ℕ) (passive resulting : Goods→ℕ)
    (axes nextAxes : Axes→ℕ) (T : Transfer h d k)
    (paid : ∀e,newPaid e=oldPaid e+routeLoad B.ordinary T.spill e)
    (bits : ∀i,resulting i=passive i+T.held i+T.kept i) (stable : nextAxes=axes) :
    output B (passWidth B oldPaid passive axes) T=ledger (π:=π) (place:=place) B.actual newPaid resulting nextAxes := by
  unfold output passWidth ledger
  rw [funext paid,funext bits,stable]
  simp only [chordWidths_add]
  abel

/-- The original one-choice site matrix, moved to the exact pre- and post-date
physical width types. Its coefficient equation includes no ballot summation. -/
def ledgerOperator {F : Type*} [Field F] (G : PortGraph (Fin K) (Fin edges))
    (oldPaid newPaid : Fin edges→ℕ) (passive original resulting : Goods→ℕ)
    (axes nextAxes : Axes→ℕ) (T : Transfer h d k)
    (inj : Function.Injective place) (pad : Chord K) {r : ℕ}
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (geometry : G.chordWidths oldPaid=B.actual.chordWidths oldPaid)
    (paid : ∀e,newPaid e=oldPaid e+routeLoad B.ordinary T.spill e)
    (entry : ∀i,original i=passive i+T.old i+T.active i)
    (exit : ∀i,resulting i=passive i+T.held i+T.kept i) (stable : nextAxes=axes) :
    let U:=ledger (π:=π) (place:=place) G oldPaid original axes
    let V:=ledger (π:=π) (place:=place) B.actual newPaid resulting nextAxes
    {gate : SiteMatrix (State U) (State V) F // ∀x,(raw F U).coeff x=SiteMatrix.act gate (raw F V).coeff x} := by
  classical
  let carry:=passWidth B oldPaid passive axes
  let native:=matrix (F:=F) B inj pad enum carry T
  let before:=input_ledger B G oldPaid passive original axes T geometry entry
  let after:=output_ledger B oldPaid newPaid passive resulting axes nextAxes T paid exit stable
  exact ⟨rebase before after native,rebase_action before after native (action B inj pad enum carry T)⟩

/-- A local implementation can use the same physical visit order even when
its state families are spelled with the chronological stock/paid prefix. -/
def Presents {F : Type*} [Field F] (inj : Function.Injective place) (pad : Chord K) {r : ℕ}
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (carry : Widths K) (T : Transfer h d k) {U V : Widths K} (gate : SiteMatrix (State U) (State V) F) :=
  ∃(left : input (π:=π) (place:=place) carry T=U) (right : output B carry T=V),
    gate=rebase left right (matrix (F:=F) B inj pad enum carry T)

theorem presents_rebased {F : Type*} [Field F] (inj : Function.Injective place) (pad : Chord K) {r : ℕ}
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (carry : Widths K) (T : Transfer h d k) {U V : Widths K}
    (left : input (π:=π) (place:=place) carry T=U) (right : output B carry T=V) :
    Presents B inj pad enum carry T (rebase left right (matrix (F:=F) B inj pad enum carry T)) :=
  ⟨left,right,rfl⟩

theorem Presents.rebase {F : Type*} [Field F] {inj : Function.Injective place} {pad : Chord K} {r : ℕ}
    {enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges))}
    {carry : Widths K} {T : Transfer h d k} {U V U' V' : Widths K} {gate : SiteMatrix (State U) (State V) F}
    (same : Presents B inj pad enum carry T gate) (left : U=U') (right : V=V') :
    Presents B inj pad enum carry T (WireTelescope.rebase left right gate) := by
  subst U'
  subst V'
  exact same

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
