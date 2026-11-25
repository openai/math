import OAI.Hierarchy.TaggedWireChosenPackets

namespace OAI
/-! # Every inactive party contributes a scalar one and a singleton wire state -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe AdaptiveProbe
open scoped Classical BigOperators

namespace PhysicalMatrix
variable {S k : ℕ} {F : Type} [Field F] (place : Fin k ↪ Fin S) {s : Fin S}

theorem state_away (U : Widths k) (away : s∉Set.range place) :
    Subsingleton (State (placeWidths place U) s) := by
  constructor
  intro x y
  funext p
  have excluded : p.1.1∉Set.range (physicalChord place) := by
    rintro ⟨e,matchEdge⟩
    obtain ⟨side,colour⟩ : ∃t,PhysicalMatrix.side place e t=p.1.2 := by
      unfold PhysicalMatrix.side
      split_ifs
      · exact ⟨_,rfl⟩
      · exact ⟨!p.1.2,Bool.not_not _⟩
    apply away
    refine ⟨(portGraph k).vertex e side,?_⟩
    rw [←PhysicalMatrix.incident place e side,matchEdge,colour]
    exact p.property
  have n:=PhysicalMatrix.width_away place U excluded
  have bound (v : Index (placeWidths place U) p.1.1) : v.val=0 := by
    have z:=v.isLt
    change v.val<2^(placeWidths place U p.1.1) at z
    simpa [n] using z
  exact Fin.ext ((bound _).trans (bound _).symm)

theorem empty_entry {U V : Widths k} (M : SiteMatrix (State U) (State V) F) (away : s∉Set.range place)
    (x : State (placeWidths place U) s) (y : State (placeWidths place V) s) :
    matrix place M s x y=1 := by
  let : IsEmpty {i // place i=s}:=⟨fun u=>away ⟨u.val,u.property⟩⟩
  simp [matrix]

private theorem transport_empty {U V U' V' : Widths S} (u : U=U') (v : V=V')
    (M : SiteMatrix (State U) (State V) F) (M' : SiteMatrix (State U') (State V') F)
    (equal : HEq M M') {s : Fin S} (h : ∀x y,M s x y=1) : ∀x y,M' s x y=1 := by
  subst U';subst V';cases equal
  exact h
end PhysicalMatrix

namespace ChosenPackets
variable {F : Type} [Field F] {S r : ℕ} (P : Placed F S)
variable (c : Histogram (Fin P.data.terms) r) {s : Fin S} (away : s∉Set.range P.place)

private theorem placed_offers_width :
    placeWidths P.place (P.data.outputWidths c + P.graph.chordWidths (fun _=>r*P.data.selectorBits))=P.offers c := by
  let : Nonempty (Fin S) := ⟨P.place P.root⟩
  rw [map_add]
  exact congrArg (fun u=>u+placeWidths P.place (P.graph.chordWidths (fun _=>r*P.data.selectorBits)))
    (physical_histogram_width P.data c P.place)

include away in
theorem Placed.offers_away : Subsingleton (State (P.offers c) s) := by
  let : Nonempty (Fin P.sites):=⟨P.root⟩
  have h:=PhysicalMatrix.state_away P.place
    (P.data.outputWidths c+P.graph.chordWidths (fun _=>r*P.data.selectorBits)) away
  rw [←placed_offers_width P c]
  exact h

include away in
theorem Placed.entry_away (x : State (P.wants r) s) (y : State (P.offers c) s) : P.signed r c s x y=1 := by
  let : Nonempty (Fin S) := ⟨P.place P.root⟩
  let : Nonempty (Fin P.sites):=⟨P.root⟩
  let M:=P.data.broadcastMatrix P.root r P.graph c
  have a : placeWidths P.place (P.data.inputWidths r)=P.wants r:=by
    exact physical_demand (edge:=P.edge) (req:=P.wanted) P.place P.data.width r
  have b : placeWidths P.place (P.data.outputWidths c+P.graph.chordWidths (fun _=>r*P.data.selectorBits))=P.offers c:=by
    exact placed_offers_width P c
  apply PhysicalMatrix.transport_empty a b (PhysicalMatrix.matrix P.place M) (P.signed r c) _ (fun _ _=>PhysicalMatrix.empty_entry P.place M away _ _) x y
  apply HEq.symm
  unfold Placed.signed PhysicalMatrix.packetMatrix
  first | exact cast_heq _ _

theorem Row.skip_state (s : Fin S) : Subsingleton (State (0 : Widths S) s) := by
  constructor
  intro x y
  funext p
  apply Fin.ext
  have hx : (x p).val < 1 := by simpa using (x p).isLt
  have hy : (y p).val < 1 := by simpa using (y p).isLt
  omega

theorem Row.skip_entry (letters : ℕ) (c : Histogram (Fin letters) 0) (s : Fin S)
    (x y : State (0 : Widths S) s) : (Row.skipped (F:=F) (S:=S) letters).entry c s x y=1 := by
  let := Row.skip_state s
  simp [Row.entry,SiteMatrix.identity,Subsingleton.elim x y]

end ChosenPackets
end Hierarchy.WireTelescope
end

end OAI
