import OAI.Hierarchy.ProtocolRAMEmit
import OAI.Hierarchy.TaggedPruning
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths

namespace OAI
/-! # Integer pruning on the triple tables emitted by the protocol controller -/

noncomputable section

namespace Hierarchy.ProtocolRAMEmit

open Computability.VPVNP.BurstRAM
open LinearAlgebra.SpectralBooks.ChordGraph
open TaggedPrune CorrectionFrame
open scoped BigOperators Fin.CommRing

variable {w n k h M den : ℕ} {b : Fin k → ℕ}

abbrev ActiveRows (rows : Fin n → Row) := {i : Fin n // 0 < (rows i).width}

def activeIndex (rows : Fin n → Row) (j : Fin (Fintype.card (ActiveRows rows))) :
    ActiveRows rows := (Fintype.equivFin (ActiveRows rows)).symm j

/-- Both sites are the global identifiers read by the physical controller. -/
def Row.leftSite {last : ℕ} (r : Row) (fits : r.endpoint ≤ last ∧ r.opposite ≤ last) :
    Fin (last+1) := ⟨r.endpoint,Nat.lt_succ_of_le fits.1⟩

def Row.rightSite {last : ℕ} (r : Row) (fits : r.endpoint ≤ last ∧ r.opposite ≤ last) :
    Fin (last+1) := ⟨r.opposite,Nat.lt_succ_of_le fits.2⟩

/-- The canonical chord of an unordered active row. Either orientation of the
physical source and destination is valid. -/
def chord {last : ℕ} (r : Row) (distinct : r.endpoint ≠ r.opposite)
    (fits : r.endpoint ≤ last ∧ r.opposite ≤ last) : Chord (last+1) :=
  if h : r.endpoint < r.opposite then ⟨(r.leftSite fits,r.rightSite fits),h⟩
  else ⟨(r.rightSite fits,r.leftSite fits),show r.opposite < r.endpoint by omega⟩

structure Geometry (D : TaggedPrune.Layout h w b) (M den : ℕ) (rows : Fin n → Row) where
  distinct : ∀ i : ActiveRows rows, (rows i.val).endpoint ≠ (rows i.val).opposite
  fits : ∀ i : ActiveRows rows, (rows i.val).endpoint ≤ D.last ∧ (rows i.val).opposite ≤ D.last
  scale : ActiveRows rows → ℝ
  scale_nonneg : ∀ i, 0 ≤ scale i
  different_zero : ∀ i, let r := rows i.val
                        D.layer (r.leftSite (fits i)) ≠ D.layer (r.rightSite (fits i)) → scale i = 0
  distance : ∀ i, let r := rows i.val
                  D.layer (r.leftSite (fits i)) ≠ D.layer (r.rightSite (fits i)) →
                  (M:ℝ)*dist (point (D.layer (r.leftSite (fits i))))
                    (point (D.layer (r.rightSite (fits i)))) ≤ (r.lengthCode:ℝ)/den

namespace Geometry

variable {D : TaggedPrune.Layout h w b} {rows : Fin n → Row} (G : Geometry D M den rows)

def edge (i : ActiveRows rows) : Chord (D.last+1) := chord _ (G.distinct i) (G.fits i)

theorem edge_layer_eq (i : ActiveRows rows) :
    (D.layer (G.edge i).1.1 = D.layer (G.edge i).1.2) ↔
      D.layer ((rows i.val).leftSite (G.fits i)) = D.layer ((rows i.val).rightSite (G.fits i)) := by
  unfold edge chord
  split
  · rfl
  · exact eq_comm

theorem edge_dist (i : ActiveRows rows) :
    dist (point (D.layer (G.edge i).1.1)) (point (D.layer (G.edge i).1.2)) =
      dist (point (D.layer ((rows i.val).leftSite (G.fits i))))
        (point (D.layer ((rows i.val).rightSite (G.fits i)))) := by
  unfold edge chord
  split
  · rfl
  · exact dist_comm _ _

def links : TaggedPrune.Links D M where
  number := Fintype.card (ActiveRows rows)
  ends j := G.edge (activeIndex rows j)
  bits j := (rows (activeIndex rows j).val).width
  len j := ((rows (activeIndex rows j).val).lengthCode:ℝ)/den
  scale j := G.scale (activeIndex rows j)
  len_nonneg _ := by positivity
  scale_nonneg j := G.scale_nonneg (activeIndex rows j)
  different_zero j cross := G.different_zero _ ((G.edge_layer_eq _).not.mp cross)
  distance j cross := by
    rw [G.edge_dist]
    exact G.distance _ ((G.edge_layer_eq _).not.mp cross)

open LinearAlgebra.SpectralBooks

/-- Each positive physical row contributes its width to its unordered chord.
Parallel rows add their widths, and idle rows contribute zero. -/
theorem installedWidths_eq (A : PortGraph (Fin (D.last+1)) (Fin n))
    (tail : ∀ i : ActiveRows rows, A.tail i.val = (rows i.val).leftSite (G.fits i))
    (head : ∀ i : ActiveRows rows, A.head i.val = (rows i.val).rightSite (G.fits i)) :
    AdaptiveProbe.installedWidths G.links.ends G.links.bits = A.chordWidths (fun i => (rows i).width) := by
  classical
  let f := fun i : Fin n => A.chordWidth i (rows i).width
  have active (i : ActiveRows rows) : (rows i.val).width • unitChord (G.edge i) = f i.val := by
    change _ = A.chordWidth i.val (rows i.val).width
    unfold PortGraph.chordWidth edge chord
    simp only [tail i,head i,unitChord,Finsupp.smul_single,smul_eq_mul,mul_one]
    by_cases h : (rows i.val).endpoint < (rows i.val).opposite
    · have left : (rows i.val).leftSite (G.fits i) < (rows i.val).rightSite (G.fits i) := h
      simp only [dite_eq_left h,dite_eq_left left]
    · have no : ¬ (rows i.val).leftSite (G.fits i) < (rows i.val).rightSite (G.fits i) := h
      have right : (rows i.val).rightSite (G.fits i) < (rows i.val).leftSite (G.fits i) :=
        show (rows i.val).opposite < (rows i.val).endpoint by have := G.distinct i; omega
      simp only [dite_eq_right h,dite_eq_right no,dite_eq_left right]
  have idle : (∑ i : {j : Fin n // ¬ 0<(rows j).width}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have zero : (rows i.val).width=0 := Nat.eq_zero_of_not_pos i.property
    dsimp only [f]
    rw [zero]
    unfold PortGraph.chordWidth
    split_ifs <;> simp
  calc
    _ = ∑ j, f (activeIndex rows j).val :=
      Finset.sum_congr rfl fun j _ => active (activeIndex rows j)
    _ = ∑ i : ActiveRows rows, f i.val :=
      (Fintype.equivFin (ActiveRows rows)).symm.sum_comp (fun i => f i.val)
    _ = _ := by
      have split := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => 0<(rows i).width) f
      rw [idle,add_zero] at split
      exact split

end Geometry

/-- The metric table fields contain the integer length numerator and bit width
used in the exact pruning decision. Inactive board rows contribute no terms. -/
theorem Geometry.keep_iff_output {W : ℕ} {D : TaggedPrune.Layout h w b} {rows : Fin n → Row}
    (G : Geometry D M den rows) (ticks dst : ℕ) (m : Memory W) (hw : 0<w) (hd : 0<den)
    (bound : ∀ i : ActiveRows rows, (rows i.val).width < 2^W ∧ (rows i.val).lengthCode < 2^W) :
    G.links.Keep ticks ↔ 2*M*(∑ j, b j)*den ≤
      (∑ j ∈ G.links.cross,
        let i := (activeIndex rows j).val
        ((emitted dst rows m (dst+3*n+3*i.val+2)).val *
          (emitted dst rows m (dst+3*n+3*i.val+1)).val)) + ticks*w*den := by
  rw [G.links.keep_iff_integer hw hd (fun j => (rows (activeIndex rows j).val).lengthCode) (fun _ => rfl)]
  apply Iff.of_eq
  apply congrArg (fun z : ℕ => 2*M*(∑ t, b t)*den ≤ z)
  apply congrArg (· + ticks*w*den)
  apply Finset.sum_congr rfl
  intro j _
  let i := activeIndex rows j
  have width := (emitted_read dst rows m i.val (1:Fin 3)).2.1
  have len := (emitted_read dst rows m i.val (2:Fin 3)).2.1
  change emitted dst rows m (dst+3*n+3*i.val.val+1) = ((rows i.val).width:Word W) at width
  change emitted dst rows m (dst+3*n+3*i.val.val+2) = ((rows i.val).lengthCode:Word W) at len
  change (rows i.val).lengthCode*(rows i.val).width =
    (emitted dst rows m (dst+3*n+3*i.val.val+2)).val * (emitted dst rows m (dst+3*n+3*i.val.val+1)).val
  rw [width,len,Fin.val_cast_of_lt (bound i).1,Fin.val_cast_of_lt (bound i).2]

end Hierarchy.ProtocolRAMEmit

end
end OAI
