import OAI.Hierarchy.ProbeStripBroadcastTree
import OAI.Hierarchy.ProbeDisjointStrips
import OAI.Hierarchy.ProbePayloadPlacement
import OAI.Hierarchy.ProtocolRAMLocalCharge

namespace OAI
/-! # Per-reporter occupancy of all original local and selector wires in one event -/

noncomputable section
namespace Hierarchy.AdaptiveProbe.Strip

open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe ProbeStage
open scoped BigOperators Classical

variable {X Ball E : Type} [Fintype Ball] [Fintype E] {S : ℕ}

/-- One fixed physical chord may be used by several local roles of its unique
owner. Its first endpoint is always among that ball's actual named sites. -/
def reportedRole (place : Ball×X↪Fin S) (ends : E→DistinctPair X) (p : Ball) (e : E) : Chord S :=
  orderedEnds (place (p,(ends e).left)) (place (p,(ends e).right))
    (fun eqn=>(ends e).apart (congrArg Prod.snd (place.injective eqn)))

omit [Fintype Ball] [Fintype E] in
theorem reported_owner (place : Ball×X↪Fin S) (ends : E→DistinctPair X) (p : Ball) (e : E) :
    ∃ x : X, place (p,x)=(reportedRole place ends p e).val.1 := by
  unfold reportedRole orderedEnds
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

omit [Fintype Ball] [Fintype E] in
theorem reported_second (place : Ball×X↪Fin S) (ends : E→DistinctPair X) (p : Ball) (e : E) :
    ∃ x : X, place (p,x)=(reportedRole place ends p e).val.2 := by
  unfold reportedRole orderedEnds
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

/-- Arbitrary repeated local options, purchased probe edges and repeated
physical endpoint pairs count at most once per role, irrespective of the
number of bought balls or their placement order. -/
theorem role_fiber (place : Ball×X↪Fin S) (ends : E→DistinctPair X) (c : Chord S) :
    Fintype.card {z : Ball×E // reportedRole place ends z.1 z.2=c} ≤ Fintype.card E := by
  apply Fintype.card_le_of_injective (fun z=>z.val.2)
  intro a b role
  obtain ⟨i,ia⟩ := reported_owner place ends a.val.1 a.val.2
  obtain ⟨j,jb⟩ := reported_owner place ends b.val.1 b.val.2
  rw [a.property] at ia
  rw [b.property] at jb
  have same : a.val.1 = b.val.1 :=
    congrArg (fun z : Ball × X => z.1) (place.injective (ia.trans jb.symm))
  exact Subtype.ext (Prod.ext same role)

theorem occupancy (place : Ball×X↪Fin S) (ends : E→DistinctPair X) (c : Chord S)
    (width : Ball→E→ℕ) (cap : ℕ) (bound : ∀p e,width p e≤cap) :
    (∑ z : {u : Ball×E // reportedRole place ends u.1 u.2=c},width z.val.1 z.val.2) ≤
      Fintype.card E*cap := by
  calc
    _ ≤ ∑ _ : {u : Ball×E // reportedRole place ends u.1 u.2=c},cap := Finset.sum_le_sum (fun z _=>bound _ _)
    _ = Fintype.card {u : Ball×E // reportedRole place ends u.1 u.2=c}*cap := by simp
    _ ≤ _ := Nat.mul_le_mul_right cap (role_fiber place ends c)

/-- The actual aggregate width read at a physical chord is precisely
the fiber sum of the named role incidences. -/
theorem width_at_reporter (place : Ball×X↪Fin S) (ends : E→DistinctPair X)
    (width : Ball→E→ℕ) (c : Chord S) :
    (∑ p,optionWidths (reportedRole place ends p) (width p)) c =
      ∑ z : {u : Ball×E // reportedRole place ends u.1 u.2=c},width z.val.1 z.val.2 := by
  classical
  simp only [optionWidths,Finsupp.finsetSum_apply,Finsupp.single_apply]
  let keep (u : Ball×E) := reportedRole place ends u.1 u.2=c
  let bits (u : Ball×E) := width u.1 u.2
  calc
    _ = ∑ u : Ball×E,if keep u then bits u else 0 :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by rw [←Finset.sum_filter,←Finset.sum_subtype_eq_sum_filter,Finset.subtype_univ]

def ballEmbedding (place : Ball×X↪Fin S) (p : Ball) : X ↪ Fin S :=
  ⟨fun x=>place (p,x),fun _ _ h=>congrArg Prod.snd (place.injective h)⟩

omit [Fintype Ball] in
/-- Arbitrary printed ordinal names produce exactly the native physical
row, including both possible orientations of its endpoint names. -/
theorem placed_options [Fintype X] (place : Ball×X↪Fin S) (p : Ball)
    (name : X≃Fin (Fintype.card X)) (ends : E→DistinctPair X) (bits : E→ℕ) :
    placeWidths (name.symm.toEmbedding.trans (ballEmbedding place p))
        (optionWidths (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (ends e)) bits) =
      optionWidths (reportedRole place ends p) bits := by
  simp only [optionWidths,map_sum]
  apply Finset.sum_congr rfl
  intro e _
  let : Nonempty (Fin (Fintype.card X)) := ⟨name (ends e).left⟩
  rw [place_single,physicalChord_role]; rfl

omit [Fintype Ball] in
theorem placed_tree {n k : ℕ} (place : Ball×TreeSite n k↪Fin S)
    (p : Ball) (name : TreeSite n k≃Fin (Fintype.card (TreeSite n k))) (w : ℕ) :
    placeWidths (name.symm.toEmbedding.trans (ballEmbedding place p))
        ((treeGraph name).chordWidths (fun _=>w)) =
      optionWidths (reportedRole place (treeEnds n k) p) (fun _=>w) := by
  let extra : Empty→DistinctPair (TreeSite n k) := isEmptyElim
  rw [tree_widths name extra]
  simpa only [tree_role_ends,optionWidths] using placed_options place p name (treeEnds n k) (fun _=>w)

/-- Per real reporter, in one event at most the finite menu's role count
times its per-word cap and the original core tree's role count times its
selector rate are written. -/
theorem installed_and_broadcast {n k : ℕ} (place : Ball×TreeSite n k↪Fin S)
    (ends : E→DistinctPair (TreeSite n k)) (c : Chord S) {r width cap : ℕ}
    {H : ℕ} (count : Ball→Fin H→E→ℕ) (hist : Ball→Histogram (Fin H) r)
    (bits : Ball→ℕ) (entries : ∀p j e,count p j e≤width) (select : ∀p,bits p≤cap) :
    (∑ z : {u : Ball×E // reportedRole place ends u.1 u.2=c},histWidth (count z.val.1) (hist z.val.1) z.val.2) +
      (∑ z : {u : Ball×TreeLink n k // reportedRole place (treeEnds n k) u.1 u.2=c},r*bits z.val.1) ≤
      r*(Fintype.card E*width + (n+(n+1)*(k*2))*cap) := by
  have wires := occupancy place ends c (fun p e=>histWidth (count p) (hist p) e) (r*width)
    (fun p e=>ProtocolRAM.histWidth_le (count p) (hist p) e width (fun j=>entries p j e))
  have links := occupancy place (treeEnds n k) c (fun p _=>r*bits p) (r*cap)
    (fun p _=>Nat.mul_le_mul_left r (select p))
  rw [tree_card] at links
  exact (Nat.add_le_add wires links).trans_eq (by ring)

/-- Aperture at one actual chord after both the signed word and its
broadcast have been placed, counted over every disjoint retained ball. -/
theorem placed_width_bound {n k : ℕ} (place : Ball×TreeSite n k↪Fin S)
    (name : Ball→TreeSite n k≃Fin (Fintype.card (TreeSite n k)))
    (ends : E→DistinctPair (TreeSite n k)) (c : Chord S) {r width cap H : ℕ}
    (count : Ball→Fin H→E→ℕ) (hist : Ball→Histogram (Fin H) r)
    (bits : Ball→ℕ) (entries : ∀p j e,count p j e≤width) (select : ∀p,bits p≤cap) :
    (∑ p,placeWidths ((name p).symm.toEmbedding.trans (ballEmbedding place p))
      (optionWidths (fun e=>@DistinctPair.chord _ _ ⟨name p⟩ (ends e))
          (histWidth (count p) (hist p)) + (treeGraph (name p)).chordWidths (fun _=>r*bits p))) c ≤
      r*(Fintype.card E*width + (n+(n+1)*(k*2))*cap) := by
  simp only [map_add,placed_options,placed_tree,Finset.sum_add_distrib,Finsupp.add_apply,
    width_at_reporter]
  exact installed_and_broadcast place ends c count hist bits entries select


end Hierarchy.AdaptiveProbe.Strip

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
variable {z d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (marked : StageAt z d→(Fin k×Bool)→Finset (Fin (2^z)))

/-- The injective placement of all retained columns extends to every
center and signed-axis socket by preserving the actual layer bit. -/
def allTreeSites (unique : ∀s c c' r,r∈marked s c → r∈marked s c'→c=c') :
    (LiveChains S π depth marked × ColumnSite (Columns depth) k) ↪ ColumnSite (StageColumns z d) k :=
  (Equiv.prodAssoc _ _ _).symm.toEmbedding.trans
    ((allStripColumns S π depth marked unique).prodMap (Function.Embedding.refl _))

theorem allTreeSites_single (unique : ∀s c c' r,r∈marked s c → r∈marked s c'→c=c')
    (p : LiveChains S π depth marked) (x : ColumnSite (Columns depth) k) :
    allTreeSites S π depth marked unique (p,x)=stripSites S π depth marked p x := by
  exact Prod.ext (allStripColumns_single S π depth marked unique p x.1) rfl

end Hierarchy.ProbeStage
end

end OAI
