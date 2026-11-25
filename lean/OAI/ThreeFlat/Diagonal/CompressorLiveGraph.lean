import OAI.ThreeFlat.Diagonal.CompressorTemplateValue
import OAI.ThreeFlat.Diagonal.CompressorPaddingWord

namespace OAI
/-! # Agreement of the bounded live-row query with the numbered shrinking graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement CompressorRegularize
open scoped Classical BigOperators Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w t l : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (G : ArcColumns (Word w)) (m : Memory w)
variable (R : ArcReads P E G m) (code : B ↪ ℕ) (hc : ∀ b,E.base b=(code b:Word w))
variable (hi : Function.Injective E.base) (bound : ∀i,S.pieces i≤S.pieceRadix)
variable (fit : ∀e,edgeId S P code bound e<2^w)

def endpoint (lay rev : Bool) (q : ShrinkEdge P S.pieces) := base (slotSite P lay (baseRole lay rev) q)
abbrev liveDegree (S : Stage) := S.degree*(3*(2^S.colors*S.degree)/4)*(∑ k,S.pieces k)

private theorem endpoint_count (lay rev : Bool) (v : B × BitWord t) (colors : 2≤S.colors) :
    (CompressorRegularize.incident (endpoint S P lay rev) v).card=liveDegree S := by
  refine Eq.trans ?_ (incident_count P lay (baseRole lay rev) S.pieces v colors)
  apply congrArg Finset.card
  ext e
  simp only [CompressorRegularize.incident, Finset.mem_filter, Finset.mem_univ, true_and, endpoint]
  first
  | exact Iff.rfl
  | exact ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩⟩

noncomputable def ordinalOf (lay rev : Bool) (colors : 2≤S.colors) :
    ShrinkEdge P S.pieces ≃ (B × BitWord t) × Fin (liveDegree S) := by
  letI : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  exact numbering (endpoint S P lay rev) (fun v => endpoint_count S P lay rev v colors)

include R hc hi
theorem query_graph (one : (1:Word w)≠0) (lay rev : Bool) (colors : 2≤S.colors)
    (liveFits : liveDegree S≤2^w) (tagFits : 2^t<2^w)
    (baseFits : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (v : B × BitWord t) (i : Fin (liveDegree S)) :
    let cs := fun r z => allWords (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay r z
    let e := (ordinalOf S P code bound lay rev colors).symm (v,i)
    liveQuery cs rev (baseAddress S E v) (i.val:Word w) = fun
      | .identifier => idEmbedding S P code bound fit e
      | .neighbor => baseAddress S E (endpoint S P lay (!rev) e)
      | .delta => tagWord E.lanes (wireShift S P lay e)
      | .matePort => ((ordinalOf S P code bound lay (!rev) colors e).2.val:Word w) := by
  let : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  let cs := fun r z => allWords (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay r z
  let key := sortedKey S P code bound fit
  have lists (rev : Bool) (v : B × BitWord t) : cs rev (baseAddress S E v)=visitWords S E G m lay rev v :=
    visit_rows S E G m lay rev v (baseFits v) tagFits
  refine liveQuery_correct (endpoint S P lay) (fun r v => endpoint_count S P lay r v colors) key
    (baseAddress S E) (fun e => tagWord E.lanes (wireShift S P lay e)) cs ?_ ?_ liveFits rev v i
  · intro rev b
    rw [lists]
    exact visitSupport S P E G m R code hc hi bound fit one lay rev b
  · intro rev b a ha e hk
    rw [lists] at ha
    exact visitPayload S P E G m R code hc hi bound fit one lay rev b a ha e hk

section
attribute [local irreducible] numbering

omit R hc hi in
private theorem numbering_independent {Edges Vertices : Type*} {degree : ℕ}
    [ord : LinearOrder Edges] (vertex : Edges → Vertices)
    {fe ge : Fintype Edges} {dv dw : DecidableEq Vertices}
    (h : ∀ v, (@CompressorRegularize.incident Edges Vertices fe dv vertex v).card = degree)
    (k : ∀ v, (@CompressorRegularize.incident Edges Vertices ge dw vertex v).card = degree) :
    @numbering Edges Vertices fe ord dv degree vertex h =
      @numbering Edges Vertices ge ord dw degree vertex k := by
  cases Subsingleton.elim fe ge
  cases Subsingleton.elim dv dw
  rfl

omit R hc hi in
/-- The pair numbered at the far role is exactly the target permutation of
the mathematical regularization (or its inverse for a reverse-column row). -/
theorem ordinal_graph (lay rev : Bool) (colors : 2≤S.colors)
    (good : TagConditions P.slots (shift P) P.offset)
    (p : (B × BitWord t) × Fin (liveDegree S)) :
    let A := shrinkingGraph P lay S.pieces (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound)
      colors binary_neg good
    (if rev then A.base.target.symm p else A.base.target p) =
      ordinalOf S P code bound lay (!rev) colors ((ordinalOf S P code bound lay rev colors).symm p) := by
  let : LinearOrder (ShrinkEdge P S.pieces) := LinearOrder.lift' _
    (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound).injective
  cases rev <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      shrinkingGraph, CompressorRegularize.graph, ordinalOf, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm] <;>
    apply congrArg₂ (fun (dst src : ShrinkEdge P S.pieces ≃ (B × BitWord t) × Fin (liveDegree S)) =>
      dst (src.symm p)) <;>
    apply numbering_independent

end


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
