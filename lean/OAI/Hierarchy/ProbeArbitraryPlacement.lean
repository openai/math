import OAI.Hierarchy.ProbeTreeBroadcast
import OAI.Hierarchy.ProbeColumnWires
import OAI.LinearAlgebra.SpectralBooks.WireSymmetry

namespace OAI
/-! # Arbitrary physical placements of the signed wire identity -/

noncomputable section
namespace Hierarchy.Probe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat.CatalyticEmbedding AdaptiveProbe
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k S : ℕ} [Nonempty (Fin k)]

/-- Chords on a public layout are unordered pairs serialized in increasing
order. The smaller endpoint may switch sides from one tile to the next. -/
def orderedEnds (i j : Fin S) (ne : i≠j) : Chord S :=
  if h : i<j then ⟨(i,j),h⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt h) ne.symm⟩

theorem orderedEnds_comm (i j : Fin S) (ne : i≠j) :
    orderedEnds i j ne = orderedEnds j i ne.symm := by
  rcases lt_or_gt_of_ne ne with h|h
  · simp only [orderedEnds,dite_eq_left h,dite_eq_right (not_lt.mpr h.le)]
  · simp only [orderedEnds,dite_eq_right (not_lt.mpr h.le),dite_eq_left h]

def physicalChord (place : Fin k ↪ Fin S) (e : Chord k) : Chord S :=
  orderedEnds (place e.val.1) (place e.val.2) (place.injective.ne e.property.ne)

omit [Nonempty (Fin k)] in
@[simp] theorem physicalChord_increasing (place : Fin k ↪o Fin S) (e : Chord k) :
    physicalChord place.toEmbedding e=embedEdge place e := by
  simp [physicalChord,orderedEnds,place.strictMono e.property,embedEdge]

/-- Site naming a role once and then placing its named sites produces the
true globally sorted chord of that role's actual two physical sockets. -/
theorem physicalChord_role {X : Type*} [Fintype X] (name : X ≃ Fin (Fintype.card X))
    (global : X ↪ Fin S) (a : DistinctPair X) :
    physicalChord (name.symm.toEmbedding.trans global) (@DistinctPair.chord X _ ⟨name⟩ a) =
      orderedEnds (global a.left) (global a.right) (global.injective.ne a.apart) := by
  change orderedEnds _ _ _ = _
  rcases @DistinctPair.chord_joins X _ ⟨name⟩ a with eqn | eqn
  · simp only [eqn,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Equiv.symm_apply_apply]
  · simp only [eqn,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Equiv.symm_apply_apply]
    exact orderedEnds_comm _ _ _

def placeWidths (place : Fin k ↪ Fin S) : Widths k →+ Widths S :=
  Finsupp.mapDomain.addMonoidHom (physicalChord place)

omit [Nonempty (Fin k)] in
@[simp] theorem place_single (place : Fin k ↪ Fin S) (e : Chord k) (n : ℕ) :
    placeWidths place (Finsupp.single e n)=Finsupp.single (physicalChord place e) n := Finsupp.mapDomain_single

private theorem group_arbitrary_wire [Nonempty (Fin S)] (place : Fin k ↪ Fin S) (e : Chord k) :
    groupMulHom (K:=F) place (ChordGraph.wire F e) = ChordGraph.wire F (physicalChord place e) := by
  unfold ChordGraph.wire
  change ofRaw (((Raw.diagonal (Fin 2) F (Fin 2)).group _).group place) = _
  rw [ofRaw_eq_iff.mpr (Raw.group_group_equivalent _ _ _)]
  have eqn : place ∘ ![e.val.1,e.val.2] = ![place e.val.1,place e.val.2] := by
    funext i
    fin_cases i <;> rfl
  rw [eqn]
  by_cases up : place e.val.1 < place e.val.2
  · simp only [physicalChord,orderedEnds,dite_eq_left up]
  · simp only [physicalChord,orderedEnds,dite_eq_right up]
    exact ofRaw_eq_iff.mpr (Raw.grouped_wire_symm F (Fin 2) _ _)

theorem group_arbitrary_graph [Nonempty (Fin S)] (place : Fin k ↪ Fin S) (g : Widths k) :
    groupMulHom (K:=F) place (graphClass F g) = graphClass F (placeWidths place g) := by
  induction g using Finsupp.induction with
  | zero => simp
  | single_add t w f h₁ h₂ ih => simp [map_add,group_arbitrary_wire,ih]

theorem arbitrary_sum {S : ℕ} [Nonempty (Fin S)] (place : Fin k ↪ Fin S)
    {H : Type*} [Fintype H] (a : Widths k) (b : H → Widths k)
    (z : H → (∀ i, State a i) → F) (hz : (raw F a).coeff = ∑ h, z h)
    (tiles : ∀ h, ({raw F a with coeff := z h} : Raw (Fin k) F).Restricts (raw F (b h))) :
    ∃ Z : H → (∀ i, State (placeWidths place a) i) → F,
      (raw F (placeWidths place a)).coeff = ∑ h, Z h ∧
        ∀ h, ({raw F (placeWidths place a) with coeff := Z h} : Raw (Fin S) F).Restricts
          (raw F (placeWidths place (b h))) := by
  let X := raw F a
  let U (h : H) := ({X with coeff := z h} : Raw (Fin k) F).group place
  have comb : (X.group place).coeff = ∑ h, (U h).coeff := by
    change (fun x : (v : Fin S) → (p : {i // place i=v}) → X.Leg p.1 =>
      X.coeff ((groupIndexEquiv place X.Leg).symm x)) =
      ∑ h, (fun x => z h ((groupIndexEquiv place X.Leg).symm x))
    funext x
    change (raw F a).coeff _ = _
    simp only [hz,Finset.sum_apply]
    exact Finset.sum_apply _ _ _
  have rep (v : Widths k) :
      ofRaw ((raw F v).group place) = ofRaw (raw F (placeWidths place v)) := by
    change groupMulHom (K := F) place (ofRaw (raw F v)) = _
    rw [ofRaw_raw,ofRaw_raw,group_arbitrary_graph]
  have terms (h : H) : (U h).Restricts (raw F (placeWidths place (b h))) :=
    ofRaw_le_iff.mp ((ofRaw_le_iff.mpr (Raw.group_restricts place (tiles h))).trans_eq (rep _))
  obtain ⟨M,all,restr⟩ := transport_sum (X.group place) (raw F (placeWidths place a))
    (fun h => raw F (placeWidths place (b h))) (fun h => (U h).coeff) comb
    (ofRaw_le_iff.mp (rep a).symm.le) terms
  exact ⟨_,all,restr⟩


end Hierarchy.Probe
end

end OAI
