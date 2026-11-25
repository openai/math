import OAI.Hierarchy.ProtocolRAMTurnOccurrence
import OAI.Hierarchy.ProtocolRAMTurnRead

namespace OAI
/-! # The raw occurrence addresses of consecutive canonical spine steps -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnStepOrder
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix ProtocolRAMTurnItinerary
open ProtocolRAM.Calendar CoreRoute
open scoped Classical

def offset (len : ℕ) (rev : Bool) (j : ℕ) := if rev then len-1-j else j

theorem previous (t : Turn) (q : ℕ) (pos : q+1=t.position) (bound : q < t.length) :
    t.occurrence false=t.origin+offset t.length t.reverse q := by
  cases h:t.reverse <;> simp [Turn.occurrence,offset,h] <;> omega

theorem next (t : Turn) (q : ℕ) (pos : q=t.position) (bound : q < t.length) :
    t.occurrence true=t.origin+offset t.length t.reverse q := by
  cases h:t.reverse <;> simp [Turn.occurrence,offset,h] <;> omega

theorem inverse_ordinal {E : Type} {K : ℕ} (a b : Fin K) (xs : List E)
    (j : Fin (oriented a b xs).length) :
    ((orientedIndex a b xs).symm j).val=offset xs.length (decide (¬a<b)) j.val := by
  by_cases h:a<b
  · simp [orientedIndex,offset,h]
  · have index : ((orientedIndex a b xs).symm j).val=xs.length-(j.val+1) := by
      rw [orientedIndex,dite_eq_right h]; rfl
    rw [index]
    simp [offset,h]; omega

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)
local notation "L" => B.matrixLayout inj pad
local notation "Count" => Fintype.card (Slots h d k)

/-- Inverse of the actual paid occurrence enumeration before the original
matrix-row renaming. Repeated occurrences of the same edge remain distinct. -/
def address (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : Fin ((L).steps s).length) : Fin (edges+Count) :=
  finSumFinEquiv ((Equiv.sumCongr (Equiv.refl _) (enum B o).symm) ((L).occurrences.symm ⟨s,j⟩))

theorem address_val (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : Fin ((L).steps s).length) :
    (address B inj pad o s j).val = ProtocolRAMTurnGeometry.origin o s+
      offset (ProtocolRAMTurnGeometry.length s) (reverse B inj pad s) j.val := by
  rcases s with e|i|c
  · change Fin 1 at j
    fin_cases j
    rfl
  · let u := (orientedIndex ((L).goods.tail i) ((L).goods.head i) (B.ordinary i)).symm j
    let t : Fin (arity i) := ⟨u.val,u.isLt.trans_le (ProtocolRAMTurnGeometry.length_ordinary B i).le⟩
    change edges+(slotOrder o (.inl ⟨i,t⟩)).val=_
    rw [←ProtocolRAMTurnGeometry.goods_at o i t]
    apply congrArg (ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inl i))+·)
    simpa only [t,u,reverse,ProtocolRAMTurnGeometry.length_ordinary B i] using
      inverse_ordinal ((L).goods.tail i) ((L).goods.head i) (B.ordinary i) j
  · let u := (orientedIndex ((L).reserve.tail c) ((L).reserve.head c) (B.centers c)).symm j
    let t : Fin 2 := ⟨u.val,u.isLt.trans_le (ProtocolRAMTurnGeometry.length_center B c).le⟩
    change edges+(slotOrder o (.inr ⟨c,t⟩)).val=_
    rw [←ProtocolRAMTurnGeometry.center_at o c t]
    apply congrArg (ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inr c))+·)
    simpa only [t,u,reverse,ProtocolRAMTurnGeometry.length_center B c] using
      inverse_ordinal ((L).reserve.tail c) ((L).reserve.head c) (B.centers c) j

theorem actual_order (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : Fin ((L).steps s).length) :
    (L).nativeOrder (enum B o) (address B inj pad o s j)=
      (Equiv.sigmaCongrLeft (β:=fun i=>Fin ((L).steps i).length) Layout.numbered).symm ⟨s,j⟩ := by
  let p := (L).occurrences.symm ⟨s,j⟩
  let join := Equiv.sumCongr (Equiv.refl (Fin edges)) (enum B o)
  let rename := Equiv.sigmaCongrLeft (β:=fun i=>Fin ((L).steps i).length) Layout.numbered
  change rename.symm ((L).occurrences (join (finSumFinEquiv.symm (finSumFinEquiv (join.symm p)))))=_
  have cancel := (congrArg join (finSumFinEquiv.symm_apply_apply (join.symm p))).trans (join.apply_symm_apply p)
  exact congrArg rename.symm ((congrArg (L).occurrences cancel).trans ((L).occurrences.apply_symm_apply ⟨s,j⟩))

theorem actual_edge (s : ProtocolRAMTurnGeometry.Source edges h d k) (j : Fin ((L).steps s).length) :
    (L).nativeEdge (enum B o) (address B inj pad o s j)=((L).steps s).get j := by
  let p := (L).occurrences.symm ⟨s,j⟩
  let get := fun t : Σ i, Fin ((L).steps i).length => ((L).steps t.1).get t.2
  have obs : get ((L).occurrences p) = Sum.elim id RouteOccurrence.edge p := (L).occurrence_edge p
  have back : (L).occurrences p = ⟨s,j⟩ := (L).occurrences.apply_symm_apply _
  let join := Equiv.sumCongr (Equiv.refl (Fin edges)) (enum B o)
  change Sum.elim id RouteOccurrence.edge (join (finSumFinEquiv.symm (finSumFinEquiv (join.symm p))))=_
  have cancel := (congrArg join (finSumFinEquiv.symm_apply_apply (join.symm p))).trans (join.apply_symm_apply p)
  exact (congrArg (Sum.elim id RouteOccurrence.edge) cancel).trans (obs.symm.trans (congrArg get back))

end Hierarchy.ProtocolRAMTurnStepOrder

end
end OAI
