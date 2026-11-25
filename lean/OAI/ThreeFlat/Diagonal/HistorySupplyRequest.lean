import OAI.ThreeFlat.Diagonal.HistoryCrossPort
import OAI.ThreeFlat.Diagonal.HistoryScopeOffsets
import OAI.ThreeFlat.Diagonal.HistoryMaskOrder

namespace OAI
/-! # The precise hidden or fresh callback of an occupied party's supply port -/
namespace ThreeFlat.Diagonal
open LinearAlgebra.SpectralBooks MotifBinaryPacking HistoryContraction MotifKernel
open scoped Classical BigOperators

namespace HistoryMaskOrder
open private count from OAI.ThreeFlat.Diagonal.HistoryMaskOrder

theorem strictMono {a : ℕ} (active : Fin a→Prop) : StrictMono (fun i => (order active i).val) := by
  intro i j h
  exact ((Finset.univ.filter active).orderIsoOfFin (count active)).strictMono h

end HistoryMaskOrder

namespace MotifKernel.PrivateOrder
variable {J G E : Type} [Fintype J] [Fintype G] [Fintype E] [DecidableEq G]
  {P : PortGraph J E} {site : J→G} {v : G} {I : E→Type} [∀e,Fintype (I e)]

def onSide (party : {j // site j=v}) (q : P.Port party.val)
    (cross : wireOwner P.tail P.head site q.val.1=none) : ExternalAt P site v := by
  refine ⟨⟨q.val.1,cross⟩,?_⟩
  obtain ⟨⟨e,b⟩,atParty⟩:=q
  cases b
  · exact Or.inl ((congrArg site atParty).trans party.property)
  · exact Or.inr ((congrArg site atParty).trans party.property)

omit [Fintype J] [Fintype G] [Fintype E] in
theorem owner_of_non_crossing (party : {j // site j=v}) (q : P.Port party.val)
    (localEdge : wireOwner P.tail P.head site q.val.1≠none) :
    wireOwner P.tail P.head site q.val.1=some v := by
  obtain ⟨⟨e,side⟩,atParty⟩:=q
  have same : site (P.tail e)=site (P.head e) := by
    by_contra apart
    exact localEdge (ite_eq_right apart)
  cases side
  · exact (ite_eq_left same).trans (congrArg some ((congrArg site atParty).trans party.property))
  · exact (ite_eq_left same).trans (congrArg some (same.trans ((congrArg site atParty).trans party.property)))

omit [Fintype J] [Fintype G] [Fintype E] [(e : E) → Fintype (I e)] in
theorem absorbed_request (D : PrivateOrder P site v I) {p : ℕ}
    (fresh : (a : ExternalAt P site v)→Fin (D.width a.val.val)→Fin p)
    (party : {j // site j=v}) (q : P.Port party.val) (bit : Fin (D.width q.val.1))
    (own : wireOwner P.tail P.head site q.val.1=some v) :
    D.partySource fresh party q bit=.hidden (D.privateBit ⟨q.val.1,own⟩ bit) := by
  obtain ⟨⟨e,b⟩,he⟩:=q
  have here : site (P.tail e)=site (P.head e) := by
    by_contra miss
    simp [wireOwner,miss] at own
  cases b <;> simp [partySource,here,id]

omit [Fintype J] [Fintype G] [Fintype E] [(e : E) → Fintype (I e)] in
theorem crossing_request (D : PrivateOrder P site v I) {p : ℕ}
    (fresh : (a : ExternalAt P site v)→Fin (D.width a.val.val)→Fin p)
    (party : {j // site j=v}) (q : P.Port party.val) (bit : Fin (D.width q.val.1))
    (other : wireOwner P.tail P.head site q.val.1=none) :
    D.partySource fresh party q bit=.pin (fresh (onSide party q other) bit) := by
  obtain ⟨⟨e,b⟩,he⟩:=q
  have apart : site (P.tail e)≠site (P.head e) := by
    intro same
    simp [wireOwner,same] at other
  cases b <;> simp [partySource,apart,onSide,id]

omit [Fintype J] [Fintype G] [(e : E) → Fintype (I e)] in
/-- Interpreting scope 3 sums the widths of precisely the earlier absorbed
edges in the native eight-edge order, then adds the bit within this edge. -/
theorem privateBit_ordered [LinearOrder E] (D : PrivateOrder P site v I)
    (ordered : StrictMono (fun i => (D.edge i).val)) (a : Absorbed P site v)
    (j : Fin (D.width a.val)) :
    (D.privateBit a j).val =
      (∑ b ∈ Finset.univ.filter (fun e => wireOwner P.tail P.head site e=some v ∧ e<a.val),D.width b)+j.val := by
  classical
  rw [D.privateBit_val]
  congr 1
  let i:=D.edge.symm a
  have atI : (D.edge i).val=a.val:=congrArg Subtype.val (D.edge.apply_symm_apply a)
  apply Finset.sum_bij (fun k _=>(D.edge (Fin.castLE i.isLt.le k)).val)
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(D.edge _).property,by rw [←atI];exact ordered k.isLt⟩
  · intro x _ y _ h
    exact Fin.ext (congrArg (fun z : Fin D.count => z.val) (D.edge.injective (Subtype.ext h)))
  · intro b hb
    obtain ⟨_,own,small⟩:=Finset.mem_filter.mp hb
    let k:=D.edge.symm ⟨b,own⟩
    have pos:(D.edge k).val=b := congrArg Subtype.val (D.edge.apply_symm_apply ⟨b,own⟩)
    have smallIndex : k < i := ordered.lt_iff_lt.mp (show (D.edge k).val < (D.edge i).val by rw [pos,atI]; exact small)
    exact ⟨⟨k.val,smallIndex⟩,Finset.mem_univ _,pos⟩
  · intro _ _
    rfl

theorem masked_order_strict {a : ℕ} (active : Fin a→Prop) :
    StrictMono (fun i=>(HistoryMaskOrder.order active i).val) :=
  HistoryMaskOrder.strictMono active

end MotifKernel.PrivateOrder

namespace SlotRefinement
variable {V E D Pad : Type} [Fintype V] [Fintype E] [Fintype D]
    (S : PortGraph V E) (T : PortGraph V D) (n b : E→ℕ) (positive : ∀ e,0<n e)
    (cover : ((Σ e,Fin (n e)) ⊕ Pad) ≃ D)
    (ends : ∀ e (i : Fin (n e)) side,T.vertex (cover (.inl ⟨e,i⟩)) side=S.vertex e side)

noncomputable def freshRequest {v : V} (x : S.Port v) (j : Fin (b x.val.1)) :
    Σ p : T.Port v, Fin (actualWidth n b cover p.val.1) :=
  let part := (SlotEnergy.pieceIndex _ _ (positive x.val.1)).symm j
  let p : T.Port v:=⟨(cover (.inl ⟨x.val.1,part.1⟩),x.val.2),(ends _ _ _).trans x.property⟩
  ⟨p,Fin.cast (by simp [p,actualWidth]) part.2⟩

omit [Fintype V] [Fintype E] [Fintype D] in
theorem piecePin_request {v : V} {k : ℕ} (addr : (p : T.Port v)→Fin (actualWidth n b cover p.val.1)→Fin k)
    (x : S.Port v) (j : Fin (b x.val.1)) :
    let z:=freshRequest S T n b positive cover ends x j
    piecePin S T n b positive cover ends addr x j=addr z.1 z.2 := rfl

end SlotRefinement
end ThreeFlat.Diagonal

end OAI
