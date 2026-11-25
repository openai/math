import OAI.ThreeFlat.Diagonal.HistogramBitAddresses
import OAI.ThreeFlat.Diagonal.ParallelSlotRewrite
import OAI.ThreeFlat.Diagonal.HistorySupplyPointers

namespace OAI
/-! # Pointers to the actual half-slots of a balanced history subdivision -/

namespace ThreeFlat.Diagonal.SlotRefinement

noncomputable section

open LinearAlgebra.SpectralBooks MotifBinaryPacking HistoryContraction MotifKernel
open scoped Classical BigOperators

variable {V E D Pad : Type} [Fintype V] [Fintype E] [Fintype D] {A : E → Type} [∀ e, Fintype (A e)]
    (S : PortGraph V E) (T : PortGraph V D) (n b : E → ℕ) (hn : ∀ e, 0<n e)
    (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) (code : ∀ e, A e ≃ Fin (2^b e))
    (ends : ∀ e (i : Fin (n e)) side, T.vertex (cover (.inl ⟨e,i⟩)) side = S.vertex e side)

private def slot {v : V} (x : S.Port v) (i : Fin (n x.1.1)) : T.Port v :=
  ⟨(cover (.inl ⟨x.1.1,i⟩),x.1.2),(ends _ _ _).trans x.property⟩

omit [Fintype V] [Fintype E] [Fintype D] in
private theorem slotWidth {v : V} (x : S.Port v) (i : Fin (n x.1.1)) :
    actualWidth n b cover (slot S T n cover ends x i).1.1 = SlotEnergy.piece (b x.1.1) (n x.1.1) i := by
  simp [slot,actualWidth]

/-- Once the selected balanced piece is known, its pin is addressed at the
local bit offset on the same side of the numbered physical edge. -/
noncomputable def pieceSource {p h : ℕ} {v : V}
    (addr : (a : T.Port v) → Fin (actualWidth n b cover a.1.1) → BitSource h p)
    (x : S.Port v) (j : Fin (b x.1.1)) : BitSource h p :=
  let part := (SlotEnergy.pieceIndex _ _ (hn x.1.1)).symm j
  addr (slot S T n cover ends x part.1) (Fin.cast (slotWidth S T n b cover ends x part.1).symm part.2)

omit [Fintype E] [Fintype D] [(e : E) → Fintype (A e)] in
private theorem part_val (e : E) (x : A e) (i : Fin (n e)) :
    (actualWords A n b hn cover code e x i).val = (splitWord _ _ (hn e) (code e x) i).val := rfl

omit [Fintype V] [Fintype E] [Fintype D] [(e : E) → Fintype (A e)] in
theorem pieceSource_read {p h : ℕ} {v : V} (ys : T.State (fun a => Fin (2^actualWidth n b cover a)) v)
    (addr : (a : T.Port v) → Fin (actualWidth n b cover a.1.1) → BitSource h p)
    (g : Fin h → Bool) (pin : Fin p → Bool) (read : ∀ a t, (addr a t).read g pin = (ys a).val.testBit t.val)
    (x : S.Port v) (j : Fin (b x.1.1)) :
    (pieceSource S T n b hn cover ends addr x j).read g pin =
      (code _ ((balanced S A T n b hn cover code ends).read v ys x)).val.testBit j.val := by
  let old := (balanced S A T n b hn cover code ends).read v ys x
  have oldPiece (i : Fin (n x.1.1)) : actualWords A n b hn cover code _ old i = ys (slot S T n cover ends x i) :=
    congrFun ((actualWords A n b hn cover code x.1.1).apply_symm_apply _) i
  obtain ⟨⟨i,t⟩,rfl⟩ := (SlotEnergy.pieceIndex _ _ (hn x.1.1)).surjective j
  unfold pieceSource
  simp only [read,Fin.val_cast]
  let readPiece (z : Σ i : Fin (n x.1.1), Fin (SlotEnergy.piece (b x.1.1) (n x.1.1) i)) :=
    (ys (slot S T n cover ends x z.1)).val.testBit z.2.val
  have undo := (SlotEnergy.pieceIndex (b x.1.1) (n x.1.1) (hn x.1.1)).symm_apply_apply ⟨i,t⟩
  refine (congrArg readPiece undo).trans ?_
  change (ys (slot S T n cover ends x i)).val.testBit t.val = (code _ old).val.testBit _
  rw [←oldPiece i,part_val]
  exact split_piece _ _ _ _

end

end ThreeFlat.Diagonal.SlotRefinement

end OAI
