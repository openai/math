import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementExtraction
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementOrder

/-! # Factoring the old contraction into its canonical record tensors -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace PortGraph.PatchRecord.Partition

open UniformDecorations
variable {V E A J B : Type} [Fintype V] [Fintype E] [DecidableEq V] [Fintype J] {K : ℕ}
variable (P : Partition V J K) (M : RootedMap V E) (z : V → A) (name : V ↪ ℕ)
variable {w : ℕ} (U : Tables B w)

private theorem dart_eq {n : ℕ} {θ : Fin n → MapType} {d t : PatchDart θ}
    (h : d.1 = t.1) (k : d.2.val = t.2.val) : d = t := by
  rcases d with ⟨v,b⟩
  rcases t with ⟨u,c⟩
  obtain rfl : v = u := h
  exact congrArg (Sigma.mk v) (Fin.ext k)

omit [Fintype J] in
private theorem internal_read (j : J) (i : (P.record M z name j).shape.Vertex)
    (d : (P.record M z name j).toPiece.graph.Port i) :
    let R := (P.record M z name j).shape
    R.read (.inl d.val) = ⟨i,R.slotEquiv i (.inl d)⟩ := by
  let R := (P.record M z name j).shape
  have hi : (R.read (.inl d.val)).1 = i := (R.read_internal_owner _ _).trans d.property
  exact dart_eq hi (R.slotEquiv_internal_val d).symm

omit [Fintype J] in
private theorem stub_read (j : J) (i : (P.record M z name j).shape.Vertex)
    (d : {t // (P.record M z name j).toPiece.attach t = i}) :
    let R := (P.record M z name j).shape
    d.val.val = ⟨i,R.slotEquiv i (.inr d)⟩ := by
  let R := (P.record M z name j).shape
  exact dart_eq d.property (R.slotEquiv_stub_val d).symm

omit [Fintype J] in
/-- On an actual edge assignment the old shared table reads the same word at
each slot as its copy in the canonical record. -/
theorem entry_oldTable (a : E → Bits w) (j : J) (i : (P.record M z name j).shape.Vertex) :
    (view M).localize U (P.vertexAt name j i) (M.graph.atVertex a _) =
      (P.record M z name j).shape.oldTable U i
        ((P.record M z name j).toPiece.graph.atVertex (fun e => a (P.wireEquiv M z name j e).val) i)
        (fun t => a ((P.cutDarts M z name ⟨j,t.val⟩).1.val)) := by
  let R := (P.record M z name j).shape
  apply congrArg (U (M.typeAt (P.vertexAt name j i)))
  funext k
  obtain ⟨(p | s),rfl⟩ := (R.slotEquiv i).surjective k
  · let f (t : R.Dart) := a (actual M (P.vertexAt name j) t).1
    change f ⟨i,R.slotEquiv i (.inl p)⟩ =
      Sum.elim _ _ ((R.slotEquiv i).symm (R.slotEquiv i (.inl p)))
    rw [Equiv.symm_apply_apply]
    have hp := congrArg (fun d : E × Bool => a d.1) (wire_darts M (P.vertexAt name j) z (Finset.card_pos.mpr (P.nonempty j)) (P.bounded j) p.val.1 p.val.2)
    exact (congrArg f (P.internal_read M z name j i p).symm).trans hp
  · let f (t : R.Dart) := a (actual M (P.vertexAt name j) t).1
    change f ⟨i,R.slotEquiv i (.inr s)⟩ =
      Sum.elim _ _ ((R.slotEquiv i).symm (R.slotEquiv i (.inr s)))
    rw [Equiv.symm_apply_apply]
    exact congrArg f (P.stub_read M z name j i s).symm

/-- Split a global assignment into one exterior choice per paired wire and
one separate assignment of internal wires per record. -/
def splitState :
    (E → Bits w) ≃ ((M.graph.CrossEdge P.part → Bits w) ×
      ((j : J) → (P.record M z name j).shape.toPiece.Edge → Bits w)) :=
  (((P.oldEdge M z name).symm.arrowCongr (Equiv.refl _)).trans
    (Equiv.sumPiEquivProdPi (fun _ => Bits w))).trans
      ((Equiv.refl _).prodCongr (Equiv.piCurry (fun _ _ => Bits w)))

set_option maxHeartbeats 500000 in
/-- The old map contraction is the state sum of the original record
coefficients contracted along the actual paired stubs. -/
theorem eval_eq_sum_records [CommSemiring B] :
    eval M U = ∑ x : M.graph.CrossEdge P.part → Bits w,
      ∏ j, (P.record M z name j).shape.oldValue U
        (fun s => x ((P.cutDarts M z name ⟨j,s⟩).1)) := by
  unfold eval contraction PatchShape.oldValue openValue
  simp_rw [Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  let left (a : E → Bits w) := ∏ v, (view M).localize U v (M.graph.atVertex a v)
  let right (x : (M.graph.CrossEdge P.part → Bits w) ×
        ((i : J) → (P.record M z name i).shape.toPiece.Edge → Bits w)) :=
    ∏ i, ∏ v, (P.record M z name i).shape.oldTable U v
      ((P.record M z name i).toPiece.graph.atVertex (x.2 i) v)
      (fun t => x.1 ((P.cutDarts M z name ⟨i,t.val⟩).1))
  change (∑ a : E → Bits w, left a) = ∑ x, right x
  refine @Fintype.sum_equiv _ _ B ?_ ?_ inferInstance (P.splitState (w := w) M z name) left right ?_
  intro a
  let term (v : vertices (P.record M z name)) :=
    (P.record M z name v.1).shape.oldTable U v.2
      ((P.record M z name v.1).toPiece.graph.atVertex (fun e => a (P.wireEquiv M z name v.1 e).val) v.2)
      (fun t => a ((P.cutDarts M z name ⟨v.1,t.val⟩).1.val))
  refine Eq.trans ?_ (Fintype.prod_sigma term)
  refine Fintype.prod_equiv (P.oldVertex M z name).symm _ term ?_
  intro v
  obtain ⟨⟨j,i⟩,rfl⟩ := (P.oldVertex M z name).surjective v
  rw [Equiv.symm_apply_apply]
  exact P.entry_oldTable M z name U a j i

end PortGraph.PatchRecord.Partition

end

end SpectralBooks
end LinearAlgebra
end OAI
