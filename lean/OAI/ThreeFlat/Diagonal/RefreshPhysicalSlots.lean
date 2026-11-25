import OAI.ThreeFlat.Diagonal.RefreshHistory
import OAI.ThreeFlat.Diagonal.ParallelSlotRewrite
import OAI.ThreeFlat.Diagonal.PaddedSlotNumbering
import OAI.ThreeFlat.Diagonal.DoublePorts

namespace OAI
/-! # Physical slot numbering of the shared bundles, sparse arcs, and refresh padding -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander
open scoped Classical BigOperators
noncomputable section

variable {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] {m h : ℕ}

abbrev LiveSlot (V L : Type) (m d : ℕ) := ((V × Fin m) × Fin d) × L

def actualPortGraph {d : ℕ} (T : LiftedSlots (V × Fin m) d L) : PortGraph ((V × L) × Fin m) (LiveSlot V L m d) :=
  let site := fun e : LiveSlot V L m d => ((e.1.1.1,e.2),e.1.1.2)
  ⟨site,fun e => site (T.actualTarget e)⟩

def extSlots : (V × L) × Fin m ≃ LiveSlot V L m 1 where
  toFun p := (((p.1.1,p.2),0),p.1.2)
  invFun p := ((p.1.1.1,p.2),p.1.1.2)
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨v,s⟩,k⟩; obtain ⟨v,i⟩ := v; exact congrArg (fun j => (((v,i),j),k)) (Subsingleton.elim _ _)

def sparseSlots {E : Type} (number : E ≃ Fin m × Fin h) : (Σ _ : V × L, E) ≃ LiveSlot V L m h where
  toFun a := (((a.1.1,(number a.2).1),(number a.2).2),a.1.2)
  invFun p := ⟨(p.1.1.1,p.2),number.symm (p.1.1.2,p.1.2)⟩
  left_inv := by rintro ⟨⟨u,g⟩,e⟩; simp
  right_inv := by rintro ⟨⟨⟨u,i⟩,k⟩,g⟩; simp

def refreshSlots {E : Type} (number : E ≃ Fin m × Fin h) (pad : ℕ) :
    (RawEdge (fun _ : V × L => E) m ⊕ LiveSlot V L m pad) ≃ LiveSlot V L m (1+h+pad) :=
  (((extSlots.sumCongr (sparseSlots number)).trans
    (CompressorRefresh.unionLabels _ L _ _)).sumCongr (Equiv.refl _)).trans
    (CompressorRefresh.unionLabels _ L _ _)

omit [Fintype L] in
theorem union_actual_right {V' : Type} {a b : ℕ} (A : LiftedSlots V' a L) (B : LiftedSlots V' b L)
    (p : (V' × Fin b) × L) :
    (CompressorRefresh.union A B).actualTarget (CompressorRefresh.unionLabels V' L a b (.inr p)) =
      CompressorRefresh.unionLabels V' L a b (.inr (B.actualTarget p)) := by
  obtain ⟨p,g⟩ := p
  simp [CompressorRefresh.unionLabels_right, LiftedSlots.actualTarget,CompressorRefresh.union,
    CompressorRefresh.unionTarget_right]

variable (G : LiftedSlots V m (C × L)) (c : Fin m → Fin m → ℕ)
variable (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0)

def ports : PortGraph (Fin m) (Arc c) := ⟨arcStart,arcEnd⟩

abbrev numbering := DoublePorts.arcNumber (Equiv.refl (Fin m)) c rows
abbrev outputGraph (hm : 2 ≤ m) (pad : ℕ) :=
  CompressorRefresh.graph G (DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero) hm pad

omit [Fintype V] [AddCommGroup C] [Fintype L] in
/-- Both actual half-incidences have the sites used by the grouped algebraic
formula, with one external slot and the numbered sparse row at every port. -/
theorem refresh_ends (hm : 2 ≤ m) (pad : ℕ) (e : RawEdge (fun _ : V × L => Arc c) m) (side : Bool) :
    (actualPortGraph (outputGraph G c sym rows zero hm pad)).vertex
      (refreshSlots (numbering c rows) pad (.inl e)) side =
      (rawGraph (externalSite G) (fun _ => ports c)).vertex e side := by
  rcases e with (⟨⟨v,g⟩,s⟩ | ⟨⟨v,g⟩,e⟩) <;> cases side with
  | false => rfl
  | true =>
    simp only [PortGraph.vertex, actualPortGraph,outputGraph,CompressorRefresh.graph,refreshSlots,Equiv.trans_apply,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,CompressorRefresh.union_actual_left,union_actual_right]
    first
    | exact rfl
    | simp [sparseSlots,numbering,rawGraph,ports,arcEnd,DoublePorts.arcNumber,CompressorRefresh.unionLabels_left,CompressorRefresh.unionLabels_right,CompressorRefresh.slotCases,
        CompressorRefresh.internal]
      change ((DoublePorts.ofMatrix (Equiv.refl (Fin m)) c sym rows zero).target
        (DoublePorts.arcNumber (Equiv.refl (Fin m)) c rows e)).1 = e.fst.2
      rw [DoublePorts.ofMatrix_target]
      rfl

/-- Word width of an actual numbered refresh arc. -/
def freshWidth (b : RawEdge (fun _ : V × L => Arc c) m → ℕ) (pad : ℕ) (e : LiveSlot V L m (1+h+pad)) :=
  Sum.elim b (fun _ => 0) ((refreshSlots (numbering c rows) pad).symm e)

def physicalRefresh (hm : 2 ≤ m) (pad : ℕ) (A : RawEdge (fun _ : V × L => Arc c) m → Type)
    (b : RawEdge (fun _ : V × L => Arc c) m → ℕ) (pack : ∀ e, A e ≃ Fin (2^b e)) :
    SlotRefinement.Refines (rawGraph (externalSite G) (fun _ => ports c)) A
      (actualPortGraph (outputGraph G c sym rows zero hm pad))
      (fun e => Fin (2^freshWidth c rows b pad e)) := by
  let cover := refreshSlots (V := V) (L := L) (numbering c rows) pad
  let num := ((Equiv.sigmaUnique _ (fun _ : RawEdge (fun _ : V × L => Arc c) m => Unit)).sumCongr (Equiv.refl _)).trans cover
  let width := freshWidth c rows b pad
  letI : ∀ p : LiveSlot V L m pad, Unique (Fin (2^width (num (.inr p)))) := fun p => by
    change Unique (Fin (2^Sum.elim b (fun _ => 0) (cover.symm (cover (.inr p)))))
    simp; infer_instance
  apply SlotRefinement.parallel num _ _ _ _ _ _
  · intro e
    apply (pack e).trans
    refine (finCongr ?_).trans (Equiv.piUnique (fun i : Unit => Fin (2^width (num (.inl ⟨e,i⟩))))).symm
    change 2^b e = 2^Sum.elim b (fun _ => 0) (cover.symm (cover (.inl e)))
    simp
  · intro e i side
    exact refresh_ends G c sym rows zero hm pad e side

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
