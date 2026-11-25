import OAI.ThreeFlat.Diagonal.SlotBaseChart
import OAI.ThreeFlat.Diagonal.CompressorUnionImage

namespace OAI
/-! # Naturality of the refresh output slot graph under base numbering -/

namespace ThreeFlat.Diagonal.SlotImage

open Computability.VPVNP.Compression CompressorRefresh

variable {B C H L : Type} {a b d n : ℕ}

/-- Each directed slot lookup and its shift agree in the two base charts. -/
structure Chart (G : LiftedSlots B d L) (H : LiftedSlots C d L) (f : B ≃ C) : Prop where
  oriented : ∀ p b, SlotImage.oriented H b (baseSlots f p)=baseSlots f (SlotImage.oriented G b p)
  shift : ∀ p b, SlotImage.shift H b (baseSlots f p)=SlotImage.shift G b p

theorem ownChart (G : LiftedSlots B d L) (f : B ≃ C) : Chart G (inBaseChart G f) f where
  oriented p b := by cases b <;> first | exact chart_target G f p | exact chart_reverse G f p
  shift p b := by cases b <;> simp [SlotImage.shift,inBaseChart]

theorem Chart.union {A : LiftedSlots B a L} {A' : LiftedSlots C a L}
    {P : LiftedSlots B b L} {P' : LiftedSlots C b L} {f : B ≃ C}
    (x : Chart A A' f) (y : Chart P P' f) : Chart (union A P) (union A' P') f := by
  have left (p : B × Fin a) : baseSlots f (leftRow (b:=b) p)=leftRow (baseSlots f p) := rfl
  have right (p : B × Fin b) : baseSlots f (rightRow (a:=a) p)=rightRow (baseSlots f p) := rfl
  constructor
  · intro p back
    obtain ⟨q,rfl⟩ := (slotCases B a b).symm.surjective p
    rcases q with q|q
    · change SlotImage.oriented (CompressorRefresh.union A' P') back (baseSlots f (leftRow q)) =
        baseSlots f (SlotImage.oriented (CompressorRefresh.union A P) back (leftRow q))
      rw [left,oriented_left,oriented_left,x.oriented,left]
    · change SlotImage.oriented (CompressorRefresh.union A' P') back (baseSlots f (rightRow q)) =
        baseSlots f (SlotImage.oriented (CompressorRefresh.union A P) back (rightRow q))
      rw [right,oriented_right,oriented_right,y.oriented,right]
  · intro p back
    obtain ⟨q,rfl⟩ := (slotCases B a b).symm.surjective p
    rcases q with q|q
    · change SlotImage.shift (CompressorRefresh.union A' P') back (baseSlots f (leftRow q)) =
        SlotImage.shift (CompressorRefresh.union A P) back (leftRow q)
      rw [left,shift_left,shift_left,x.shift]
    · change SlotImage.shift (CompressorRefresh.union A' P') back (baseSlots f (rightRow q)) =
        SlotImage.shift (CompressorRefresh.union A P) back (rightRow q)
      rw [right,shift_right,shift_right,y.shift]

theorem Chart.external {G : LiftedSlots B d (H×L)} {G' : LiftedSlots C d (H×L)} {f : B ≃ C}
    (old : Chart G G' f) : Chart (external G) (external G') (baseSlots f) where
  oriented p b := by
    have h := old.oriented p.1 b
    cases b <;> exact congrArg (fun q=>(q,p.2)) h
  shift p b := by
    have h := congrArg Prod.snd (old.shift p.1 b)
    cases b <;> exact h

theorem internalChart [Zero L] (f : B ≃ C) (E : SlotGraph (Fin d) a) :
    Chart (internal (L:=L) B E) (internal C E) (baseSlots f) where
  oriented p b := by cases b <;> rfl
  shift p b := by cases b <;> rfl

theorem Chart.refresh [Zero L] {G : LiftedSlots B d (H×L)} {G' : LiftedSlots C d (H×L)} {f : B ≃ C}
    (old : Chart G G' f) (E : SlotGraph (Fin d) a) (hd : 2≤d) (pad : ℕ) :
    Chart (graph G E hd pad) (graph G' E hd pad) (baseSlots f) :=
  ((old.external).union (internalChart f E)).union (internalChart f (padding hd pad))

variable {u u' lanes : ℕ}

theorem Chart.pull_stored {G : LiftedSlots B d L} {G' : LiftedSlots C d L} {f : B ≃ C}
    (h : Chart G G' f) (base : B ≃ Fin u) (base' : C ≃ Fin u') (lane : L ≃ Fin lanes) (size : u=u')
    (matchBase : ∀ p, (base' (f p)).val=(base p).val) (K : Columns) (mem : ℕ → ℕ)
    (w : Edge B L d → ℕ) (w' : Edge C L d → ℕ) (matchWidth : ∀ e,w' (baseEdges f e)=w e)
    (stored : Stored G' base' lane K mem w') : Stored G base lane K mem w where
  rowCount := by rw [size]; exact stored.rowCount
  graph p b i := by
    have r := stored.graph (baseSlots f p) b i
    have key : cell K base' (baseSlots f p) b i=cell K base p b i := by simp [cell,ordinal,baseSlots,matchBase]
    rw [key] at r
    rw [r]
    unfold fields
    rw [h.oriented p b,h.shift p b]
    change ![(base' (f (SlotImage.oriented G b p).1)).val,(SlotImage.oriented G b p).2.val,
      (lane (SlotImage.shift G b p)).val] i = _
    rw [matchBase]
  widthWord e := by
    have r := stored.widthWord (baseEdges f e)
    rw [matchWidth e] at r
    simpa [edgeOrdinal,ordinal,baseEdges,baseSlots,matchBase] using r


end ThreeFlat.Diagonal.SlotImage

end OAI
