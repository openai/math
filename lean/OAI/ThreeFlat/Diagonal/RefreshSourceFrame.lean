import OAI.ThreeFlat.Diagonal.RefreshInputBounds

namespace OAI
/-! # Retaining the true refresh source through writes to later directory arrays -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RefreshDemandRows CompressorPacking.Native

variable {W v a t : ℕ} {current : Word W} {m : Memory W}
    {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)} {C : SlotImage.Columns}
    {split : ℕ} {w : SlotImage.RefreshInput v a t → ℕ}

/-- Runtime cells read by a refresh demand span. Common header fields are
retained through offset 19, the last directory slot read by the width pass. -/
def sourceCell (current head : ℕ) (C : SlotImage.Columns) (split oldWidths i : ℕ) :=
  i=current ∨ head≤ i ∧ i≤head+19 ∨ C.graph≤ i ∧ i<C.graph+6*C.rows ∨
  C.widths≤ i ∧ i<C.widths+oldWidths ∨ split≤ i ∧ i<split+3*C.rows

theorem Source.frame (s : Source current m G C split w) (m' : Memory W)
    (keep : ∀ i, sourceCell current.val (m current.val).val C split (v*mPort a*(mPort a*2^t)) i → m' i=m i) :
    Source current m' G C split w := by
  let count := v*mPort a*(mPort a*2^t)
  have ptr : m' current.val=m current.val := keep _ (Or.inl rfl)
  have header (off : ℕ) (h : off≤19) :
      info (fun i=>(m' i).val) current off=info (fun i=>(m i).val) current off := by
    dsimp only [info]
    rw [ptr,keep _ (Or.inr (Or.inl ⟨by omega,by omega⟩))]
  have edge (i : ℕ) (l : C.graph≤ i) (r : i<C.graph+6*C.rows) : m' i=m i :=
    keep _ (Or.inr (Or.inr (Or.inl ⟨l,r⟩)))
  have widths (i : ℕ) (l : C.widths≤ i) (r : i<C.widths+count) : m' i=m i :=
    keep _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨l,r⟩))))
  have data (i : ℕ) (l : split≤ i) (r : i<split+3*C.rows) : m' i=m i :=
    keep _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨l,r⟩))))
  have shifted (p : Fin v × Fin (mPort a)) (back : Bool) :
      m' (SlotImage.cell C (Equiv.refl _) p back 2)=m (SlotImage.cell C (Equiv.refl _) p back 2) :=
    edge _ (SlotImage.cell_range s.image p back 2).1 (SlotImage.cell_range s.image p back 2).2
  have splitWord (p : Fin v × Fin (mPort a)) : SlotImage.ordinal (Equiv.refl _) p<C.rows := by
    rw [s.image.rowCount]; exact SlotImage.ordinal_lt _ p
  refine ⟨s.image.frame (fun i l u => congrArg Fin.val (edge i l u))
    (fun i l u => congrArg Fin.val (widths i l u)),?_,ptr ▸ s.headerBound,
    (header 8 (by decide)).trans s.remaining,(header 9 (by decide)).trans s.width,
    (header 10 (by decide)).trans s.graph,(header 11 (by decide)).trans s.rows,
    (header 12 (by decide)).trans s.splitBase,s.graphBound,s.widthBound,s.shiftsBound⟩
  constructor
  · intro p
    have h := splitWord p
    rw [data _ (by omega) (by omega),shifted p false]
    exact s.shifts.forward p
  · intro p
    have h := splitWord p
    rw [data _ (by omega) (by omega),shifted p true]
    exact s.shifts.reverse p
  · intro p
    have h := splitWord p
    rw [data _ (by omega) (by omega),shifted p true]
    exact s.shifts.consumed p


end ThreeFlat.Diagonal.RefreshStageNav

end OAI
