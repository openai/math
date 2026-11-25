import OAI.ThreeFlat.Diagonal.ShrinkSubdivision

namespace OAI
/-! # The physical order of the halves incident at a regular compressor site -/

namespace ThreeFlat.Diagonal.CompressorPacking.HalfOrder
open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks
variable {V Tag L : Type} {d : ℕ} [AddCommGroup L]

def atSlot (v : Site V Tag L) (i : Fin d) : Numbered V Tag L d :=
  (((v.1,v.2.1),i),v.2.2)

omit [AddCommGroup L] in
@[simp] theorem at_numbered (e : Numbered V Tag L d) : atSlot (numberedSite e) e.1.2 = e := rfl
omit [AddCommGroup L] in
@[simp] theorem numbered_at (v : Site V Tag L) (i : Fin d) : numberedSite (atSlot v i) = v := rfl

variable (G : LiftedSlots (V × Tag) d L) (v : Site V Tag L)

def outgoing (i : Fin d) : (slotPortGraph G).Port v := ⟨(atSlot v i,false),rfl⟩

def incoming (i : Fin d) : (slotPortGraph G).Port v := by
  refine ⟨(G.actualTarget.symm (atSlot v i),true),?_⟩
  change numberedSite (G.actualTarget (G.actualTarget.symm (atSlot v i))) = v
  rw [Equiv.apply_symm_apply,numbered_at]

def bySide : Fin d ⊕ Fin d ≃ (slotPortGraph G).Port v where
  toFun := Sum.elim (outgoing G v) (incoming G v)
  invFun p := if p.val.2 then .inr ((G.actualTarget p.val.1).1.2) else .inl p.val.1.1.2
  left_inv s := by
    cases s with
    | inl i => rfl
    | inr i =>
      change Sum.inr ((G.actualTarget (G.actualTarget.symm (atSlot v i))).1.2) = Sum.inr i
      rw [Equiv.apply_symm_apply]
      rfl
  right_inv p := by
    rcases p with ⟨⟨e,b⟩,h⟩
    cases b with
    | false =>
      change numberedSite e = v at h
      subst v
      rfl
    | true =>
      change numberedSite (G.actualTarget e) = v at h
      subst v
      apply Subtype.ext
      change (G.actualTarget.symm (atSlot (numberedSite (G.actualTarget e)) (G.actualTarget e).1.2),true) = (e,true)
      rw [at_numbered,Equiv.symm_apply_apply]

def order : Fin (2*d) ≃ (slotPortGraph G).Port v :=
  ((finCongr (two_mul d)).trans finSumFinEquiv.symm).trans (bySide G v)

def outOrdinal (i : Fin d) : Fin (2*d) := (finCongr (two_mul d)).symm (finSumFinEquiv (.inl i))
def inOrdinal (i : Fin d) : Fin (2*d) := (finCongr (two_mul d)).symm (finSumFinEquiv (.inr i))

@[simp] theorem order_out (i : Fin d) : order G v (outOrdinal i) = outgoing G v i := by
  simp [order,outOrdinal,bySide]
@[simp] theorem order_in (i : Fin d) : order G v (inOrdinal i) = incoming G v i := by
  simp only [order, inOrdinal, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]; rfl

@[simp] theorem outOrdinal_val (i : Fin d) : (outOrdinal i).val = i.val := rfl
@[simp] theorem inOrdinal_val (i : Fin d) : (inOrdinal i).val = d+i.val := rfl

end ThreeFlat.Diagonal.CompressorPacking.HalfOrder

end OAI
