import OAI.ThreeFlat.Diagonal.CompressorHalfValues
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # Match the physical ordinal of a half-record to its port in the contraction -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks
variable {B S : Type} {d t : ℕ}

def home (e : Live B d t) : B × BitWord t := (e.1.1,e.2)
def atHome (u : B × BitWord t) (i : Fin d) : Live B d t := ((u.1,i),u.2)

def chartGraph (G : LiftedSlots B d (BitWord t)) (s : (B × BitWord t) ≃ S) : PortGraph S (Live B d t) :=
  ⟨fun e => s (home e),fun e => s (home (G.actualTarget e))⟩

variable (G : LiftedSlots B d (BitWord t)) (chart : (B × BitWord t) ≃ S) (u : B × BitWord t)

def outbound (i : Fin d) : (chartGraph G chart).Port (chart u) := ⟨(atHome u i,false),rfl⟩
def inbound (i : Fin d) : (chartGraph G chart).Port (chart u) :=
  ⟨(G.actualTarget.symm (atHome u i),true),by
    change chart (home (G.actualTarget (G.actualTarget.symm _)))=_
    rw [Equiv.apply_symm_apply]; rfl⟩

private def byPolarity : Fin d ⊕ Fin d ≃ (chartGraph G chart).Port (chart u) where
  toFun := Sum.elim (outbound G chart u) (inbound G chart u)
  invFun p := if p.val.2 then .inr (G.actualTarget p.val.1).1.2 else .inl p.val.1.1.2
  left_inv := by
    rintro (i|i)
    · rfl
    · change Sum.inr ((G.actualTarget (G.actualTarget.symm _)).1.2) = Sum.inr i
      rw [Equiv.apply_symm_apply]; rfl
  right_inv := by
    rintro ⟨⟨e,b⟩,h⟩
    cases b with
    | false =>
      change chart (home e)=chart u at h
      obtain rfl := chart.injective h
      rfl
    | true =>
      change chart (home (G.actualTarget e))=chart u at h
      obtain rfl := chart.injective h
      apply Subtype.ext
      change (G.actualTarget.symm (atHome (home (G.actualTarget e)) (G.actualTarget e).1.2),true)=(e,true)
      change (G.actualTarget.symm (G.actualTarget e),true)=(e,true)
      rw [Equiv.symm_apply_apply]

def portOrder : Fin (2*d) ≃ (chartGraph G chart).Port (chart u) :=
  ((finCongr (two_mul d)).trans finSumFinEquiv.symm).trans (byPolarity G chart u)

/-- The contraction port selected by any retained four-word record refers to its
source-coordinate edge and to the polarity recorded in that word. -/
theorem portOrder_value (j : Fin (2*d)) :
    (portOrder G chart u j).val=(sourceHalf G u j,decide (d≤j.val)) := by
  let e := (finCongr (two_mul d)).trans finSumFinEquiv.symm
  obtain ⟨x,rfl⟩ := e.symm.surjective j
  change ((byPolarity G chart u) (e (e.symm x))).val=_
  rw [Equiv.apply_symm_apply]
  cases x with
  | inl i =>
    have idx : (e.symm (.inl i)).val=i.val := rfl
    have slot : halfSlot (e.symm (.inl i))=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simp [byPolarity,outbound,sourceHalf,atHome,idx,slot,i.isLt,Nat.not_le.mpr i.isLt]
  | inr i =>
    have idx : (e.symm (.inr i)).val=d+i.val := rfl
    have slot : halfSlot (e.symm (.inr i))=i := by
      apply Fin.ext
      change (d+i.val)%d=i.val
      rw [Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]
    have h : d≤d+i.val := Nat.le_add_right ..
    simp [byPolarity,inbound,sourceHalf,atHome,idx,slot,h,not_lt_of_ge h]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Halves

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking Native
open scoped BigOperators Classical
noncomputable section

/-- The native first half lists outgoing slots and the second half lists inverse targets. -/
theorem half_total {B : Type} {q t : ℕ} (H : LiftedSlots B q (BitWord t))
    (w : ((B×Fin q)×BitWord t)→ℕ) (z : B×BitWord t) :
    (∑ j : Fin (2*q), w (ShrinkStage.Halves.sourceHalf H z j))=
      ∑ i : Fin q,(w ((z.1,i),z.2)+w (H.actualTarget.symm ((z.1,i),z.2))) := by
  let ord : Fin (2*q) ≃ Fin (q+q) := finCongr (two_mul q)
  let f (k : Fin (q+q)) := w (ShrinkStage.Halves.sourceHalf H z (ord.symm k))
  have front (j : Fin q) : f (j.castAdd q)=w ((z.1,j),z.2) := by
    let i := ord.symm (j.castAdd q)
    have vl : i.val=j.val := rfl
    have sl : ShrinkStage.Halves.halfSlot i=j := Fin.ext (by change i.val%q=j.val;rw [vl,Nat.mod_eq_of_lt j.isLt])
    change w (ShrinkStage.Halves.sourceHalf H z i)=_
    simp [ShrinkStage.Halves.sourceHalf,show i.val<q by rw [vl];exact j.isLt,sl]
  have back (j : Fin q) : f (Fin.natAdd q j)=w (H.actualTarget.symm ((z.1,j),z.2)) := by
    let i := ord.symm (Fin.natAdd q j)
    have vl : i.val=q+j.val := rfl
    have sl : ShrinkStage.Halves.halfSlot i=j := Fin.ext (by
      change i.val%q=j.val
      rw [vl,Nat.add_mod_left,Nat.mod_eq_of_lt j.isLt])
    change w (ShrinkStage.Halves.sourceHalf H z i)=_
    simp [ShrinkStage.Halves.sourceHalf,show ¬i.val<q by rw [vl];omega,sl]
  calc
    _ = ∑ j,f (ord j) := by simp only [f,Equiv.symm_apply_apply]
    _ = ∑ j,f j := ord.sum_comp f
    _ = _ := by rw [Fin.sum_univ_add];simp only [front,back,Finset.sum_add_distrib]

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
