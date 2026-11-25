import OAI.Hierarchy.DescentLaneGates

namespace OAI
/-! # Arithmetic addresses before and after transposing a physical packed word by lane -/

namespace Hierarchy.DescentLaneGates
open DescentKernelHistory DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {A : Type} {width : A→ℕ} {r m p q : ℕ}

/-- Manufacture an affine read from an actual indexed finite word and its arithmetic stride law. -/
def affine (hp : 0<p) (a : A) (read : Fin p→Fin (width a)) (step : ℕ)
    (law : ∀j,(read j).val=(read ⟨0,hp⟩).val+step*j.val) : Lane p width where
  port:=a
  start:=(read ⟨0,hp⟩).val
  stride:=step
  fits j:=by rw [←law j];exact (read j).isLt

theorem affine_at (hp : 0<p) (a : A) (read : Fin p→Fin (width a)) (step : ℕ)
    (law : ∀j,(read j).val=(read ⟨0,hp⟩).val+step*j.val) (j : Fin p) :
    (affine hp a read step law).atBit j=⟨a,read j⟩ := by
  exact congrArg (Sigma.mk a) (Fin.ext (law j).symm)

/-- The old within-word order is (layer, full digit, slot bit). Each new named lane is a
particular layer, group and slot bit, and contains p consecutive carried digits. -/
abbrev Block (r m b : ℕ) := Fin r × Fin m × Fin b

def splitOrder {X S B T : Type} : ((X×S×B)×T) ≃ X×((S×T)×B) where
  toFun z:=(z.1.1,(z.1.2.1,z.2),z.1.2.2)
  invFun z:=((z.1,z.2.1.1,z.2.2),z.2.1.2)
  left_inv _:=rfl
  right_inv _:=rfl

def blockBit (r m p b : ℕ) : Block r m b × Fin p ≃ Fin (r*((m*p)*b)) :=
  splitOrder.trans ((Equiv.prodCongr (Equiv.refl (Fin r))
    ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin b))).trans finProdFinEquiv)).trans finProdFinEquiv)

theorem blockBit_val (b : ℕ) (t : Block r m b) (d : Fin p) :
    (blockBit r m p b (t,d)).val=t.2.2.val+b*(d.val+p*t.2.1.val+(m*p)*t.1.val) := by
  change t.2.2.val + b * (d.val + p * t.2.1.val) + (m*p*b) * t.1.val = _
  ring

theorem blockBit_slope (hp : 0<p) (b : ℕ) (t : Block r m b) (d : Fin p) :
    (blockBit r m p b (t,d)).val=(blockBit r m p b (t,⟨0,hp⟩)).val+b*d.val := by
  simp only [blockBit_val,zero_add];ring

def distribute {I T : Type} (U : I→Type) : ((Σi,U i)×T)≃(Σi,U i×T) where
  toFun z:=⟨z.1.1,z.1.2,z.2⟩
  invFun z:=(⟨z.1,z.2.1⟩,z.2.2)
  left_inv _:=rfl
  right_inv _:=rfl

variable (subSize len : Fin q→ℕ) (fit : ∀i,len i=r*((m*p)*subSize i))
abbrev SpineRow := Σi : Fin q,Block r m (subSize i)

def spineBit : SpineRow (r:=r) (m:=m) subSize × Fin p ≃ Fin (∑i,len i) :=
  (distribute _).trans ((Equiv.sigmaCongrRight fun i=>(blockBit r m p (subSize i)).trans (finCongr (fit i).symm)).trans finSigmaFinEquiv)

theorem spineBit_slope (hp : 0<p) (row : SpineRow (r:=r) (m:=m) subSize) (d : Fin p) :
    (spineBit subSize len fit (row,d)).val=(spineBit subSize len fit (row,⟨0,hp⟩)).val+subSize row.1*d.val := by
  change (finSigmaFinEquiv ⟨row.1,Fin.cast (fit row.1).symm (blockBit r m p (subSize row.1) (row.2,d))⟩).val =
    (finSigmaFinEquiv ⟨row.1,Fin.cast (fit row.1).symm (blockBit r m p (subSize row.1) (row.2,⟨0,hp⟩))⟩).val+_
  simp only [finSigmaFinEquiv_apply,Fin.val_cast]
  rw [blockBit_slope hp (subSize row.1) row.2 d,Nat.add_assoc]

def groupOrder (r m : ℕ) (subSize : Fin q→ℕ) : SpineRow (r:=r) (m:=m) subSize ≃ Fin (∑i,r*(m*subSize i)) :=
  (Equiv.sigmaCongrRight fun i=>(Equiv.prodCongr (Equiv.refl (Fin r))
    (finProdFinEquiv (m:=m) (n:=subSize i))).trans finProdFinEquiv).trans finSigmaFinEquiv

include fit in
theorem packed_width : (∑i,r*(m*subSize i))*p=∑i,len i := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _=>by rw [fit i];ring

/-- Fixed transposition on the actual complete word. Every lane now occupies a consecutive p-block. -/
def transpose : Equiv.Perm (Fin (∑i,len i)) := (spineBit subSize len fit).symm.trans
  (((Equiv.prodCongr (groupOrder r m subSize) (Equiv.refl (Fin p))).trans finProdFinEquiv).trans (finCongr (packed_width subSize len fit)))

theorem transpose_lane (row : SpineRow (r:=r) (m:=m) subSize) (d : Fin p) :
    (transpose subSize len fit (spineBit subSize len fit (row,d))).val=p*(groupOrder r m subSize row).val+d.val := by
  simp [transpose,finProdFinEquiv,Nat.add_comm]

end
end Hierarchy.DescentLaneGates

end OAI
