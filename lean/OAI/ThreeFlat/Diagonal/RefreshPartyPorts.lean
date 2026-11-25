import OAI.ThreeFlat.Diagonal.RefreshPhysicalSlots

namespace OAI
/-! # Per-party endpoint ordinals in the fixed refresh ROM -/

namespace ThreeFlat.Diagonal.RefreshParty

open LinearAlgebra.SpectralBooks RefreshTies Expander
open scoped Classical BigOperators
noncomputable section

variable {m h : ℕ}

/-- Polarity banks in increasing address order. -/
def bankOrder (n : ℕ) : Bool × Fin n ≃ Fin (2*n) :=
  ({ toFun := fun p => if p.1 then .inr p.2 else .inl p.2
     invFun := Sum.elim (fun i=>(false,i)) (fun i=>(true,i))
     left_inv := by rintro ⟨b,i⟩; cases b <;> rfl
     right_inv := by rintro (i|i) <;> rfl } : Bool × Fin n ≃ Fin n ⊕ Fin n).trans
    (finSumFinEquiv.trans (finCongr (two_mul n).symm))

theorem bank_index {n : ℕ} (b : Bool) (i : Fin n) :
    (bankOrder n (b,i)).val=(if b then n else 0)+i.val := by cases b <;> simp [bankOrder, Nat.add_comm]

/-- Each direction has two local endpoints even on a dense loop. -/
def denseEnds (p : Fin m) : (Bool × Bool × Fin m) ≃ (RefreshMotif.denseGraph m).Port p where
  toFun z := if z.2.1 then ⟨((z.1,z.2.2,p),true),rfl⟩ else ⟨((z.1,p,z.2.2),false),rfl⟩
  invFun q := (q.1.1.1,q.1.2,if q.1.2 then q.1.1.2.1 else q.1.1.2.2)
  left_inv := by rintro ⟨dir,side,j⟩; cases side <;> rfl
  right_inv := by
    rintro ⟨⟨⟨dir,i,j⟩,b⟩,endpoint⟩
    cases b with
    | false => change i=p at endpoint; subst p; rfl
    | true => change j=p at endpoint; subst p; rfl

/-- The order installed for the demand-coordinate slots in the physical
kernel ROM. The inner bank selects the two endpoints of a tie. -/
def denseOrder (p : Fin m) : Fin (4*m) ≃ (RefreshMotif.denseGraph m).Port p :=
  ((Equiv.prodCongr (Equiv.refl Bool) (bankOrder m)).trans
    ((bankOrder (2*m)).trans (finCongr (by omega)))).symm.trans (denseEnds p)

theorem dense_index (p j : Fin m) (dir side : Bool) :
    ((denseOrder p).symm (denseEnds p (dir,side,j))).val =
      ((if dir then 2 else 0)+(if side then 1 else 0))*m+j.val := by
  simp only [denseOrder,Equiv.symm_trans_apply,Equiv.symm_apply_apply,Equiv.symm_symm,
    Equiv.trans_apply,Equiv.prodCongr_apply]
  change (bankOrder (2*m) (dir,bankOrder m (side,j))).val = _
  rw [bank_index, bank_index]
  cases dir <;> cases side <;> simp; omega

variable (c : Fin m → Fin m → ℕ) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)

private def sparseEnds (p : Fin m) : Bool × Fin h ≃ (ports c).Port p where
  toFun z :=
    let e := (numbering c rows).symm (p,z.2)
    if z.1 then ⟨(DoublePorts.reverseArc c sym e,true),rfl⟩ else ⟨(e,false),rfl⟩
  invFun q := (q.1.2,(numbering c rows (if q.1.2 then DoublePorts.reverseArc c sym q.1.1 else q.1.1)).2)
  left_inv := by
    rintro ⟨b,i⟩
    have invol (e : Expander.Arc c) :
        DoublePorts.reverseArc c sym (DoublePorts.reverseArc c sym e) = e := by
      obtain ⟨⟨u,v⟩,j⟩ := e
      rfl
    cases b <;> simp [invol]
  right_inv := by
    rintro ⟨⟨e,b⟩,hp⟩
    cases b with
    | false =>
      change e.1.1=p at hp
      subst p
      apply Subtype.ext
      change ((numbering c rows).symm (numbering c rows e),false)=(e,false)
      rw [Equiv.symm_apply_apply]
    | true =>
      change e.1.2=p at hp
      subst p
      apply Subtype.ext
      change (DoublePorts.reverseArc c sym ((numbering c rows).symm
        (numbering c rows (DoublePorts.reverseArc c sym e))),true)=(e,true)
      rw [Equiv.symm_apply_apply]
      rfl

def sparseOrder (p : Fin m) : Fin (2*h) ≃ (ports c).Port p :=
  (bankOrder h).symm.trans (sparseEnds c sym rows p)

theorem sparse_index (p : Fin m) (q : (ports c).Port p) :
    ((sparseOrder c sym rows p).symm q).val = (if q.1.2 then h else 0)+
      (numbering c rows (if q.1.2 then DoublePorts.reverseArc c sym q.1.1 else q.1.1)).2.val := by
  exact bank_index _ _

end
end ThreeFlat.Diagonal.RefreshParty

end OAI
