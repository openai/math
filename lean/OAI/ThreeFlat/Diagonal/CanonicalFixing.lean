import OAI.ThreeFlat.Diagonal.PhysicalBlock

namespace OAI
/-! # Eliminating the forced words in a block fixing

The two external endpoints determine all old and new touched chunks. The
initial and final auxiliary words also come from the endpoints. Exactly one
free auxiliary word remains at each internal boundary.
-/

namespace ThreeFlat.Diagonal

variable {F S A I : Type*} [Field F] [Fintype S] [DecidableEq S] [Inhabited S]
  [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I] {n : ℕ}

theorem endWord_succ_last {B : Type*} (n : ℕ) (z : B) (v : Fin (n+1) → B) :
    endWord (n+1) z v = v (Fin.last n) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => exact ih (v 0) (fun i => v i.succ)

/-- Reconstruct every word in a consistent block fixing from its free interior. -/
def canonicalFixing (atSlot : Fin (n+1) → I) (active : Bool) (x y : MachineState I S A)
    (interior : Fin n → A) : BlockFixing (n+1) S A :=
  (x.1 active ∘ atSlot, y.1 active ∘ atSlot, x.2, Fin.snoc interior y.2)

/-- With general catalyst matrices, projecting onto endpoints leaves only the
sum over intermediate auxiliary words and equality of all preserved active chunks. -/
theorem approximate_fixings_entry (atSlot : Fin (n+1) → I) (active : Bool)
    (X : BlockFixing (n+1) S A → Matrix (I → S) (I → S) F)
    (x y : MachineState I S A) :
    (∑ f : BlockFixing (n+1) S A, physicalFixing atSlot active f (X f)) x y =
      if ∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i then
        ∑ h : Fin n → A, X (canonicalFixing atSlot active x y h) (x.1 (!active)) (y.1 (!active))
      else 0 := by
  classical
  let good : Prop := ∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i
  let L := x.1 active ∘ atSlot
  let R := y.1 active ∘ atSlot
  have entry (f : BlockFixing (n+1) S A) :
      physicalFixing atSlot active f (X f) x y =
        if good then
          if L = f.1 then
            if R = f.2.1 then
              if x.2 = f.2.2.1 then
                if y.2 = f.2.2.2 (Fin.last n) then X f (x.1 (!active)) (y.1 (!active))
                else 0
              else 0
            else 0
          else 0
        else 0 := by
    rw [physicalFixing, physical_fixing_entry]
    simp only [touchedEnd, Prod.mk.injEq, endWord_succ_last]
    change (if (L = f.1 ∧ x.2 = f.2.2.1) ∧ (R = f.2.1 ∧ y.2 = f.2.2.2 (Fin.last n)) ∧ good
        then _ else _) = _
    split_ifs <;> simp_all
  rw [Matrix.sum_apply]
  simp_rw [entry]
  change _ = if good then _ else _
  by_cases hg : good
  · simp only [hg, ite_true, Fintype.sum_prod_type, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ]
    let along (v : Fin (n+1) → A) :=
      if y.2 = v (Fin.last n) then X (L,R,x.2,v) (x.1 (!active)) (y.1 (!active)) else 0
    change ∑ v, along v = _
    rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => A)).sum_comp along, Fintype.sum_prod_type]
    simp [along, Fin.snocEquiv, canonicalFixing, L, R, Finset.sum_ite_irrel]
  · simp only [hg, ite_false, Finset.sum_const_zero]

end ThreeFlat.Diagonal

end OAI
