import OAI.ThreeFlat.Diagonal.PhysicalScalar
import OAI.ThreeFlat.Diagonal.OrderedTicks
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.FinRange

namespace OAI
/-! # The original transition product on the two physical halves

Within one block the inactive half stays fixed. Every visited slot is
distinct, so summing the genuine single-tick transitions gives exactly the
sum over fixed blocks used in the rank argument.
-/

namespace ThreeFlat.Diagonal

variable {I S A F : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype A] [DecidableEq A] [Field F] {n : ℕ}

/-- Read active chunk and auxiliary memory together, with the inactive half
as a separate, fixed index. -/
def halfEquiv (active : Bool) : MachineState I S A ≃ ((I → S) × A) × (I → S) where
  toFun x := ((x.1 active, x.2), x.1 (!active))
  invFun p := (fun side => if side = active then p.1.1 else p.2, p.1.2)
  left_inv := by
    rintro ⟨u,a⟩
    apply Prod.ext
    · funext b
      cases active <;> cases b <;> rfl
    · rfl
  right_inv := by
    rintro ⟨⟨u,a⟩,v⟩
    cases active <;> rfl

/-- Act on one half and the auxiliary word, tensoring with the identity on
the other half. -/
noncomputable def halfLift (active : Bool) (M : Matrix ((I → S) × A) ((I → S) × A) F) :
    Matrix (MachineState I S A) (MachineState I S A) F :=
  (Matrix.blockDiagonal fun _ : I → S => M).submatrix (halfEquiv active) (halfEquiv active)

private theorem halfLift_prod (active : Bool) (l : List (Matrix ((I → S) × A) ((I → S) × A) F)) :
    (l.map (halfLift active)).prod = halfLift active l.prod := by
  induction l with
  | nil =>
    change 1 = (Matrix.blockDiagonal (1 : (I → S) → Matrix ((I → S) × A) ((I → S) × A) F)).submatrix
      (halfEquiv active) (halfEquiv active)
    rw [Matrix.blockDiagonal_one, Matrix.submatrix_one_equiv]
  | cons t l ih =>
    simp only [List.map_cons, List.prod_cons, ih, halfLift, Matrix.submatrix_mul_equiv,
      Matrix.blockDiagonal_mul]

/-- The chronological tick matrix, including the identity on the inactive
half and on every other active chunk. -/
noncomputable def physicalTick (active : Bool) (i : I) (K : S → S → Matrix A A F) :
    Matrix (MachineState I S A) (MachineState I S A) F :=
  halfLift active (orderedBlock (fun _ => K) [i])

/-- Distinct slot addresses within each aligned block turn the whole
single-tick chronological matrix product into the actual fixing sum. -/
theorem physical_ticks_eq_fixings [Inhabited S] (atSlot : Fin n → I) (hi : Function.Injective atSlot)
    (active : Bool) (tick : Fin n → S → S → Matrix A A F) :
    (List.ofFn fun i => physicalTick active (atSlot i) (tick i)).prod =
      ∑ f : BlockFixing n S A, physicalFixing atSlot active f (fixingWeight tick f • 1) := by
  classical
  let K := Function.extend atSlot tick (fun _ => 0)
  let slots := List.ofFn atSlot
  have hK i : K (atSlot i) = tick i := hi.extend_apply tick _ i
  have hlist : (List.ofFn fun i => physicalTick active (atSlot i) (tick i)) =
      (slots.map fun i => orderedBlock K [i]).map (halfLift active) := by
    rw [List.map_map]
    simp only [slots, List.map_ofFn, Function.comp_def]
    congr 1
    funext i
    unfold physicalTick
    congr 1
    ext x y
    simp [orderedBlock, hK]
  rw [hlist, halfLift_prod, ordered_ticks_eq K slots (List.nodup_ofFn.mpr hi)]
  ext x y
  rw [scalar_fixings_entry]
  simp only [halfLift, Matrix.submatrix_apply, halfEquiv, Equiv.coe_fn_mk,
    Matrix.blockDiagonal_apply, orderedBlock]
  have hout : (∀ i ∉ slots, x.1 active i = y.1 active i) ↔
      ∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i := by
    simp [slots, List.mem_ofFn]
  simp only [hout, slots, List.map_ofFn, Function.comp_def, hK]
  split_ifs <;> simp_all

end ThreeFlat.Diagonal

end OAI
