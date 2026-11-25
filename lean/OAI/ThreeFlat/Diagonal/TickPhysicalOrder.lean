import OAI.ThreeFlat.Diagonal.TemplateDiagonal

namespace OAI
/-! # Single-step chronological entries of the actual physical tick template -/

namespace ThreeFlat.Diagonal.TickPhysicalOrder

open scoped Classical
noncomputable section

/-- The templates use a block index and a local counter. Their matrix
product is the chronological product with natural counter block*n+offset. -/
theorem indices {Z : Type*} [Monoid Z] (blocks n : ℕ) (f : ℕ → Z) :
    (List.ofFn fun k : Fin blocks => (List.ofFn fun j : Fin n => f (k.val*n+j.val)).prod).prod =
    ((List.range (blocks*n)).map f).prod := by
  have row (l : ℕ) : (List.ofFn fun j : Fin n => f (l+j.val)) = (List.range n).map (fun j => f (l+j)) := by
    apply List.ext_getElem
    · simp
    · intros; simp
  induction blocks with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ_last,List.prod_append,Nat.succ_mul,List.range_add,List.map_append,List.prod_append]
    simpa only [Fin.val_castSucc,Fin.val_last,List.prod_singleton,List.map_map,Function.comp_def,row] using
      congrArg (fun a => a*((List.range n).map (fun j => f (k*n+j))).prod) ih

variable {F I D A : Type*} [Field F] [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]
    [Fintype A] [DecidableEq A]

def untouched (side : Bool) (i : I) (x y : Bool → I → D) : Prop :=
  x (!side) = y (!side) ∧ ∀ j, j ≠ i → x side j = y side j

omit [Fintype D] in
theorem physical_entry (side : Bool) (i : I) (K : D → D → Matrix A A F)
    (x y : Bool → I → D) (a b : A) :
    physicalTick side i K (x,a) (y,b) = if untouched side i x y then K (x side i) (y side i) a b else 0 := by
  simp only [physicalTick,halfLift,Matrix.submatrix_apply,halfEquiv,Equiv.coe_fn_mk,
    Matrix.blockDiagonal_apply,orderedBlock,List.map_singleton,List.prod_singleton,List.mem_singleton]
  by_cases passive : x (!side) = y (!side) <;>
    by_cases elsewhere : ∀ j, j ≠ i → x side j = y side j <;> simp [untouched,passive,elsewhere]

def unpack {N : ℕ} (order : Fin N ≃ Bool × I) : (Fin N → D) ≃ (Bool → I → D) where
  toFun z side i := z (order.symm (side,i))
  invFun x k := x (order k).1 (order k).2
  left_inv z := by funext k; simp
  right_inv z := by funext side i; simp

def state {N : ℕ} (order : Fin N ≃ Bool × I) : ((Fin N → D) × A) ≃ MachineState I D A :=
  (unpack order).prodCongr (Equiv.refl _)

omit [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D] in
theorem untouched_iff {N : ℕ} (order : Fin N ≃ Bool × I) (k : Fin N) (x y : Fin N → D) :
    untouched (order k).1 (order k).2 (unpack order x) (unpack order y) ↔ ∀ j, j ≠ k → x j = y j := by
  have idx (j : Fin N) : order.symm ((order j).1,(order j).2) = j := by simp
  constructor
  · rintro ⟨passive,rest⟩ j ne
    by_cases same : (order j).1 = (order k).1
    · have other : (order j).2 ≠ (order k).2 := fun eq => ne (order.injective (Prod.ext same eq))
      have h := rest (order j).2 other
      change x (order.symm ((order k).1,(order j).2)) = y (order.symm ((order k).1,(order j).2)) at h
      simpa only [← same,idx] using h
    · have opp : (order j).1 = !(order k).1 := by
        cases hj : (order j).1 <;> cases hk : (order k).1 <;> simp_all
      have h := congrFun passive (order j).2
      change x (order.symm (!(order k).1,(order j).2)) = y (order.symm (!(order k).1,(order j).2)) at h
      simpa only [← opp,idx] using h
  · intro outside
    constructor
    · funext i
      apply outside
      intro h
      have bad := congrArg Prod.fst ((order.symm_apply_eq.mp h).symm)
      have noFixed (b : Bool) : b ≠ !b := by cases b <;> decide
      exact noFixed (order k).1 bad
    · intro i ne
      apply outside
      intro h
      exact ne (congrArg Prod.snd (order.symm_apply_eq.mp h))

omit [Fintype D] in
theorem entry {N : ℕ} (order : Fin N ≃ Bool × I) (k : Fin N) (K : D → D → Matrix A A F)
    (x y : Fin N → D) (a b : A) :
    (physicalTick (order k).1 (order k).2 K).submatrix (state order) (state order) (x,a) (y,b) =
      if ∀ j, j≠k → x j=y j then K (x k) (y k) a b else 0 := by
  change physicalTick _ _ K (unpack order x,a) (unpack order y,b) = _
  rw [physical_entry,untouched_iff]
  simp [unpack]

/-- The times in the original external template are unchanged by the
passage to consecutive natural tick counters. -/
theorem template {p a q n blocks : ℕ} (N : BitNetwork F p)
    (slot : Fin blocks → Fin n → I) (active : Fin blocks → Bool)
    (pins : Fin blocks → Fin n → Fin q → BitString a → BitString a → BitString a → BitString a → Fin p → Bool)
    (M : ℕ → Matrix (MachineState I (BitString a) (BitString a)) (MachineState I (BitString a) (BitString a)) F)
    (run : ∀ t : Fin blocks, ∀ j : Fin n,
      physicalTick (active t) (slot t j) (teamTick N (pins t) j) = M (t.val*n+j.val)) :
    templateRun N (List.ofFn id) slot active pins =
      ((List.range (blocks*n)).map M).prod.submatrix (fun x => (x,fun _ => false)) (fun y => (y,fun _ => false)) := by
  unfold templateRun
  rw [List.map_ofFn]
  simp only [Function.comp_def,id_eq,run,indices]

end
end ThreeFlat.Diagonal.TickPhysicalOrder

end OAI
