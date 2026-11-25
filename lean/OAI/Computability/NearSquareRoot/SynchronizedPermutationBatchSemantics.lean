import OAI.Computability.NearSquareRoot.CRTControlledBenesParallel

/-! # Batching the physical switches in a packed Beneš stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes

variable {E B V : Type*}

/-- A batch executes its assigned blocks and parks all other block fields. -/
def batchStage (which : B → ℕ) (w : B → ℕ) (t : E → B → RawTable)
    (a : Bool × ℕ) (n : ℕ) : Equiv.Perm (PackedAddress E w) :=
  controlledPerm fun e b =>
    if which b = n then stagePerm (t e b) a.1 a.2 else Equiv.refl _

/-- The prefix of the batch list executes exactly the blocks numbered below its length. -/
theorem batchStage_prefix (which : B → ℕ) (w : B → ℕ) (t : E → B → RawTable)
    (a : Bool × ℕ) (n : ℕ) (v : PackedAddress E w → V) :
    (List.range n).foldl (fun arr s => scatter (batchStage which w t a s) arr) v =
      scatter (controlledPerm fun e b =>
        if which b < n then stagePerm (d := w b) (t e b) a.1 a.2 else Equiv.refl _) v := by
  induction n with
  | zero =>
    funext y
    change v y = v (_,_)
    congr 1
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,ih]
    funext y
    change v (_,_) = v (_,_)
    congr 1
    apply Prod.ext
    · rfl
    funext b
    by_cases h : which b < n
    · have hne : which b ≠ n := by omega
      have hs : which b < n+1 := by omega
      simp [batchStage,controlledPerm,h,hne,hs]
    · by_cases he : which b = n
      · simp [batchStage,controlledPerm,he]
      · have hs : ¬ which b < n+1 := by omega
        simp [batchStage,controlledPerm,h,he,hs]

/-- The complete batch list acts as the original simultaneous switch on the data array. -/
theorem batchStage_run (which : B → ℕ) (w : B → ℕ) (t : E → B → RawTable)
    (a : Bool × ℕ) (batches : ℕ) (hw : ∀ b, which b < batches)
    (v : PackedAddress E w → V) :
    (List.range batches).foldl (fun arr s => scatter (batchStage which w t a s) arr) v =
      scatter (packedStage w t a) v := by
  rw [batchStage_prefix]
  simp [hw,packedStage]

/-- Chronological sequence of stage/batch pairs used by the physical directory. -/
def batchOrder (D batches : ℕ) : List ((Bool × ℕ) × ℕ) :=
  (executionOrder D).flatMap fun a => (List.range batches).map (a,·)

@[simp] theorem batchOrder_length (D batches : ℕ) :
    (batchOrder D batches).length = 2*D*batches := by
  have count (L : List (Bool × ℕ)) :
      (L.flatMap fun a => (List.range batches).map (a,·)).length = L.length*batches := by
    induction L with
    | nil => simp
    | cons a L ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  simpa only [batchOrder,executionOrder_length] using count (executionOrder D)

/-- Scattering the records at every physical batch realizes the selected block permutation. -/
theorem batchData_run (which : B → ℕ) (w : B → ℕ) (t : E → B → RawTable)
    (p : E → (b : B) → Equiv.Perm (Word (w b))) (ht : ∀ e b, RawRepresents (p e b) (t e b))
    (D batches : ℕ) (hw : ∀ b, w b ≤ D) (hwhich : ∀ b, which b < batches)
    (v : PackedAddress E w → V) :
    (batchOrder D batches).foldl (fun arr s => scatter (batchStage which w t s.1 s.2) arr) v =
      scatter (controlledPerm p) v := by
  have stages (L : List (Bool × ℕ)) (arr : PackedAddress E w → V) :
      (L.flatMap fun a => (List.range batches).map (a,·)).foldl
          (fun f s => scatter (batchStage which w t s.1 s.2) f) arr =
        L.foldl (fun f a => scatter (packedStage w t a) f) arr := by
    induction L generalizing arr with
    | nil => rfl
    | cons a L ih =>
      simp only [List.flatMap_cons,List.foldl_append,List.foldl_map,List.foldl_cons,ih]
      rw [batchStage_run which w t a batches hwhich]
  exact (stages (executionOrder D) v).trans (packedData_run w t p ht D hw v)

end Benes

end NearSquareRoot
end Computability
end OAI
