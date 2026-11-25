import OAI.Computability.NearSquareRoot.CRTTablePackedRun

/-! # Exact execution of all compiled CRT switch layers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

def depthOrder (d : ℕ) : List (Fin (Nat.clog 2 d)) :=
  (List.finRange (Nat.clog 2 d)).map fun r =>
    ⟨Nat.clog 2 d - 1 - r.val, by have := r.isLt; omega⟩

private theorem depthOrder_rows (d : ℕ) :
    (depthOrder d).map (fun n => Stage.atDepth d n.val n.isLt) = Stage.bottomUp d := by
  simp [depthOrder,Stage.bottomUp,List.map_map,Function.comp_def]

/-- Ordered sequence of individual, simultaneous Beneš layers. Inverting
the padded CRT reverses the order of the depths and uses the inverse tables
at each depth. The local switch interpreter is identical in both directions. -/
def switchOrder (d D : ℕ) (inv : Bool) : List (Fin (Nat.clog 2 d) × Bool × ℕ) :=
  (bif inv then (depthOrder d).reverse else depthOrder d).flatMap
    fun n => (Benes.executionOrder D).map (fun t => (n,t))

theorem switchOrder_length (d D : ℕ) (inv : Bool) :
    (switchOrder d D inv).length = (Nat.clog 2 d)*(2*D) := by
  cases inv <;> simp [switchOrder,depthOrder,List.length_flatMap,Function.comp_def]

variable {d : ℕ} (a w : Fin d → ℕ) [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)

/-- A single switch stage, interpreted on the original address axes by the
typed packing equivalence for this particular depth. -/
noncomputable def switchPerm (inv : Bool) (s : Fin (Nat.clog 2 d) × Bool × ℕ) :
    Equiv.Perm ((g : Fin d) → AxisValue a w g) :=
  let n := s.1.val
  let e := packAddress a w hwidth n
  let f := Benes.packedStage (fun b => w (targetAxis d n b)) (packedTables a w hwidth n inv) s.2
  e.trans (f.trans e.symm)

private theorem fold_conjugate {A B T : Type*} (e : A ≃ B) (f : T → Equiv.Perm B)
    (ts : List T) (x : A) :
    e (ts.foldl (fun y t => (e.trans ((f t).trans e.symm)) y) x) =
      ts.foldl (fun y t => f t y) (e x) := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    exact (ih (e.symm (f t (e x)))).trans (congrArg (fun z => ts.foldl (fun y t => f t y) z)
      (e.apply_symm_apply _))

private theorem switchDepth (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (n : Fin (Nat.clog 2 d))
    (inv : Bool) (D : ℕ) (bound : ∀ g, w g ≤ D) (x : (g : Fin d) → AxisValue a w g) :
    let row := Stage.layerPerm a (fun g => Fin (2^w g-a g)) (Stage.atDepth d n.val n.isLt)
    (Benes.executionOrder D).foldl (fun y t => switchPerm a w hwidth inv (n,t) y) x =
      (bif inv then row.symm else row) x := by
  apply (packAddress a w hwidth n.val).injective
  exact (fold_conjugate (packAddress a w hwidth n.val) (Benes.packedStage
    (fun b => w (targetAxis d n.val b)) (packedTables a w hwidth n.val inv))
    (Benes.executionOrder D) x).trans (packedStages_apply_row a w hwidth hdense hcop n.val n.isLt inv D bound x)

private theorem foldRows (E : Fin d → Type) (rows : List (List (Stage d))) (x : CRT.Address a E)
    (inv : Bool) : (bif inv then rows.reverse else rows).foldl (fun y r =>
      (bif inv then (Stage.layerPerm a E r).symm else Stage.layerPerm a E r) y) x =
      (bif inv then (Stage.layersPerm a E rows).symm else Stage.layersPerm a E rows) x := by
  cases inv with
  | false =>
    change rows.foldl (fun y r => Stage.layerPerm a E r y) x = Stage.layersPerm a E rows x
    induction rows generalizing x with
    | nil => rfl
    | cons r rs ih => exact ih _
  | true =>
    change rows.reverse.foldl (fun y r => (Stage.layerPerm a E r).symm y) x = (Stage.layersPerm a E rows).symm x
    induction rows generalizing x with
    | nil => rfl
    | cons r rs ih => simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Stage.layersPerm, Equiv.symm_trans_apply, ih]

/-- The product of the binary switches obtained from actual serialized CRT
tables, including all padding and both directions, is the desired full
address permutation. The same schedule permits any padded common block
width greater than or equal to every axis width. -/
theorem switchOrder_run (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (D : ℕ) (bound : ∀ g, w g ≤ D)
    (inv : Bool) (x : (g : Fin d) → AxisValue a w g) :
    (switchOrder d D inv).foldl (fun y t => switchPerm a w hwidth inv t y) x =
      (bif inv then (CRT.paddedPermutation a (fun g => Fin (2^w g - a g))).symm
        else CRT.paddedPermutation a (fun g => Fin (2^w g - a g))) x := by
  let E := fun g => Fin (2^w g-a g)
  let run := fun (y : (g : Fin d) → AxisValue a w g) (n : Fin (Nat.clog 2 d)) =>
    let row := Stage.layerPerm a E (Stage.atDepth d n.val n.isLt)
    (bif inv then row.symm else row) y
  have concat (ns : List (Fin (Nat.clog 2 d))) (y : (g : Fin d) → AxisValue a w g) :
      (ns.flatMap (fun n => (Benes.executionOrder D).map (fun t => (n,t)))).foldl
        (fun z t => switchPerm a w hwidth inv t z) y = ns.foldl run y := by
    induction ns generalizing y with
    | nil => rfl
    | cons n ns ih =>
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_map, List.foldl_cons, ih]
      rw [switchDepth a w hwidth hdense hcop n inv D bound]
  rw [switchOrder, concat, ← Stage.bottomUp_perm (d := d) a E]
  have h := foldRows a E (Stage.bottomUp d) x inv
  rw [← depthOrder_rows] at h ⊢
  cases inv <;> simpa only [Bool.cond_true, Bool.cond_false, ← List.map_reverse, List.foldl_map,run] using h

end CRTTable

end NearSquareRoot
end Computability
end OAI
