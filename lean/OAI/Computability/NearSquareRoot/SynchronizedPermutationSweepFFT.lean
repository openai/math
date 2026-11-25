import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweep
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchSemantics
import OAI.Computability.NearSquareRoot.SynchronizedPackedPermutation

/-! # Batched Fourier permutations on the tape's natural list of records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PermutationSweep
open IntegerMultiplication IntegerMultiplication.Code

/-- Emit one record at each natural tape index, retaining increasing address order. -/
def tapeArray {A V : Type*} {n : ℕ} (rank : Fin n ≃ A) (encode : V → Tree) (v : A → V) : Tree :=
  Task.forest encode (List.ofFn (v ∘ rank))

/-- Intermediate scatter permutations preserve the complete forest size for arbitrary
record sizes. The workspace estimate can therefore charge the original array once. -/
theorem tapeArray_count_scatter {A V : Type*} {n : ℕ} (rank : Fin n ≃ A) (enc : V → Tree)
    (p : Equiv.Perm A) (v : A → V) :
    (tapeArray rank enc (Benes.scatter p v)).count = (tapeArray rank enc v).count := by
  let e := rank.trans (p.symm.trans rank.symm)
  have h := e.sum_comp (fun j => (enc (v (rank j))).count)
  simp only [e, Equiv.trans_apply,Equiv.apply_symm_apply] at h
  simp only [tapeArray, Task.forest_count, List.length_ofFn, costSum, List.map_ofFn, List.sum_ofFn]
  exact congrArg (fun s => n+s+1) h

end PermutationSweep

namespace BoxFin
open SynchronizedBlocks ShortFourier PermutationSweep IntegerMultiplication IntegerMultiplication.Code
noncomputable section

variable {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box)
  [∀ i, NeZero (modulus box i)] (hd : 4 ≤ box.length)

/-- Read each batched output at its literal tape rank, including blocks narrower than
the common Beneš depth. The scatter network uses inverse per-block routing tables. -/
theorem batchPermutation_reads {V : Type} (p : ∀ j, Equiv.Perm (BlockAddress (BoxAxis box) j))
    (tables : Fin (box.length/4) → Benes.RawTable)
    (rep : ∀ j, let e := blockWord hb j
      Benes.RawRepresents (e.symm.trans ((p j).symm.trans e)) (tables j))
    (which : Fin (box.length/4) → ℕ) (D batches : ℕ)
    (hD : ∀ j, physicalWidth (box := box) j ≤ D) (hw : ∀ j, which j < batches)
    (v : Fin (2^k) → V) (i : Fin (2^k)) :
    let rank := packedRecord hb hd
    let step := Benes.batchStage which (physicalWidth (box := box)) (fun _ : Unit => tables)
    ((Benes.batchOrder D batches).foldl (fun arr s => Benes.scatter (step s.1 s.2) arr) (v ∘ rank.symm))
        (rank i) = v (permutationSource hb hd p i) := by
  let perm (_ : Unit) j := (blockWord hb j).symm.trans ((p j).symm.trans (blockWord hb j))
  let rank := packedRecord hb hd
  have batchesRun := Benes.batchData_run which _ (fun _ : Unit => tables) perm (fun _ j => rep j)
    D batches hD hw (v ∘ rank.symm)
  have wholeRun := Benes.packedData_run _ (fun _ : Unit => tables) perm (fun _ j => rep j)
    D hD (v ∘ rank.symm)
  exact (congrFun (batchesRun.trans wholeRun.symm) (rank i)).trans
    (packedPermutation_reads hb hd p tables rep D hD v i)

/-- One fixed directory interpreter realizes the permutation on the natural record list
as the box, per-block tables and batch count vary. Its space charge uses only the
original forest and one batch workspace. -/
theorem boundedBatchPermutation {X : Type*} {V : X → Type} (box : X → List (ℕ × ℕ))
    (k L D batches : X → ℕ) (hb : ∀ x, BoxShape.Valid (k x) (L x) (box x))
    [∀ x i, NeZero (modulus (box x) i)] (hd : ∀ x, 4 ≤ (box x).length)
    (p : (x : X) → ∀ j, Equiv.Perm (BlockAddress (BoxAxis (box x)) j))
    (tables : (x : X) → Fin ((box x).length/4) → Benes.RawTable)
    (rep : ∀ x j, let e := blockWord (hb x) j
      Benes.RawRepresents (e.symm.trans ((p x j).symm.trans e)) (tables x j))
    (which : (x : X) → Fin ((box x).length/4) → ℕ)
    (hD : ∀ x j, physicalWidth (box := box x) j ≤ D x) (hw : ∀ x j, which x j < batches x)
    (key : X → ((Bool × ℕ) × ℕ) → Tree) (enc : (x : X) → V x → Tree)
    (v : (x : X) → Fin (2^k x) → V x) (tick volume work : X → ℕ)
    (directoryFits : ∀ x, (Task.forest (key x) (Benes.batchOrder (D x) (batches x))).count ≤ volume x)
    (arrayFits : ∀ x, (Task.forest (enc x) (List.ofFn (v x))).count ≤ volume x) :
    let jobs x := Benes.batchOrder (D x) (batches x)
    let width x := physicalWidth (box := box x)
    let address x := Benes.PackedAddress Unit (width x)
    let rank x := packedRecord (hb x) (hd x)
    let array x := tapeArray (rank x) (enc x)
    let input x := v x ∘ (rank x).symm
    let stage x (a : (Bool × ℕ) × ℕ) := Benes.batchStage (which x) (width x) (fun _ : Unit => tables x) a.1 a.2
    Space.BoundedTask
        (fun z : (x : X) × {a // a ∈ jobs x} × Equiv.Perm (address x) => tick z.1)
        (fun z => work z.1)
        (fun z => .fork (key z.1 z.2.1) (array z.1 (Benes.scatter z.2.2 (input z.1))))
        (fun z => array z.1 (Benes.scatter (stage z.1 z.2.1) (Benes.scatter z.2.2 (input z.1)))) →
      Space.BoundedTask (fun x => 2*D x*batches x*tick x + volume x) (fun x => volume x + work x)
        (fun x => .fork (Task.forest (key x) (jobs x)) (Task.forest (enc x) (List.ofFn (v x))))
        (fun x => Task.forest (enc x) (List.ofFn (v x ∘ permutationSource (hb x) (hd x) (p x)))) := by
  intro jobs width address rank array input stage step
  have start (x : X) : array x (input x) = Task.forest (enc x) (List.ofFn (v x)) :=
    congrArg (Task.forest (enc x)) (congrArg List.ofFn
      (funext fun j => congrArg (v x) ((rank x).symm_apply_apply j)))
  have run := PermutationSweep.run jobs stage key array input tick volume work step directoryFits
    (fun x perm => (tapeArray_count_scatter (rank x) (enc x) perm (input x)).le.trans
      ((congrArg Tree.count (start x)).le.trans (arrayFits x)))
  exact run.conform (fun x => by simp only [jobs, Benes.batchOrder_length]) (fun _ => rfl)
    (fun x => congrArg (Tree.fork _) (start x))
    (fun x => congrArg (Task.forest (enc x)) (congrArg List.ofFn (funext
      (batchPermutation_reads (hb x) (hd x) (p x) (tables x) (rep x) (which x)
        (D x) (batches x) (hD x) (hw x) (v x)))))

end
end BoxFin

end NearSquareRoot
end Computability
end OAI
