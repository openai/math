import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffective
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepRow

/-! # Effective batched Fourier permutations on the natural record list -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

open IntegerMultiplication Code
open NearSquareRoot NearSquareRoot.SynchronizedBlocks NearSquareRoot.ShortFourier NearSquareRoot.PermutationSweep
open NearSquareRoot.SynchronizedLayers NearSquareRoot.SynchronizedLayers.ScheduleProgram NearSquareRoot.BoxFin

namespace BoxFin

/-- One fixed directory interpreter realizes the permutation on the natural record list
as the box, per-block tables and batch count vary. Its space charge uses only the
original forest and one batch workspace. -/
theorem boundedBatchPermutationFamily {P : Type} [Primcodable P] {X : P → Type} {V : (j : P) → X j → Type}
    (box : ∀ j, X j → List (ℕ × ℕ))
    (k L D batches : ∀ j, X j → ℕ) (hb : ∀ j x, BoxShape.Valid (k j x) (L j x) (box j x))
    [∀ j x i, NeZero (modulus (box j x) i)] (hd : ∀ j x, 4 ≤ (box j x).length)
    (p : ∀ j (x : X j) b, Equiv.Perm (BlockAddress (BoxAxis (box j x)) b))
    (tables : ∀ j (x : X j), Fin ((box j x).length/4) → Benes.RawTable)
    (rep : ∀ j x b, let e := blockWord (hb j x) b
      Benes.RawRepresents (e.symm.trans ((p j x b).symm.trans e)) (tables j x b))
    (which : ∀ j (x : X j), Fin ((box j x).length/4) → ℕ)
    (hD : ∀ j x b, physicalWidth (box := box j x) b ≤ D j x) (hw : ∀ j x b, which j x b < batches j x)
    (key : ∀ j, X j → ((Bool × ℕ) × ℕ) → Tree) (enc : ∀ j (x : X j), V j x → Tree)
    (v : ∀ j (x : X j), Fin (2^k j x) → V j x) (tick volume work : ∀ j, X j → ℕ)
    (directoryFits : ∀ j x, (Task.forest (key j x) (Benes.batchOrder (D j x) (batches j x))).count ≤ volume j x)
    (arrayFits : ∀ j x, (Task.forest (enc j x) (List.ofFn (v j x))).count ≤ volume j x) :
    let jobs j x := Benes.batchOrder (D j x) (batches j x)
    let width j x := physicalWidth (box := box j x)
    let address j x := Benes.PackedAddress Unit (width j x)
    let rank j x := packedRecord (hb j x) (hd j x)
    let array j x := tapeArray (rank j x) (enc j x)
    let input j x := v j x ∘ (rank j x).symm
    let stage j x (a : (Bool × ℕ) × ℕ) := Benes.batchStage (which j x) (width j x) (fun _ : Unit => tables j x) a.1 a.2
    EffectiveBoundedTask.Family
        (fun j (z : (x : X j) × {a // a ∈ jobs j x} × Equiv.Perm (address j x)) => tick j z.1)
        (fun j z => work j z.1)
        (fun j z => .fork (key j z.1 z.2.1) (array j z.1 (Benes.scatter z.2.2 (input j z.1))))
        (fun j z => array j z.1 (Benes.scatter (stage j z.1 z.2.1) (Benes.scatter z.2.2 (input j z.1)))) →
      EffectiveBoundedTask.Family (fun j x => 2*D j x*batches j x*tick j x + volume j x) (fun j x => volume j x + work j x)
        (fun j x => .fork (Task.forest (key j x) (jobs j x)) (Task.forest (enc j x) (List.ofFn (v j x))))
        (fun j x => Task.forest (enc j x) (List.ofFn (v j x ∘ permutationSource (hb j x) (hd j x) (p j x)))) := by
  intro jobs width address rank array input stage step
  apply step.sweep
  intro j c contract
  exact command_contract (RegisterTagFold.command c) from
    boundedBatchPermutation (box j) (k j) (L j) (D j) (batches j) (hb j) (hd j)
      (p j) (tables j) (rep j) (which j) (hD j) (hw j) (key j) (enc j) (v j)
      (tick j) (volume j) (work j) (directoryFits j) (arrayFits j) contract.task

end BoxFin

namespace ShortFourier.BatchWord.PermDirectory

/-- One fixed physical program carries out an indexed permutation row from the
generated schedule. The only transition supplied by the caller acts on a single
batch using the lookup tables read from the program's directory. -/
theorem bounded_indexedRowFamily {P : Type} [Primcodable P] {X : P → Type} {V : (j : P) → X j → Type}
    (k L D batches : ∀ j, X j → ℕ)
    (h : ∀ j x, BoxShape.Valid (k j x) (L j x) (CoprimeBox.box (k j x)))
    [∀ j x i, NeZero (modulus (CoprimeBox.box (k j x)) i)] (hd : ∀ j x, 4 ≤ (CoprimeBox.box (k j x)).length)
    (dir : ∀ j, X j → Bool) (s : ∀ j (x : X j), Fin (directedPlan (dir j x,tally (k j x))).length)
    (hp : ∀ j x, (directedPlan (dir j x,tally (k j x)))[(s j x).val].2.1 = kindCode .permutation)
    (which : ∀ j (x : X j), Fin ((CoprimeBox.box (k j x)).length/4) → ℕ)
    (hD : ∀ j x b, physicalWidth (box := CoprimeBox.box (k j x)) b ≤ D j x)
    (hw : ∀ j x b, which j x b < batches j x)
    (key : ∀ j, X j → ((Bool × ℕ) × ℕ) → Tree) (enc : ∀ j (x : X j), V j x → Tree)
    (v : ∀ j (x : X j), Fin (2^k j x) → V j x) (tick volume work : ∀ j, X j → ℕ)
    (directoryFits : ∀ j x, (Task.forest (key j x) (Benes.batchOrder (D j x) (batches j x))).count ≤ volume j x)
    (arrayFits : ∀ j x, (Task.forest (enc j x) (List.ofFn (v j x))).count ≤ volume j x) :
    let r j x := (directedPlan (dir j x,tally (k j x)))[(s j x).val]
    let jobs j x := Benes.batchOrder (D j x) (batches j x)
    let width j x := physicalWidth (box := CoprimeBox.box (k j x))
    let address j x := Benes.PackedAddress Unit (width j x)
    let rank j x := packedRecord (h j x) (hd j x)
    let array j x := tapeArray (rank j x) (enc j x)
    let input j x := v j x ∘ (rank j x).symm
    let stage j x (a : (Bool × ℕ) × ℕ) := Benes.batchStage (which j x) (width j x)
      (fun _ : Unit => switchTable (dir j x) (s j x).val) a.1 a.2
    EffectiveBoundedTask.Family
        (fun j (z : (x : X j) × {a // a ∈ jobs j x} × Equiv.Perm (address j x)) => tick j z.1)
        (fun j z => work j z.1)
        (fun j z => .fork (key j z.1 z.2.1) (array j z.1 (Benes.scatter z.2.2 (input j z.1))))
        (fun j z => array j z.1 (Benes.scatter (stage j z.1 z.2.1) (Benes.scatter z.2.2 (input j z.1)))) →
      EffectiveBoundedTask.Family (fun j x => 2*D j x*batches j x*tick j x + volume j x) (fun j x => volume j x + work j x)
        (fun j x => .fork (Task.forest (key j x) (jobs j x)) (Task.forest (enc j x) (List.ofFn (v j x))))
        (fun j x => Task.forest (enc j x) (List.ofFn (v j x ∘ permutationSource (h j x) (hd j x) (localSource (h j x) (r j x))))) := by
  intro r jobs width address rank array input stage step
  apply step.sweep
  intro j c contract
  exact command_contract (RegisterTagFold.command c) from
    bounded_indexedRow (k j) (L j) (D j) (batches j) (h j) (hd j) (dir j) (s j) (hp j)
      (which j) (hD j) (hw j) (key j) (enc j) (v j) (tick j) (volume j) (work j)
      (directoryFits j) (arrayFits j) contract.task

end ShortFourier.BatchWord.PermDirectory

end

end NearSquareRoot
end Computability
end OAI
