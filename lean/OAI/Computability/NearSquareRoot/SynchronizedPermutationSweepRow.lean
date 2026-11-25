import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepDirectory

/-! # Directory sweep for a generated permutation row of the Fourier schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open Matrix IntegerMultiplication IntegerMultiplication.Code SynchronizedBlocks SynchronizedPadding SynchronizedLayers
open SynchronizedLayers.ScheduleProgram BoxFin PermutationSweep
open scoped Matrix

noncomputable section

/-- One fixed physical program carries out an indexed permutation row from the
generated schedule. The only transition supplied by the caller acts on a single
batch using the lookup tables read from the program's directory. -/
theorem bounded_indexedRow {X : Type*} {V : X → Type} (k L D batches : X → ℕ)
    (h : ∀ x, BoxShape.Valid (k x) (L x) (CoprimeBox.box (k x)))
    [∀ x i, NeZero (modulus (CoprimeBox.box (k x)) i)] (hd : ∀ x, 4 ≤ (CoprimeBox.box (k x)).length)
    (dir : X → Bool) (s : (x : X) → Fin (directedPlan (dir x,tally (k x))).length)
    (hp : ∀ x, (directedPlan (dir x,tally (k x)))[(s x).val].2.1 = kindCode .permutation)
    (which : (x : X) → Fin ((CoprimeBox.box (k x)).length/4) → ℕ)
    (hD : ∀ x j, physicalWidth (box := CoprimeBox.box (k x)) j ≤ D x)
    (hw : ∀ x j, which x j < batches x)
    (key : X → ((Bool × ℕ) × ℕ) → Tree) (enc : (x : X) → V x → Tree)
    (v : (x : X) → Fin (2^k x) → V x) (tick volume work : X → ℕ)
    (directoryFits : ∀ x, (Task.forest (key x) (Benes.batchOrder (D x) (batches x))).count ≤ volume x)
    (arrayFits : ∀ x, (Task.forest (enc x) (List.ofFn (v x))).count ≤ volume x) :
    let r x := (directedPlan (dir x,tally (k x)))[(s x).val]
    let jobs x := Benes.batchOrder (D x) (batches x)
    let width x := physicalWidth (box := CoprimeBox.box (k x))
    let address x := Benes.PackedAddress Unit (width x)
    let rank x := packedRecord (h x) (hd x)
    let array x := tapeArray (rank x) (enc x)
    let input x := v x ∘ (rank x).symm
    let stage x (a : (Bool × ℕ) × ℕ) := Benes.batchStage (which x) (width x)
      (fun _ : Unit => switchTable (dir x) (s x).val) a.1 a.2
    Space.BoundedTask
        (fun z : (x : X) × {a // a ∈ jobs x} × Equiv.Perm (address x) => tick z.1)
        (fun z => work z.1)
        (fun z => .fork (key z.1 z.2.1) (array z.1 (Benes.scatter z.2.2 (input z.1))))
        (fun z => array z.1 (Benes.scatter (stage z.1 z.2.1) (Benes.scatter z.2.2 (input z.1)))) →
      Space.BoundedTask (fun x => 2*D x*batches x*tick x + volume x) (fun x => volume x + work x)
        (fun x => .fork (Task.forest (key x) (jobs x)) (Task.forest (enc x) (List.ofFn (v x))))
        (fun x => Task.forest (enc x) (List.ofFn (v x ∘ permutationSource (h x) (hd x) (localSource (h x) (r x))))) :=
  boundedBatchPermutation (fun x => CoprimeBox.box (k x)) k L D batches h hd
    (fun x => localSource (h x) (directedPlan (dir x,tally (k x)))[(s x).val])
    (fun x => switchTable (dir x) (s x).val)
    (fun x b => (switchTable_spec (h x) (dir x) (s x) (hp x) b).2)
    which hD hw key enc v tick volume work directoryFits arrayFits

/-- On exact complex values the emitted destination array agrees entry by entry
with the matrix of this same directed plan opcode. -/
theorem flat_permutationRow_apply {k L : ℕ} (h : BoxShape.Valid k L (CoprimeBox.box k))
    [∀ i, NeZero (modulus (CoprimeBox.box k) i)] (hd : 4 ≤ (CoprimeBox.box k).length)
    (dir : Bool) (s : Fin (directedPlan (dir,tally k)).length)
    (hp : (directedPlan (dir,tally k))[s.val].2.1 = kindCode .permutation) (v : Fin (2^k) → ℂ) :
    let r := (directedPlan (dir,tally k))[s.val]
    (boxRow (physicalLayout h) hd r).submatrix (recordIndex h).symm (recordIndex h).symm *ᵥ v =
      v ∘ permutationSource h hd (localSource h r) := by
  dsimp only
  rw [flat_permutationRow h hd dir s hp]
  exact permutationSource_mulVec ..

end
end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
