import OAI.Computability.VPVNP.RAMTapeRecordBuffer
import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-!
# Staging the site's prescribed initialization record

The input preparer supplies the site address and packed header word in fields
one and two. The fixed staging routine sets the initialization tag, copies the
site address to the start-cost field, and copies the zero word to the ordinal.
It restores all inputs and its two scratch stacks before record emission.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RecordBuffer

open BurstRAM TapeWord

/-- The initialization record fields supplied by the staging routine, namely its tag, start
cost and ordinal. -/
inductive InitField | tag | start | ordinal

private def source : InitField → Port
  | .tag | .start => .field 1
  | .ordinal => .zeros

private def dest : InitField → Port
  | .tag => .field 0
  | .start => .field 3
  | .ordinal => .field 4

private def copyPorts (f : InitField) : ScanPort → Port
  | .left => source f
  | .right => .temp
  | .tmp => .output
  | .out => dest f

private theorem copy_inj (f : InitField) : Function.Injective (copyPorts f) := by
  intro i j h
  cases f <;> cases i <;> cases j <;> simp_all [copyPorts, source, dest]

private def normal {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

private def fill {A : Type} [Fintype A] (f : InitField) (bit : A → Bool → Bool × A)
    (start : A) : FiniteRoutine Port :=
  .ofStackCode (Operand.code bit) (copyPorts f) (.clear start) normal

private theorem fill_run {A : Type} [Fintype A] (f : InitField) (bit : A → Bool → Bool × A)
    (start finish : A) (s : Stacks Port) (v : List Bool) {t : ℕ}
    (h : StackRuns (Operand.code bit) t (.clear start) (scanStacks (s (source f)) [] [] (s (dest f)))
      (.done finish) (scanStacks (s (source f)) [] [] v)) (ht : s .temp = []) (ho : s .output = []) :
    (fill f bit start).Runs t s (Function.update s (dest f) v) := by
  apply FiniteRoutine.runs_ofStackCode_framed (copy_inj f) (normal := normal) rfl (exit := .done finish) rfl
    (fun q hn => by cases q <;> first | rfl | contradiction) h
  · intro i; cases i <;> first | rfl | exact ht | exact ho
  · intro i
    cases f <;> cases i <;> simp_all [copyPorts, source, dest, scanStacks]
  · intro j hj
    exact Function.update_of_ne (Ne.symm (hj .out)) ..

/-- Stage the initialization tag, copy the site address into the start-cost field and fill the
ordinal field with zero. -/
def initFields : FiniteRoutine Port :=
  ((fill .tag (Operand.literalBit 1) (Fin.last 1)).followedBy
    (fill .start Operand.copyBit ())).followedBy (fill .ordinal Operand.copyBit ())

/-- Record-buffer contents after setting the initialization tag, the start cost equal to the
address, and the probe ordinal to zero. -/
def initialized {w : ℕ} (s : Stacks Port) (address : Word w) : Stacks Port :=
  Function.update (Function.update (Function.update s (.field 0) (wordBits (Fin.ofNat (2^w) 1)))
    (.field 3) (wordBits address)) (.field 4) (wordBits (0 : Word w))

theorem initFields_run {w : ℕ} (s : Stacks Port) (a : Word w)
    (ha : s (.field 1) = wordBits a) (hz : s .zeros = wordBits (0 : Word w))
    (ht : s .temp = []) (ho : s .output = []) :
    initFields.Runs ((s (.field 0)).length+(s (.field 3)).length+(s (.field 4)).length+21*w+9)
      s (initialized s a) := by
  let tag := wordBits (Fin.ofNat (2^w) 1 : Word w)
  let s₁ := Function.update s (.field 0) tag
  let s₂ := Function.update s₁ (.field 3) (wordBits a)
  obtain ⟨q, run⟩ := Operand.literal_run 1 a (s (.field 0))
  have h₁ : (fill .tag (Operand.literalBit 1) (Fin.last 1)).Runs ((s (.field 0)).length+7*w+3) s s₁ := by
    apply fill_run .tag _ _ q s tag _ ht ho
    simpa only [source, dest, ha] using run
  have h₂ : (fill .start Operand.copyBit ()).Runs ((s (.field 3)).length+7*w+3) s₁ s₂ := by
    apply fill_run .start _ _ () s₁ (wordBits a) _ (by simpa [s₁] using ht) (by simpa [s₁] using ho)
    simpa [source, dest, s₁, ha] using Operand.copy_run (wordBits a) (s (.field 3))
  have h₃ : (fill .ordinal Operand.copyBit ()).Runs ((s (.field 4)).length+7*w+3) s₂ (initialized s a) := by
    apply fill_run .ordinal _ _ () s₂ (wordBits (0 : Word w)) _ (by simpa [s₂, s₁] using ht) (by simpa [s₂, s₁] using ho)
    simpa [source, dest, s₂, s₁, hz] using Operand.copy_run (wordBits (0 : Word w)) (s (.field 4))
  convert (h₁.followedBy h₂).followedBy h₃ using 1
  · rfl
  omega

end RAMTape.RecordBuffer

end VPVNP
end Computability
end OAI
