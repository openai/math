import OAI.Computability.VPVNP.RAMTapePhysicalInput
import OAI.Computability.VPVNP.RAMTapeSiteSizes
import OAI.Computability.VPVNP.RAMTapeMapWord

/-! # Starting the local validator on its physical tape

The fixed input reader and width routines share the public address and bucket
registers. At their return the fields are in their original bit order. The record
emitter receives a writable slot counter and a zero-word template, while a
second slot count remains available for sorting and boundary checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteSetup

open BurstRAM ProcessorInput RAMLayout StackCompiler

/-- Working registers for computing the validator dimensions, remaining slot tally, zero
template, and temporary storage. -/
inductive Work
  | shape (p : InputWidth.Port)
  | remaining | zeros | tmp
  deriving DecidableEq

noncomputable instance : Fintype Work := derive_fintype% Work

/-- Combined register bank for the physical input reader and validator setup. -/
abbrev Port := InputReader.Registers ⊕ Work

/-- Port for the input reader's raw bit stream. -/
def rawPort : Port := .inl (.inl .input)
/-- Port for the unary RAM word width computed from the input dimensions. -/
def wordPort : Port := .inr (.shape .word)
/-- Port for the retained unary count of record slots. -/
def slotsPort : Port := .inr (.shape .blocks)
/-- Writable slot counter used by the record emitter. -/
def remainingPort : Port := .inr .remaining
/-- Port for the fixed-width all-zero word template. -/
def zerosPort : Port := .inr .zeros
private def tmpPort : Port := .inr .tmp

private def shapePort : InputWidth.Port → Port
  | .address => .inl InputReader.addressWidthPort
  | .bucket => .inl InputReader.bucketPort
  | p => .inr (.shape p)

private theorem shape_injective : Function.Injective shapePort := by
  intro a b h
  cases a <;> cases b <;> simp_all [shapePort, InputReader.addressWidthPort, InputReader.bucketPort]

private def sizes : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine InputWidth.siteSizeProgram.code).onPorts shapePort

private def shaped (s : Stacks InputReader.Registers) (d H : ℕ) : Stacks Port
  | .inl i => s i
  | .inr (.shape .word) => List.replicate ((d+10)^4) true
  | .inr (.shape .blocks) => List.replicate (4*H) true
  | .inr _ => []

/-- Extend the shaped bank with four times the bucket capacity in remaining slots and a zero
word of the computed width. -/
def prepared (s : Stacks InputReader.Registers) (d H : ℕ) : Stacks Port :=
  Function.update (Function.update (shaped s d H) remainingPort (List.replicate (4*H) true))
    zerosPort (List.replicate ((d+10)^4) false)

private theorem sizes_run (s : Stacks InputReader.Registers) (d H : ℕ)
    (hd : s InputReader.addressWidthPort = List.replicate d true)
    (hH : s InputReader.bucketPort = List.replicate H true) :
    sizes.Runs (InputWidth.siteSizeProgram.work (InputWidth.initial d H))
      (Sum.elim s (fun _ => [])) (shaped s d H) := by
  apply FiniteRoutine.runs_onPorts_framed _ shape_injective (InputWidth.siteSizes_runs d H)
  · intro p; cases p <;> first | rfl | exact hd | exact hH
  · intro p; cases p <;> first | rfl | exact hd | exact hH
  · rintro (i | w) hm
    · rfl
    · cases w with
      | shape p =>
        cases p <;> first | rfl | exact (hm .word rfl).elim | exact (hm .blocks rfl).elim
      | remaining | zeros | tmp => rfl

private def templates : FiniteRoutine Port :=
  (WordCopy.mapWord tmpPort remainingPort id slotsPort).followedBy
    (WordCopy.mapWord tmpPort zerosPort (fun _ => false) wordPort)

private theorem templates_run (s : Stacks InputReader.Registers) (d H : ℕ) :
    templates.Runs (5*(4*H)+2 + (5*(d+10)^4+2)) (shaped s d H) (prepared s d H) := by
  let u := shaped s d H
  let v := Function.update u remainingPort (List.replicate (4*H) true)
  have h₁ := WordCopy.mapWord_run tmpPort remainingPort id (src := slotsPort)
    (by decide) (by decide) (by decide) u rfl
  change (WordCopy.mapWord tmpPort remainingPort id slotsPort).Runs
    (5*(List.replicate (4*H) true).length+2) u
    (Function.update u remainingPort (((List.replicate (4*H) true).map id).reverse ++ [])) at h₁
  simp only [List.length_replicate, List.map_id_fun, id_eq, List.reverse_replicate, List.append_nil] at h₁
  have h₂ := WordCopy.zero_template tmpPort zerosPort (src := wordPort)
    (by decide) (by decide) (by decide) v rfl rfl
  change (WordCopy.mapWord tmpPort zerosPort (fun _ => false) wordPort).Runs
    (5*(List.replicate ((d+10)^4) true).length+2) v
    (Function.update v zerosPort (List.replicate (List.replicate ((d+10)^4) true).length false)) at h₂
  simp only [List.length_replicate] at h₂
  exact h₁.followedBy h₂

/-- Run the physical input reader, compute the dimensions, and prepare the slot counter and
zero-word template. -/
def routine (B p q : ℕ) (hq : 0 < q) : FiniteRoutine Port :=
  (((InputReader.physicalReader B p q hq).onPorts Sum.inl).followedBy sizes).followedBy templates

/-- The initialized local bank and polynomial clock depend only on the data read from
the original physical input, for every incident bit pattern. -/
theorem runs (B p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) (prog : UniversalMachine.Program)
    (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let H := 2 ^ roundedUp p q n
    let w := (d+10)^4
    ∀ (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool),
      Fits prog n d H w →
      ∃ steps ≤ (InputParameters.clockCoefficient B p q+43+1026*(B+13)^7)*(n+1)^7,
        (routine B p q hq).Runs steps (labeledInput rawPort (ProcessorInput.tape prog n v hdr inc))
          (prepared (InputReader.physicalResult n d H (UniversalMachine.programPrefix prog)
            (List.ofFn (RAMSerialization.wordBits d v)) (List.ofFn hdr) (List.ofFn inc)) d H) := by
  intro d H w v hdr inc hf
  let raw := ProcessorInput.tape prog n v hdr inc
  let out := InputReader.physicalResult n d H (UniversalMachine.programPrefix prog)
    (List.ofFn (RAMSerialization.wordBits d v)) (List.ofFn hdr) (List.ofFn inc)
  obtain ⟨t, ht, hr⟩ := InputReader.physicalReader_runs B p q hq hpq prog n hn v hdr inc hf
  have h₁ : ((InputReader.physicalReader B p q hq).onPorts Sum.inl).Runs t
      (labeledInput rawPort raw) (Sum.elim out (fun _ => [])) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hr
    · intro i; simp [labeledInput, rawPort, raw]
    · intro i; rfl
    · rintro (i | j) hi
      · exact (hi i rfl).elim
      · rfl
  have h₂ := sizes_run out d H rfl rfl
  have h₃ := templates_run out d H
  refine ⟨_, ?_, (h₁.followedBy h₂).followedBy h₃⟩
  let M := d+H+11
  have hm : 0 < M := Nat.add_pos_right _ (by decide)
  have hM : M ≤ M^7 := by simpa using Nat.pow_le_pow_right hm (by decide : 1 ≤ 7)
  have hH : H ≤ M := by dsimp [M]; omega
  have hsmall : d+10 ≤ M := Nat.add_le_add (Nat.le_add_right d H) (by decide : 10 ≤ 11)
  have hw : (d+10)^4 ≤ M^7 :=
    (Nat.pow_le_pow_left hsmall 4).trans
      (Nat.pow_le_pow_right hm (by decide))
  have hprep := InputWidth.siteSizes_work_le d H
  change _ ≤ 1000*M^7 at hprep
  have htotal : InputWidth.siteSizeProgram.work (InputWidth.initial d H) +
      (5*(4*H)+2+(5*(d+10)^4+2)) ≤ 1026*M^7 := by omega
  have hd : d ≤ B*n := Nat.mul_le_mul_left _ (Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le)
  have hbucket : H ≤ 2*n := InputBucketFromSize.bucket_le hq hpq hn
  have hparam : M ≤ (B+13)*(n+1) := by
    dsimp [M]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hscaled := (Nat.mul_le_mul_left 1026 (Nat.pow_le_pow_left hparam 7))
  rw [Nat.mul_pow, ← Nat.mul_assoc] at hscaled
  rw [Nat.add_mul]
  omega

end RAMTape.SiteSetup

end VPVNP
end Computability
end OAI
