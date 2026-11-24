import OAI.Computability.VPVNP.RAMTapeInputParametersWidthCost
import OAI.Computability.VPVNP.RAMTapeInput
import OAI.Computability.VPVNP.RAMTapeInputParametersFromSize
import OAI.Computability.VPVNP.RAMTapeInputPorts
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeCeilLog
import OAI.Computability.VPVNP.TallyStacks

/-!
# Preparing the physical reader's field lengths

Copy the unary input length before computing the address width and the live
bucket on separate passes. The incident width calculation reads both results,
after which the bucket tally can be erased. The raw input and the reader's data
fields are carried through every pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputParameters

/-- Work ports for the saved length, unary bucket, and the separate bucket and incident-width
computations. -/
inductive Work (K L : Type) where
  | lengthCopy | bucket | bucketWork (k : K) | widthWork (l : L)
  deriving DecidableEq, Fintype

private abbrev Registers (K L : Type) := InputPort ⊕ Work K L
private abbrev ones (k : ℕ) := List.replicate k true

variable {K L : Type} [DecidableEq K] [DecidableEq L]

private def frame (base : Stacks InputPort) (size copy address bucket incident : ℕ) :
    Stacks (Registers K L)
  | .inl .size => ones size
  | .inl .addressCount => ones address
  | .inl .incidentCount => ones incident
  | .inl .tmp => []
  | .inl i => base i
  | .inr .lengthCopy => ones copy
  | .inr .bucket => ones bucket
  | .inr (.bucketWork _) | .inr (.widthWork _) => []

private def copyPort : CeilLog.Port → Registers K L
  | .src => .inl .size
  | .tmp => .inl .tmp
  | .out => .inr .lengthCopy

private def addressPort : CeilLog.Port → Registers K L
  | .src => .inr .lengthCopy
  | .tmp => .inl .tmp
  | .out => .inl .addressCount

private def copyLength : FiniteRoutine (Registers K L) :=
  (FiniteRoutine.ofRoutine (Tally.copyAdd CeilLog.Port.src .out .tmp)).onPorts copyPort

private def addressWidth (B : ℕ) : FiniteRoutine (Registers K L) :=
  FiniteRoutine.ofStackCode (CeilLog.code B) addressPort .scan (· == .done)

private theorem copy_run (base : Stacks InputPort) (n : ℕ) :
    (copyLength (K := K) (L := L)).Runs (5*n+2) (frame base n 0 0 0 0) (frame base n n 0 0 0) := by
  let s : Tally.State CeilLog.Port := fun i => if i = .src then n else 0
  have run := Tally.copyAdd_runs CeilLog.Port.src .out .tmp (by decide) (by decide) (by decide) s rfl
  apply FiniteRoutine.runs_onPorts_framed _ (by intro a b h; cases a <;> cases b <;> simp_all [copyPort]) run
  · intro i; cases i <;> rfl
  · intro i; cases i <;> simp [frame, copyPort, Tally.encode, s, Function.update]
  · rintro (i | u) h
    · cases i <;> rfl
    · cases u <;> first | rfl | exact (h .out rfl).elim

private theorem address_run (B n : ℕ) (base : Stacks InputPort) :
    (addressWidth (K := K) (L := L) B).Runs (CeilLog.cost B n)
      (frame base n n 0 0 0) (frame base n 0 (B * Nat.clog 2 n) 0 0) := by
  apply FiniteRoutine.runs_ofStackCode_framed
    (by intro a b h; cases a <;> cases b <;> simp_all [addressPort])
    rfl rfl (fun z hz => by simp only [beq_iff_eq] at hz; subst z; rfl) (CeilLog.runs B n [])
  · intro i; cases i <;> rfl
  · intro i; cases i <;> simp [frame, CeilLog.store, addressPort]
  · rintro (i | u) h
    · cases i <;> first | rfl | exact (h .out rfl).elim
    · cases u <;> first | rfl | exact (h .src rfl).elim

private def clearCode : StackCode Unit Bool
  | false => .pop () (fun b => b.isNone)
  | true => .halt true

private def clearBucket : FiniteRoutine (Registers K L) :=
  FiniteRoutine.ofStackCode clearCode (fun _ => .inr .bucket) false id

private theorem clear_run (base : Stacks InputPort) (d H width : ℕ) :
    (clearBucket (K := K) (L := L)).Runs (H+1) (frame base 0 0 d H width) (frame base 0 0 d 0 width) := by
  have hh (h : ℕ) : StackRuns clearCode (h+1) false (fun _ => ones h) true (fun _ => []) := by
    induction h with
    | zero => exact .cons (.pop rfl) (.nil ..)
    | succ h ih =>
      refine .cons (.pop rfl) ?_
      convert ih using 1
      · simp [ones, List.replicate_succ]
      · funext j; cases j; simp [ones, List.replicate_succ]
  apply FiniteRoutine.runs_ofStackCode_framed (fun _ _ _ => Subsingleton.elim ..) rfl rfl
    (by intro z hz; cases z <;> simp_all [clearCode]) (hh H)
  · intro i; cases i; rfl
  · intro i; cases i; rfl
  · rintro (i | u) h
    · cases i <;> rfl
    · cases u <;> first | rfl | exact (h () rfl).elim

private def bucketPort : InputBucketFromSize.Port → Registers InputBucketFromSize.Port L
  | .size => .inl .size
  | .bucket => .inr .bucket
  | r => .inr (.bucketWork r)

private def computeBucket (p q : ℕ) (hq : 0 < q) :
    FiniteRoutine (Registers InputBucketFromSize.Port L) :=
  (InputBucketFromSize.routine p q hq).onPorts bucketPort

private theorem computeBucket_run (base : Stacks InputPort) (d p q n : ℕ)
    (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) :
    ∃ t ≤ InputBucketFromSize.clockCoefficient p q * (n+1)^2,
      (computeBucket (L := L) p q hq).Runs t (frame base n 0 d 0 0)
        (frame base 0 0 d (2^BurstRAM.roundedUp p q n) 0) := by
  obtain ⟨t, ht, run⟩ := InputBucketFromSize.runs p q n hq hpq hn
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ (by intro a b h; cases a <;> cases b <;> simp_all [bucketPort]) run
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · rintro (i | u) h
    · cases i <;> first | rfl | exact (h .size rfl).elim
    · cases u <;> first | rfl | exact (h .bucket rfl).elim

/-- Scratch bank for preparing the physical input fields with the bucket and width subroutines. -/
abbrev Scratch := Work InputBucketFromSize.Port InputWidth.Port

private def widthPort : InputWidth.Port → InputPort ⊕ Scratch
  | .address => .inl .addressCount
  | .bucket => .inr .bucket
  | .incident => .inl .incidentCount
  | r => .inr (.widthWork r)

private def incidentWidth : FiniteRoutine (InputPort ⊕ Scratch) :=
  (FiniteRoutine.ofRoutine InputWidth.program.code).onPorts widthPort

private theorem incident_run (base : Stacks InputPort) (d H : ℕ) :
    incidentWidth.Runs (InputWidth.program.work (InputWidth.initial d H))
      (frame base 0 0 d H 0) (frame base 0 0 d H (RAMLayout.width d H ((d+10)^4))) := by
  apply FiniteRoutine.runs_onPorts_framed _ (by intro a b h; cases a <;> cases b <;> simp_all [widthPort])
    (InputWidth.runs d H)
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · rintro (i | u) h
    · cases i <;> first | rfl | exact (h .incident rfl).elim
    · cases u <;> rfl

/-- The only length-dependent data are on stacks. The finite control depends
on the fixed address multiplier and rational exponent. -/
def routineKeep (B p q : ℕ) (hq : 0 < q) : FiniteRoutine (InputPort ⊕ Scratch) :=
  ((copyLength.followedBy (addressWidth B)).followedBy (computeBucket p q hq)).followedBy incidentWidth

/-- A parser-only run erases the bucket tally after preparing the two lengths. -/
def routine (B p q : ℕ) (hq : 0 < q) : FiniteRoutine (InputPort ⊕ Scratch) :=
  (routineKeep B p q hq).followedBy clearBucket

/-- The parameter stage preserves all reader stacks outside its working registers. -/
def readerFrame (base : Stacks InputPort) (size copy d H width : ℕ) : Stacks (InputPort ⊕ Scratch) :=
  frame base size copy d H width

/-- Parser stacks with their literal input and the unary counters. -/
def bank (raw : List Bool) (size copy d H width : ℕ) : Stacks (InputPort ⊕ Scratch) :=
  readerFrame (InputReader.prepared raw 0 0 []) size copy d H width

theorem bank_inl (raw : List Bool) (size copy d H width : ℕ) (i : InputPort) :
    bank raw size copy d H width (.inl i) =
      InputReader.prepared raw d width (List.replicate size true) i := by cases i <;> rfl

@[simp] theorem bank_bucket (raw : List Bool) (size copy d H width : ℕ) :
    bank raw size copy d H width (.inr .bucket) = List.replicate H true := rfl

theorem bank_inr_other (raw : List Bool) (size d H width : ℕ) (i : Scratch) (hi : i ≠ .bucket) :
    bank raw size 0 d H width (.inr i) = [] := by cases i <;> first | rfl | contradiction

theorem bank_inr_empty (raw : List Bool) (size d width : ℕ) (i : Scratch) :
    bank raw size 0 d 0 width (.inr i) = [] := by cases i <;> rfl

/-- Sum of instruction bounds for the five passes. -/
private def prepBudget (B p q n : ℕ) : ℕ :=
  let d := B * Nat.clog 2 n
  let H := 2^BurstRAM.roundedUp p q n
  5*n+2 + CeilLog.cost B n + InputBucketFromSize.clockCoefficient p q * (n+1)^2 +
    InputWidth.program.work (InputWidth.initial d H)

/-- Step budget for preparing field widths, including erasure of the unary bucket copy. -/
def budget (B p q n : ℕ) := prepBudget B p q n + (2^BurstRAM.roundedUp p q n + 1)

set_option maxHeartbeats 1000000 in
private theorem keep_framed (B p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n)
    (base : Stacks InputPort) :
    let d := B * Nat.clog 2 n
    let H := 2^BurstRAM.roundedUp p q n
    ∃ t ≤ prepBudget B p q n, (routineKeep B p q hq).Runs t (readerFrame base n 0 0 0 0)
      (readerFrame base 0 0 d H (RAMLayout.width d H ((d+10)^4))) := by
  let d := B * Nat.clog 2 n
  let H := 2^BurstRAM.roundedUp p q n
  obtain ⟨t, ht, hb⟩ := computeBucket_run (L := InputWidth.Port) base d p q n hq hpq hn
  have copy := copy_run (K := InputBucketFromSize.Port) (L := InputWidth.Port) base n
  have addr := address_run (K := InputBucketFromSize.Port) (L := InputWidth.Port) B n base
  have first := FiniteRoutine.Runs.followedBy copy addr
  have second := FiniteRoutine.Runs.followedBy first hb
  have third := FiniteRoutine.Runs.followedBy second (incident_run base d H)
  refine ⟨_, ?_, third⟩
  unfold prepBudget
  exact Nat.add_le_add_right (Nat.add_le_add_left ht _) _

/-- Keep the bucket tally for subsequent validation after parsing the address and incident fields. -/
theorem runs_keep (B p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) (raw : List Bool) :
    let d := B * Nat.clog 2 n
    let H := 2^BurstRAM.roundedUp p q n
    ∃ t ≤ budget B p q n, (routineKeep B p q hq).Runs t (bank raw n 0 0 0 0)
      (bank raw 0 0 d H (RAMLayout.width d H ((d+10)^4))) := by
  obtain ⟨t, ht, h⟩ := keep_framed B p q n hq hpq hn (InputReader.prepared raw 0 0 [])
  exact ⟨t, ht.trans (Nat.le_add_right ..), h⟩

theorem runs_framed (B p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n)
    (base : Stacks InputPort) :
    let d := B * Nat.clog 2 n
    let H := 2^BurstRAM.roundedUp p q n
    ∃ t ≤ budget B p q n, (routine B p q hq).Runs t (readerFrame base n 0 0 0 0)
      (readerFrame base 0 0 d 0 (RAMLayout.width d H ((d+10)^4))) := by
  let d := B * Nat.clog 2 n
  let H := 2^BurstRAM.roundedUp p q n
  obtain ⟨t, ht, h⟩ := keep_framed B p q n hq hpq hn base
  exact ⟨_, Nat.add_le_add_right ht _, FiniteRoutine.Runs.followedBy h
    (clear_run base d H (RAMLayout.width d H ((d+10)^4)))⟩

/-- On the physical input tape the address and incident counts become available
to the parser and all private scratch stacks finish empty. -/
theorem runs (B p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) (raw : List Bool) :
    let d := B * Nat.clog 2 n
    let H := 2^BurstRAM.roundedUp p q n
    ∃ t ≤ budget B p q n, (routine B p q hq).Runs t (bank raw n 0 0 0 0)
      (bank raw 0 0 d 0 (RAMLayout.width d H ((d+10)^4))) :=
  runs_framed B p q n hq hpq hn _

/-- A constant depending only on the address multiplier and fixed exponent. -/
def clockCoefficient (B p q : ℕ) : ℕ :=
  7 + (B+32) + InputBucketFromSize.clockCoefficient p q + 917*(B+13)^7 + 3

/-- A polynomial clock for preparing both input fields, uniform in the tape length. -/
theorem budget_le (B p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) :
    budget B p q n ≤ clockCoefficient B p q * (n+1)^7 := by
  let d := B * Nat.clog 2 n
  let H := 2^BurstRAM.roundedUp p q n
  have hc : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hd : d ≤ B*n := Nat.mul_le_mul_left _ hc
  have hH : H ≤ 2*n := InputBucketFromSize.bucket_le hq hpq hn
  have hw : d+H+11 ≤ (B+13)*(n+1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have h₁ : n+1 ≤ (n+1)^7 := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (by decide : 1 ≤ 7)
  have h₂ : (n+1)^2 ≤ (n+1)^7 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
  have hcopy : 5*n+2 ≤ 7*(n+1)^7 := by
    apply (show 5*n+2 ≤ 7*(n+1) by omega).trans
    exact Nat.mul_le_mul_left _ h₁
  have hlog := (CeilLog.cost_le B n).trans (Nat.mul_le_mul_left _ h₁)
  have hwidth := (InputWidth.work_le_seventh d H).trans
    (Nat.mul_le_mul_left 917 (Nat.pow_le_pow_left hw 7))
  rw [Nat.mul_pow, ← Nat.mul_assoc] at hwidth
  have hclear : H+1 ≤ 3*(n+1)^7 := (show H+1 ≤ 3*(n+1) by omega).trans (Nat.mul_le_mul_left _ h₁)
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcopy hlog)
    (Nat.mul_le_mul_left (InputBucketFromSize.clockCoefficient p q) h₂)) hwidth) hclear
  simpa only [budget, prepBudget, clockCoefficient, d, H, Nat.add_mul] using hsum

end RAMTape.InputParameters

end VPVNP
end Computability
end OAI
