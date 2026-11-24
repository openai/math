import OAI.Computability.VPVNP.RAMTapeInputStartup
import OAI.Computability.VPVNP.RAMTapeInputParameters

/-!
# Complete uniform finite-stack reader for a live site

The only initially occupied stack contains the physical input. This fixed
control measures its length, prepares the exact widths, and extracts the
literal data fields. It retains the public length, address width, and bucket
capacity in unary for the site's remaining computations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputReader

open BurstRAM ProcessorInput RAMLayout UniversalMachine StackCompiler

/-- Retained unary length and address-width tallies of the physical site reader. -/
inductive Public where
  | length | address
  deriving DecidableEq

instance : Fintype Public := derive_fintype% _

/-- Complete reader bank combining parsing ports, parameter scratch, and the retained public
tallies. -/
abbrev Registers := InputPort ⊕ (InputParameters.Scratch ⊕ Public)

/-- Port holding the measured length of the full physical input in unary. -/
def lengthPort : Registers := .inr (.inr .length)
/-- Port holding the computed site address width in unary. -/
def addressWidthPort : Registers := .inr (.inr .address)
/-- Port holding the computed bucket capacity in unary. -/
def bucketPort : Registers := .inr (.inl .bucket)

private abbrev ones (n : ℕ) := List.replicate n true

private def corePort : InputPort ⊕ InputParameters.Scratch → Registers := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)

private theorem core_injective : Function.Injective corePort := by
  intro x y h
  cases x <;> cases y <;> simp_all [corePort]

private def decorate (core : Stacks (InputPort ⊕ InputParameters.Scratch)) (n d : ℕ) : Stacks Registers
  | .inl i => core (.inl i)
  | .inr (.inl i) => core (.inr i)
  | .inr (.inr .length) => ones n
  | .inr (.inr .address) => ones d

private theorem decorate_core (s : Stacks (InputPort ⊕ InputParameters.Scratch)) (n d : ℕ)
    (i : InputPort ⊕ InputParameters.Scratch) : decorate s n d (corePort i) = s i := by cases i <;> rfl

private def savePort (p : Public) : Registers := .inr (.inr p)
private def sourcePort : Public → InputPort
  | .length => .size
  | .address => .addressCount

private def copyPorts (p : Public) : CeilLog.Port → Registers
  | .src => .inl (sourcePort p)
  | .out => savePort p
  | .tmp => .inl .tmp

private def retain (p : Public) : FiniteRoutine Registers :=
  (FiniteRoutine.ofRoutine (Tally.copyAdd CeilLog.Port.src .out .tmp)).onPorts (copyPorts p)

private theorem retain_run (p : Public) (s : Stacks Registers) (k : ℕ)
    (hs : s (.inl (sourcePort p)) = ones k) (ht : s (.inl .tmp) = []) (ho : s (savePort p) = []) :
    (retain p).Runs (5*k+2) s (Function.update s (savePort p) (ones k)) := by
  let vals : Tally.State CeilLog.Port := fun i => if i = .src then k else 0
  have run := Tally.copyAdd_runs CeilLog.Port.src .out .tmp (by decide) (by decide) (by decide) vals rfl
  apply FiniteRoutine.runs_onPorts_framed _ (by intro i j hij; cases p <;> cases i <;> cases j <;> simp_all [copyPorts, sourcePort, savePort]) run
  · intro i; cases i with
    | src => exact hs
    | tmp => exact ht
    | out => exact ho
  · intro i
    cases i with
    | src => simpa [copyPorts, savePort, vals, Tally.encode] using hs
    | tmp => simpa [copyPorts, savePort, vals, Tally.encode] using ht
    | out => simp [copyPorts, vals, Tally.encode, ones]
  · intro i hi
    exact Function.update_of_ne (Ne.symm (hi .out)) ..

private def measure : FiniteRoutine Registers := (FiniteRoutine.ofRoutine lengthRoutine).onPorts Sum.inl
private def fields : FiniteRoutine Registers := (FiniteRoutine.ofRoutine parse).onPorts Sum.inl

/-- Code independent of the length. The rational exponent of the live bucket
is `p/q` (in the paper, `1-δ`). -/
def physicalReader (B p q : ℕ) (hq : 0 < q) : FiniteRoutine Registers :=
  (((measure.followedBy (retain .length)).followedBy
    ((InputParameters.routineKeep B p q hq).onPorts corePort)).followedBy (retain .address)).followedBy fields

/-- All private scratch is empty at return. The length, address width and
bucket capacity are available alongside the actual prefix and data fields. -/
def physicalResult (n d H : ℕ) (pref addr hdr inc : List Bool) : Stacks Registers
  | .inl .prefix => pref
  | .inl .address => addr
  | .inl .header => hdr
  | .inl .incident => inc
  | .inr (.inl .bucket) => ones H
  | .inr (.inr .length) => ones n
  | .inr (.inr .address) => ones d
  | _ => []

/-- From just the original site tape, the fixed processor obtains its local
input with polynomially bounded bit-stack instructions. The public parameters
are computed on its branch path from the length. -/
theorem physicalReader_runs (B p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) (prog : UniversalMachine.Program)
    (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let H := 2^(roundedUp p q n)
    let w := (d+10)^4
    ∀ (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool),
      Fits prog n d H w →
      let raw := ProcessorInput.tape prog n v hdr inc
      ∃ steps ≤ (InputParameters.clockCoefficient B p q + 43)*(n+1)^7,
        (physicalReader B p q hq).Runs steps (labeledInput (.inl InputPort.input) raw)
          (physicalResult n d H (programPrefix prog) (List.ofFn (RAMSerialization.wordBits d v))
            (List.ofFn hdr) (List.ofFn inc)) := by
  intro d H w v hdr inc hf raw
  let D := width d H w
  let src := InputParameters.bank raw n 0 0 0 0
  let dest := InputParameters.bank raw 0 0 d H D
  have hlen : raw.length = n := ProcessorInput.length_tape prog v hdr inc hf
  have hsmall := lengthRoutine_runs (prepared raw 0 0 []) rfl
  change lengthRoutine.Runs (5*raw.length+2) _ (Function.update _ .size (ones raw.length ++ [])) at hsmall
  rw [hlen, List.append_nil] at hsmall
  have h₀ : measure.Runs (5*n+2) (labeledInput (.inl InputPort.input) raw) (decorate src 0 0) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hsmall
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · rintro (i | j) hh
      · exact (hh i rfl).elim
      · cases j with
        | inl k => cases k <;> rfl
        | inr k => cases k <;> rfl
  have h₁ := retain_run .length (decorate src 0 0) n rfl rfl rfl
  have e₁ : Function.update (decorate src 0 0) (savePort .length) (ones n) = decorate src n 0 := by
    funext i; rcases i with i | (i | i) <;> first | rfl | cases i <;> rfl
  rw [e₁] at h₁
  obtain ⟨t, ht, hp⟩ := InputParameters.runs_keep B p q n hq hpq hn raw
  have h₂ : ((InputParameters.routineKeep B p q hq).onPorts corePort).Runs t (decorate src n 0)
      (decorate dest n 0) := by
    apply FiniteRoutine.runs_onPorts_framed _ core_injective hp (decorate_core src n 0) (decorate_core dest n 0)
    rintro (i | (i | i)) hh
    · exact (hh (.inl i) rfl).elim
    · exact (hh (.inr i) rfl).elim
    · cases i <;> rfl
  have h₃ := retain_run .address (decorate dest n 0) d rfl rfl rfl
  have e₃ : Function.update (decorate dest n 0) (savePort .address) (ones d) = decorate dest n d := by
    funext i; rcases i with i | (i | i) <;> first | rfl | cases i <;> rfl
  rw [e₃] at h₃
  obtain ⟨z, hz, hflds⟩ := parse_processorTape prog n v hdr inc [] hf
  let target := physicalResult n d H (programPrefix prog) (List.ofFn (RAMSerialization.wordBits d v))
    (List.ofFn hdr) (List.ofFn inc)
  have h₄ : fields.Runs z (decorate dest n d) target := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective hflds
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · rintro (i | (i | i)) hh
      · exact (hh i rfl).elim
      · cases i <;> rfl
      · cases i <;> rfl
  refine ⟨_, ?_, (((h₀.followedBy h₁).followedBy h₂).followedBy h₃).followedBy h₄⟩
  have hd : d ≤ n := by change (programPrefix prog).length + (d + 4 + D) ≤ n at hf; omega
  have hb := InputParameters.budget_le B p q n hq hpq hn
  have hrest := Nat.mul_le_mul_left 43 (Nat.le_self_pow (by decide : 7 ≠ 0) (n+1))
  rw [Nat.add_mul]
  omega

end RAMTape.InputReader

end VPVNP
end Computability
end OAI
