import OAI.Computability.VPVNP.RAMProcessorCreditPorts
import OAI.Computability.VPVNP.RAMTapeWordOperands
import OAI.Computability.VPVNP.RAMTapeUnaryWordValue

/-!
# Resetting the private interpreter's call credits

The reset copies the two public unary allowances and snapshots the cumulative
cost. A second scan of the cost word supplies the width for the zero probe
ordinal. Each scan restores its source and clears the previous destination.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit

open BurstRAM TapeWord

private inductive Field where
  | call | fuel | start | ordinal
  deriving DecidableEq

private def source : Field → Port
  | .call => .publicH
  | .fuel => .publicFuel
  | .start | .ordinal => .budget .cost

private def destination : Field → Port
  | .call => .budget .call
  | .fuel => .budget .fuel
  | .start => .savedStart
  | .ordinal => .ordinal

private def ports (f : Field) : ScanPort → Port
  | .left => source f
  | .right => .copyA
  | .tmp => .copyB
  | .out => destination f

private theorem ports_injective (f : Field) : Function.Injective (ports f) := by
  intro i j h
  cases f <;> cases i <;> cases j <;> simp_all [ports, source, destination]

private def bit (f : Field) (_ : Unit) (b : Bool) : Bool × Unit :=
  (if f = .ordinal then false else b, ())

private def payload (f : Field) (xs : List Bool) :=
  if f = .ordinal then List.replicate xs.length false else xs

private theorem emitted (f : Field) (xs : List Bool) :
    Operand.emitted (bit f) () xs = (payload f xs, ()) := by
  induction xs with
  | nil => simp [Operand.emitted, payload]
  | cons b xs ih =>
    rw [Operand.emitted]
    simp only [bit, ih]
    by_cases h : f = .ordinal <;> simp [payload, h, List.replicate_succ]

private def normal : Operand.State Unit → Bool
  | .done _ => true
  | _ => false

private def writeField (f : Field) : FiniteRoutine Port :=
  .ofStackCode (Operand.code (bit f)) (ports f) (.clear ()) normal

private def written (f : Field) (s : Stacks Port) :=
  Function.update s (destination f) (payload f (s (source f)))

private theorem writeField_runs (f : Field) (s : Stacks Port) (ha : s .copyA = []) (hb : s .copyB = []) :
    (writeField f).Runs ((s (destination f)).length + 7*(s (source f)).length + 3) s (written f s) := by
  have run := Operand.run (bit f) () (s (source f)) (s (destination f))
  rw [emitted] at run
  refine FiniteRoutine.runs_ofStackCode_framed (ports_injective f) (normal := normal) rfl rfl
    (fun q h => ?_) run ?_ ?_ ?_
  · cases q <;> first | rfl | contradiction
  · intro i
    cases i <;> first | rfl | exact ha | exact hb
  · intro i
    cases f <;> cases i <;> simp [written, ports, destination, source, scanStacks, ha, hb]
  · intro i hi
    exact Function.update_of_ne (Ne.symm (hi .out)) ..

/-- Install the public budgets and record the start of this call. -/
def resetCredits : FiniteRoutine Port :=
  (((writeField .call).followedBy (writeField .fuel)).followedBy (writeField .start)).followedBy
    (writeField .ordinal)

/-- Only the two per-call allowances, start cost and probe ordinal are replaced. -/
def resetFrame (s : Stacks Port) : Stacks Port
  | .budget .call => s .publicH
  | .budget .fuel => s .publicFuel
  | .savedStart => s (.budget .cost)
  | .ordinal => List.replicate (s (.budget .cost)).length false
  | i => s i

/-- Exact running time on a caller's frame. Empty, partially used, and
full destination stacks are all permitted. -/
theorem resetCredits_framed (s : Stacks Port) (ha : s .copyA = []) (hb : s .copyB = []) :
    resetCredits.Runs ((s (.budget .call)).length + (s (.budget .fuel)).length +
      (s .savedStart).length + (s .ordinal).length +
      7*((s .publicH).length + (s .publicFuel).length + 2*(s (.budget .cost)).length) + 12)
      s (resetFrame s) := by
  let s₁ := written .call s
  let s₂ := written .fuel s₁
  let s₃ := written .start s₂
  have h₁ := writeField_runs .call s ha hb
  have h₂ := writeField_runs .fuel s₁ (by simpa [s₁, written, destination] using ha)
    (by simpa [s₁, written, destination] using hb)
  have h₃ := writeField_runs .start s₂ (by simpa [s₂, s₁, written, destination] using ha)
    (by simpa [s₂, s₁, written, destination] using hb)
  have h₄ := writeField_runs .ordinal s₃ (by simpa [s₃, s₂, s₁, written, destination] using ha)
    (by simpa [s₃, s₂, s₁, written, destination] using hb)
  have h := ((h₁.followedBy h₂).followedBy h₃).followedBy h₄
  have he : written .ordinal s₃ = resetFrame s := by
    funext i
    cases i with
    | budget p => cases p <;> rfl
    | _ => rfl
  rw [he] at h
  convert h using 1
  · rfl
  · simp [s₃, s₂, s₁, written, destination, source]
    omega

/-- Starting a call reloads the full fuel and call budgets, records the old
cumulative cost, and initializes the ordinal to the width-correct zero. -/
theorem resetCredits_run {w : ℕ} (H fuelCap fuel call site : ℕ) (cap g c : Word w)
    (saved ord : List Bool) :
    resetCredits.Runs (call + fuel + saved.length + ord.length + 7*(H + fuelCap + 2*w) + 12)
      (bank H fuelCap fuel call site cap g c saved ord)
      (bank H fuelCap fuelCap H site cap g c (wordBits c) (wordBits (0 : Word w))) := by
  let s := bank H fuelCap fuel call site cap g c saved ord
  have h := resetCredits_framed s rfl rfl
  have he : resetFrame s = bank H fuelCap fuelCap H site cap g c (wordBits c) (wordBits (0 : Word w)) := by
    funext i
    cases i with
    | budget p => cases p <;> rfl
    | ordinal =>
      change List.replicate (wordBits c).length false = wordBits (0 : Word w)
      rw [length_wordBits, UnaryWord.zeros_wordBits]
    | _ => rfl
  rw [he] at h
  simpa only [s, bank, Charges.bank, Charges.Data.stacks, List.length_replicate, length_wordBits] using h

end RAMTape.CallCredit

end VPVNP
end Computability
end OAI
