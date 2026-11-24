import OAI.Computability.VPVNP.SliceArithmeticMagnitude
import OAI.Computability.VPVNP.SliceArithmeticSubtract
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Register and stream interface for signed witness counts -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticSignedCount

open BurstRAM RAMTape TapeWord

/-- Caller ports for the two signed witness counts, the modulus and field width advice, and the
output coefficient. -/
inductive External where
  | positive | negative | prime | zeroWord | degree | result
  deriving DecidableEq
instance : Fintype External :=
  ⟨{.positive, .negative, .prime, .zeroWord, .degree, .result}, by intro i; cases i <;> simp⟩

/-- Work ports for reducing both witness counts, subtracting their residues, and emitting the
packed field coefficient. -/
inductive Private where
  | divide (i : DivisionStack.Port) | arithmetic (i : ISA.Port 3 0)
  | residue (negative : Bool) | scratch | marker
  deriving DecidableEq, Fintype

/-- Stack interface for converting a signed witness count into a power-basis field element. -/
abbrev Port := Private ⊕ External

/-- Encode the two input counts, field parameters, and result suffix on the external
signed-count ports. -/
def external (p e w : ℕ) (positive negative result : List Bool) : Stacks External
  | .positive => positive
  | .negative => negative
  | .prime => wordBits (Fin.ofNat (2^w) p)
  | .zeroWord => wordBits (0 : BurstRAM.Word w)
  | .degree => List.replicate e true
  | .result => result

/-- Install the current division input and the two saved residues alongside the caller's
stacks. -/
def frame (io : Stacks External) (input : List Bool) (residues : Bool → List Bool) : Stacks Port
  | .inr i => io i
  | .inl (.divide .input) => input
  | .inl (.residue sign) => residues sign
  | .inl _ => []

/-- Signed-count workspace with empty division input and empty residue stacks for both signs. -/
def clean (io : Stacks External) := frame io [] (fun _ => [])

/-- Select the negative count when `sign` is true and the positive count otherwise. -/
def source (sign : Bool) : External := if sign then .negative else .positive

/-- Route division through the advised prime and store its remainder on the port for the chosen
sign. -/
def divisionPorts (sign : Bool) : DivisionStack.Port → Port
  | .divisor => .inr .prime
  | .remainder => .inl (.residue sign)
  | i => .inl (.divide i)

private theorem division_injective (sign : Bool) : Function.Injective (divisionPorts sign) := by
  intro i j h
  cases i <;> cases j <;> simp_all [divisionPorts]

/-- A preserved count supplies the input of the division. Its quotient is
discarded, and the remainder remains on the selected arithmetic register. -/
def reduceCount (sign : Bool) : FiniteRoutine Port :=
  (SuccessorFields.prependCopy (.inr (source sign)) (.inl (.divide .input)) (.inl .scratch)).followedBy
    (SliceArithmeticMagnitude.machine.onPorts (divisionPorts sign))

/-- Step bound for copying an `n`-bit witness count and reducing it modulo a `w`-bit prime
word. -/
def reduceCost (n w : ℕ) := 5*n + 2 + SliceArithmeticMagnitude.cost n w

theorem reduceCount_runs {p w : ℕ} [NeZero p] (hw : SliceArithmetic.Word.workingWidth p ≤ w)
    (sign : Bool) (io : Stacks External) (r : Bool → List Bool) (empty : r sign = [])
    (hprime : io .prime = wordBits (Fin.ofNat (2^w) p)) :
    let x := io (source sign)
    let a : Fin p := Fin.ofNat p (value x)
    (reduceCount sign).Runs (reduceCost x.length w) (frame io [] r)
      (frame io [] (Function.update r sign (wordBits (SliceArithmetic.Word.limb w a)))) := by
  intro x a
  let d : BurstRAM.Word w := Fin.ofNat _ p
  let s := frame io [] r
  let m := frame io x r
  let u := frame io [] (Function.update r sign (wordBits (SliceArithmetic.Word.limb w a)))
  have hp : d.val = p := Nat.mod_eq_of_lt (SliceArithmetic.Word.modulus_lt hw)
  have copy := SuccessorFields.prependCopy_runs (.inr (source sign)) (.inl (.divide .input))
    (.inl Private.scratch) (by simp) (by simp) (by decide) s rfl
  have copied : Function.update s (.inl (.divide .input)) (s (.inr (source sign)) ++ s (.inl (.divide .input))) = m := by
    funext i
    rcases i with i|i
    · cases i with
      | divide j => cases j <;> simp [s, m, frame, x]
      | _ => rfl
    · rfl
  rw [copied] at copy
  have raw := SliceArithmeticMagnitude.machine_runs x d (hp.symm ▸ NeZero.pos p)
  have div : (SliceArithmeticMagnitude.machine.onPorts (divisionPorts sign)).Runs
      (SliceArithmeticMagnitude.cost x.length w) m u := by
    apply FiniteRoutine.runs_onPorts_framed _ (division_injective sign) raw
    · intro i
      cases i with
      | divisor => exact hprime
      | remainder => exact empty
      | _ => rfl
    · intro i
      cases i with
      | divisor => exact hprime
      | remainder =>
        change Function.update r sign _ sign = _
        rw [Function.update_self, hp]
        rfl
      | _ => rfl
    · rintro (i|i) hi
      · cases i with
        | divide j => cases j <;> first | rfl | exact (hi .input rfl).elim
        | residue b =>
          have h : b ≠ sign := fun eq => hi .remainder (by rw [eq]; rfl)
          exact Function.update_of_ne h ..
        | _ => rfl
      · rfl
  exact copy.followedBy div

/-- Map the subtraction registers to the prime and the two saved residues, using the caller's
zero word as width template. -/
def arithmeticPorts : ISA.Port 3 0 → Port
  | .reg i => Fin.cases (.inr .prime) (Fin.cases (.inl (.residue false)) (fun _ => .inl (.residue true))) i
  | .persistent => .inr .zeroWord
  | i => .inl (.arithmetic i)

private theorem arithmetic_injective : Function.Injective arithmeticPorts := by
  change ∀ i j : ISA.Port 3 0, arithmeticPorts i = arithmeticPorts j → i = j
  decide

theorem subtract_runs {p w : ℕ} [NeZero p] (hw : SliceArithmetic.Word.workingWidth p ≤ w)
    (io : Stacks External) (a b : Fin p)
    (hp : io .prime = wordBits (Fin.ofNat (2^w) p)) (hz : io .zeroWord = wordBits (0 : BurstRAM.Word w)) :
    let bits (x : Fin p) := wordBits (SliceArithmetic.Word.limb w x)
    ∃ t ≤ 400 * (w+1)^2, (SliceArithmeticSubtract.machine.onPorts arithmeticPorts).Runs t
      (frame io [] (fun sign => if sign then bits b else bits a))
      (frame io [] (fun sign => if sign then bits (-b) else bits (a-b))) := by
  intro bits
  let d : BurstRAM.Word w := Fin.ofNat _ p
  obtain ⟨t, ht, sub⟩ := SliceArithmeticSubtract.machine_runs hw d (Nat.mod_eq_of_lt (SliceArithmetic.Word.modulus_lt hw)) a b
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_onPorts_framed _ arithmetic_injective sub
  · intro i
    cases i with
    | reg i => fin_cases i <;> first | rfl | exact hp
    | persistent => exact hz
    | pub i => exact i.elim0
    | work => rfl
    | logPort j => cases j <;> rfl
  · intro i
    cases i with
    | reg i => fin_cases i <;> first | rfl | exact hp
    | persistent => exact hz
    | pub i => exact i.elim0
    | work => rfl
    | logPort j => cases j <;> rfl
  rintro (i|i) hi
  · cases i with
    | residue sign => cases sign <;> first | exact (hi (.reg 1) rfl).elim | exact (hi (.reg 2) rfl).elim
    | divide j => cases j <;> rfl
    | _ => rfl
  · rfl

end SliceArithmeticSignedCount

end VPVNP
end Computability
end OAI
