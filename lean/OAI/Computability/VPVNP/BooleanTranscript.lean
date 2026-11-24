import OAI.Computability.VPVNP.Circuits
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Boolean gate transcripts

Section 1.1 of *VP and VNP differ over every field* represents a deterministic
Boolean verifier by summing a product of local consistency tests over all gate
values. Each gate in the verifier may reuse any previously computed gate. On
Boolean inputs the product singles out its unique transcript over every field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BooleanTranscript

variable {σ R S : Type*} {n : ℕ}

/-- Encode a Boolean value by the corresponding ring element. -/
def bit [Zero R] [One R] (b : Bool) : R := if b then 1 else 0

/-- Equality test on two Boolean-valued elements of a ring. -/
def equalBit [CommRing R] (a b : R) : R := a * b + (1 - a) * (1 - b)

theorem equalBit_bits [CommRing R] (a b : Bool) :
    equalBit (bit a : R) (bit b) = if a = b then 1 else 0 := by
  cases a <;> cases b <;> simp [equalBit, bit]

/-- AND and NOT with topologically ordered references, a complete Boolean gate basis. -/
inductive Gate (σ : Type*) (n : ℕ) where
  | and (a b : Ref Bool σ n)
  | not (a : Ref Bool σ n)

/-- Compute the Boolean result of an AND or NOT gate from its referenced inputs and earlier
wires. -/
def Gate.eval (input : σ → Bool) (wires : Fin n → Bool) : Gate σ n → Bool
  | .and a b => a.read id input wires && b.read id input wires
  | .not a => !(a.read id input wires)

/-- Interpret AND as multiplication and NOT as subtraction from one in the coefficient ring. -/
def Gate.arith [CommRing R] (input : σ → R) (wires : Fin n → R) : Gate σ n → R
  | .and a b => a.read bit input wires * b.read bit input wires
  | .not a => 1 - a.read bit input wires

private theorem read_bits [CommRing R] (input : σ → Bool) (w : Fin n → Bool) (r : Ref Bool σ n) :
    r.read (bit (R := R)) (bit ∘ input) (bit ∘ w) = bit (r.read id input w) := by
  cases r <;> rfl

theorem Gate.arith_bits [CommRing R] (input : σ → Bool) (w : Fin n → Bool) (g : Gate σ n) :
    g.arith (bit ∘ input) (bit ∘ w) = (bit (g.eval input w) : R) := by
  cases g with
  | and a b =>
    simp only [Gate.arith, Gate.eval, read_bits]
    cases a.read id input w <;> cases b.read id input w <;> simp [bit]
  | not a =>
    simp only [Gate.arith, Gate.eval, read_bits]
    cases a.read id input w <;> simp [bit]

/-- A Boolean program built by adjoining one gate at a time. Each new gate can refer to all
preceding gates. -/
inductive Program (σ : Type*) : ℕ → Type _ where
  | nil : Program σ 0
  | snoc {n : ℕ} (p : Program σ n) (g : Gate σ n) : Program σ (n + 1)

/-- The Boolean value at each gate after running the program on the given inputs. -/
def Program.run (input : σ → Bool) : {n : ℕ} → Program σ n → Fin n → Bool
  | _, .nil => Fin.elim0
  | _, .snoc p g => Fin.snoc (p.run input) (g.eval input (p.run input))

/-- Product of all gate tests, evaluated on a proposed transcript. -/
def Program.check [CommRing R] (input : σ → R) : {n : ℕ} → Program σ n → (Fin n → R) → R
  | _, .nil, _ => 1
  | k + 1, .snoc p g, w =>
    p.check input (Fin.init w) * equalBit (g.arith input (Fin.init w)) (w (Fin.last k))

/-- The gate tests have value one at the true transcript and zero at every other
Boolean transcript. This is an identity over any commutative ring. -/
theorem Program.check_bits [CommRing R] (input : σ → Bool) (p : Program σ n) (w : Fin n → Bool) :
    p.check (bit ∘ input) (bit ∘ w) = if w = p.run input then (1 : R) else 0 := by
  induction p with
  | nil => simp [Program.check, Subsingleton.elim w (Program.nil.run input)]
  | @snoc k p g ih =>
    obtain ⟨⟨b, v⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (k + 1) => Bool)).surjective w
    change (p.snoc g).check (bit ∘ input) (bit ∘ Fin.snoc v b) =
      if Fin.snoc v b = (p.snoc g).run input then (1 : R) else 0
    simp only [Program.check, Program.run, ← Fin.comp_init, Fin.init_snoc,
      Function.comp_apply, Fin.snoc_last, ih, Gate.arith_bits, equalBit_bits, Fin.snoc_inj]
    by_cases h : v = p.run input
    · subst v
      simp [eq_comm]
    · simp [h]

/-- A Boolean program together with the reference whose bit is returned to the verifier. -/
structure Circuit (σ : Type*) (n : ℕ) where
  /-- The ordered gates whose computed bits form the transcript. -/
  program : Program σ n
  /-- The input, Boolean constant, or gate bit chosen as the circuit's result. -/
  output : Ref Bool σ n

/-- Evaluate the program on the Boolean input and read its designated output bit. -/
def Circuit.eval (c : Circuit σ n) (input : σ → Bool) : Bool :=
  c.output.read id input (c.program.run input)

/-- The transcript tests multiplied by the acceptance indicator. -/
def Circuit.weight [CommRing R] (c : Circuit σ n) (input : σ → R) (w : Fin n → R) : R :=
  c.program.check input w * c.output.read bit input w

/-- Summing over gate assignments recovers the Boolean verifier's answer. -/
theorem Circuit.sum_weight_bits [CommRing R] (c : Circuit σ n) (input : σ → Bool) :
    ∑ w : Fin n → Bool, c.weight (bit ∘ input) (bit ∘ w) = (bit (c.eval input) : R) := by
  simp [Circuit.weight, Program.check_bits, ite_mul, read_bits, Circuit.eval]

private theorem read_hom [CommRing R] [CommRing S] (f : R →+* S) (input : σ → R)
    (w : Fin n → R) (r : Ref Bool σ n) :
    f (r.read bit input w) = r.read bit (f ∘ input) (f ∘ w) := by
  cases r with
  | const b => cases b <;> simp [Ref.read, bit]
  | var | gate => rfl

private theorem Gate.arith_hom [CommRing R] [CommRing S] (f : R →+* S) (input : σ → R)
    (w : Fin n → R) (g : Gate σ n) :
    f (g.arith input w) = g.arith (f ∘ input) (f ∘ w) := by
  cases g <;> simp [Gate.arith, read_hom]

theorem Program.check_hom [CommRing R] [CommRing S] (f : R →+* S) (input : σ → R)
    (p : Program σ n) (w : Fin n → R) :
    f (p.check input w) = p.check (f ∘ input) (f ∘ w) := by
  induction p with
  | nil => simp [Program.check]
  | snoc p g ih => simp [Program.check, equalBit, ih, Gate.arith_hom, Fin.comp_init]

theorem Circuit.weight_hom [CommRing R] [CommRing S] (f : R →+* S) (c : Circuit σ n)
    (input : σ → R) (w : Fin n → R) :
    f (c.weight input w) = c.weight (f ∘ input) (f ∘ w) := by
  simp [Circuit.weight, Program.check_hom, read_hom]

end BooleanTranscript

end VPVNP
end Computability
end OAI
