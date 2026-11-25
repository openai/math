import OAI.Computability.NearSquareRoot.KernelSelectorStream
import OAI.Computability.NearSquareRoot.KernelPass

/-!
# Tape execution of the address-dependent coefficient lookup in a scale pass

A normalized template reads two adjacent bits of each slot per mathematical
column. The scanner remembers the first bit of each pair while traversing
the aligned slots. It then adds the column test to a finite vector over ℤ/2.
All physical address words and the coefficient stream are generated in tape
order from their common width.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleStream
open IntegerMultiplication IntegerMultiplication.Code
open KernelSelectorAlign (Column slots flatBits foldSlots get ofFn)

private theorem finiteLookup {a : ℕ} {S Y : Type} [Finite S] [Codec Y]
    (step : S → Column a → S) (init : S) (out : S → Y) :
    Task List.length (fun xs => send (flatBits a xs))
      (fun xs => send (out (xs.foldl step init))) := by
  classical
  let := Fintype.ofFinite S
  let e := Fintype.equivFin S
  let : Codec S := ⟨fun s => send (e s)⟩
  let : FiniteState S := ⟨inferInstance, (FiniteState.identify (X := Fin (Fintype.card S))).comp e.injective⟩
  obtain ⟨C, bound⟩ := (Set.finite_range (size (X := S))).bddAbove
  have scan := (KernelSelectorAlign.flatToSlots a).compose (foldSlots a step init)
  have lookup := (Easy.finite out).on (fun xs : List (Column a) => xs.foldl step init)
  apply (scan.compose lookup).bound (C+3)
  intro xs
  have sz := bound (Set.mem_range_self (xs.foldl step init))
  change size (xs.foldl step init) ≤ C at sz
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Join two successive columns of individual bits to recover the template's
paired column. Slots are the most significant fields. -/
def paired {a : ℕ} (u v : Column a) : KernelPass.Column (a+1) :=
  fun i j => if j = 0 then (get a u i).toNat else (get a v i).toNat

def split (a : ℕ) (c : KernelPass.Column (a+1)) (j : Fin 2) : Column a :=
  ofFn a fun i => decide (c i j = 1)

private theorem bit_value (x : ZMod 2) : ((decide (x = 1)).toNat : ZMod 2) = x := by
  have h : x = 0 ∨ x = 1 := by fin_cases x <;> first | left; rfl | right; rfl
  rcases h with rfl | rfl <;> decide

theorem paired_split (a : ℕ) (c : KernelPass.Column (a+1)) :
    paired (split a c 0) (split a c 1) = c := by
  funext i j
  fin_cases j <;> simp [paired, split, bit_value]

@[simp] theorem split_paired_left {a : ℕ} (u v : Column a) :
    split a (paired u v) 0 = u := by
  have e : (fun i : Fin (a+1) => decide (paired u v i 0 = 1)) = get a u := by
    funext i
    cases h : get a u i <;> simp [paired, h]
  simp [split, e]

@[simp] theorem split_paired_right {a : ℕ} (u v : Column a) :
    split a (paired u v) 1 = v := by
  have e : (fun i : Fin (a+1) => decide (paired u v i 1 = 1)) = get a v := by
    funext i
    cases h : get a v i <;> simp [paired, h]
  simp [split, e]

/-- Stream of single-bit columns in physical left-to-right order. Each pair
comes from one column of the normalized plan. -/
def singleColumns {a : ℕ} (s : List (KernelPass.Column (a+1))) : List (Column a) :=
  s.flatMap fun c => [split a c 0, split a c 1]

private def tick {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (r : Option (Column a) × (Fin q → ZMod 2)) (x : Column a) :
    Option (Column a) × (Fin q → ZMod 2) :=
  match r.1 with
  | none => (some x,r.2)
  | some u => (none,r.2 + test (paired u x))

private theorem fold_pairs {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (l : List (KernelPass.Column (a+1))) (s : Fin q → ZMod 2) :
    (singleColumns l).foldl (tick test) (none,s) = (none, s + (l.map test).sum) := by
  induction l generalizing s with
  | nil => simp [singleColumns]
  | cons c l ih =>
    simp only [singleColumns, List.flatMap_cons, List.cons_append, List.nil_append,
      List.foldl_cons, tick, paired_split]
    simpa [singleColumns, List.map_cons, add_assoc] using ih (s + test c)

/-- Fixed-point constants used by the scale pass. The numerator magnitude is
a little-endian P192 bit word and the power-of-two denominator a unary ruler. -/
abbrev ScalarWord := Bool × Bits.Word × Tally

def scalarWord (x : KernelPass.Coefficient) : ScalarWord :=
  (decide (x.1 < 0), Bits.phrase (Nat.log 2 x.1.natAbs+1) x.1.natAbs, tally x.2)

def wordValue (w : ScalarWord) : ℚ :=
  (if w.1 then -(Bits.value w.2.1 : ℚ) else (Bits.value w.2.1 : ℚ)) / 2^w.2.2.length

@[simp] theorem wordValue_scalarWord (x : KernelPass.Coefficient) :
    wordValue (scalarWord x) = KernelPass.value x := by
  obtain ⟨z,p⟩ := x
  simp only [wordValue, scalarWord, Bits.value_phrase (Nat.lt_pow_succ_log_self (by decide : 1<2) _),
    tally_length, KernelPass.value, decide_eq_true_eq]
  cases z <;> simp

/-- The scalar emitted for a given sequence of individual physical columns. -/
def emit {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → KernelPass.Coefficient) (l : List (Column a)) : ScalarWord :=
  scalarWord (table (l.foldl (tick test) (none,0)).2)

/-- The encoding used by the tape algorithm has the exact diagonal value of
the formally specified scale instruction, including zero query functions. -/
theorem emit_correct {a q h : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → KernelPass.Coefficient) (x : KernelPass.Addr (a+1) h) :
    wordValue (emit test table (singleColumns (List.ofFn x))) =
      (KernelPass.Plan.scale q test table).eval h (0,x) (0,x) := by
  simp [emit, fold_pairs, KernelPass.Plan.eval, List.map_ofFn, Fin.sum_ofFn]

/-- Binary code for the finite state selected by the column scans. -/
def tag {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2) (l : List (Column a)) :
    Fin (2^q) := finFunctionFinEquiv (l.foldl (tick test) (none,0)).2

theorem tagTask {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2) :
    Task List.length (fun xs => send (flatBits a xs)) (fun xs => send (tag test xs)) :=
  finiteLookup (tick test) (none,0) (fun s => finFunctionFinEquiv s.2)

theorem tag_singleColumns {a q h : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (x : KernelPass.Addr (a+1) h) :
    finFunctionFinEquiv.symm (tag test (singleColumns (List.ofFn x))) =
      ∑ j, test (x j) := by
  simp [tag, fold_pairs, List.map_ofFn, Fin.sum_ofFn]
  exact Equiv.symm_apply_apply finFunctionFinEquiv _

/-- Every scale coefficient is emitted by an actual P192 fixed-tape program.
A slot holds 2h adjacent bits, so the physical width is k = (a+1)2h.
The execution costs O(2^k(k+1)) steps and clears its scratch area. -/
theorem physical_scale {a q : ℕ} (test : KernelPass.Column (a+1) → Fin q → ZMod 2)
    (table : (Fin q → ZMod 2) → KernelPass.Coefficient) :
    ShortWord.PhysicalTask (fun h => ((a+1)*(2*h)+1)*2^((a+1)*(2*h)))
      (fun h => send (tally ((a+1)*(2*h))))
      (fun h => send ((KernelSelector.addressColumns a (2*h)).map (emit test table))) := by
  have one := finiteLookup (tick test) (none,0) (fun s => scalarWord (table s.2))
  exact ShortWord.physicalTask ((KernelSelector.generateColumnTable _ one).on (fun h => 2*h))

end KernelScaleStream

end NearSquareRoot
end Computability
end OAI
