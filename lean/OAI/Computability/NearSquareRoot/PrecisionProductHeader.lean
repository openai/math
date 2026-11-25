import OAI.Computability.IntegerMultiplication.Bits.Small
import OAI.Computability.IntegerMultiplication.Code.Automata
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.NearSquareRoot.PrecisionProductZip
import OAI.Computability.NearSquareRoot.PrecisionGrid

/-! # Reading the fractional precision from an operand stream

A stored real component has length `96*k+5`. The transducer counts in
groups of 96 bits and emits 70 unary symbols for each complete group,
then appends one symbol. Reading a single record suffices for the entire
stream, including when the right operand has the wider coefficient format.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductPass

open IntegerMultiplication Code FixedPoint

private def counter (_ : Bool) (s : Fin 96) : Fin 96 × Tally :=
  (⟨(s.val+1)%96, Nat.mod_lt _ (by decide)⟩, if s.val = 95 then tally 70 else [])

private theorem counter_length (l : Bits.Word) (s : Fin 96) :
    (machine counter (l,s)).1.length = 70*((s.val+l.length)/96) := by
  induction l generalizing s with
  | nil => simp [machine, Nat.div_eq_of_lt s.isLt]
  | cons x l ih =>
    rw [machine_cons]
    change ((if s.val = 95 then tally 70 else []) ++
      (machine counter (l, ⟨(s.val+1)%96, by omega⟩)).1).length = _
    rw [List.length_append, ih, List.length_cons]
    have := s.isLt
    split_ifs <;> simp only [tally_length, List.length_nil] <;> omega

private def readFraction (l : List Dusk.Pair) : Tally :=
  () :: (machine counter ((l.headD ([],[])).1, 0)).1

private theorem readFraction_easy : Easy readFraction := by
  have h := (Iter.leader (X := Dusk.Pair) ([],[])).fstCompose
  have m := (h.pair (Easy.const (0 : Fin 96))).machine (step := counter)
  exact m.fstCompose.compose (by fun_prop : Easy (fun l : Tally => () :: l))

private theorem readFraction_eq {n k : ℕ} (x : Fin n → Record k) (hn : 0 < n) :
    readFraction (List.ofFn (fun j => Dusk.mark (x j))) = tally (fractionBits k) := by
  rw [← recover_tally (readFraction _)]
  congr 1
  simp only [readFraction, List.length_cons, counter_length]
  have head : (List.ofFn (fun j => Dusk.mark (x j))).headD ([],[]) = Dusk.mark (x ⟨0,hn⟩) := by
    cases n with
    | zero => omega
    | succ n => simp [List.ofFn_succ]
  rw [head]
  simp only [Dusk.mark,Dusk.trip_length, componentBits, fractionBits]
  omega

/-- Build the product's header from the first right record. The left and
right lists are separate at entry and remain in their original order. -/
theorem headerFromRight {I : Type} (N k : I → ℕ) (a : I → List Dusk.Pair)
    (b : (i : I) → Fin (N i) → Record (k i)) (hN : ∀ i, 0 < N i) :
    Task (fun i => size (a i, List.ofFn (fun j => Dusk.mark (b i j))))
      (fun i => send (a i, List.ofFn (fun j => Dusk.mark (b i j))))
      (fun i => send (a i, tally (fractionBits (k i)), List.ofFn (fun j => Dusk.mark (b i j)))) := by
  have easy : Easy (fun p : List Dusk.Pair × List Dusk.Pair => (p.1, readFraction p.2, p.2)) :=
    Easy.fst.pair ((Easy.snd.compose readFraction_easy).pair Easy.snd)
  have run := easy.on (fun i => (a i, List.ofFn (fun j => Dusk.mark (b i j))))
  simpa only [readFraction_eq (b _) (hN _)] using run

/-- Bounds for synthesizing the header from two address-ordered arrays.
The right-hand address width `q` can differ from the data width `k`. -/
theorem headerFromArrays {I : Type} (N k q : I → ℕ)
    (a : (i : I) → Fin (N i) → Dusk.Pair) (b : (i : I) → Fin (N i) → Record (q i))
    (C : ℕ) (ha : ∀ i j, size (a i j) ≤ C*(k i+1))
    (hb : ∀ i j, size (Dusk.mark (b i j)) ≤ C*(k i+1)) (hN : ∀ i, 0 < N i) :
    Space.BoundedTask (fun i => (N i+1)*(k i+1)) (fun i => (N i+1)*(k i+1))
      (fun i => send (List.ofFn (a i), List.ofFn fun j => Dusk.mark (b i j)))
      (fun i => send (List.ofFn (a i), tally (fractionBits (q i)), List.ofFn fun j => Dusk.mark (b i j))) := by
  have run := Space.BoundedTask.of_time (headerFromRight N q (fun i => List.ofFn (a i)) b hN)
  have volume i : size (List.ofFn (a i), List.ofFn fun j => Dusk.mark (b i j)) ≤
      (2*C+3)*((N i+1)*(k i+1)) := by
    have hx := streamSize _ (ha i)
    have hy := streamSize _ (hb i)
    rw [size_prod]
    ring_nf at hx hy ⊢
    omega
  apply run.bound (2*C+4) (4*C+7)
  · intro i
    have h := volume i
    ring_nf at h ⊢
    omega
  · intro i
    change size _ + size _ + 1 ≤ _
    have h := volume i
    ring_nf at h ⊢
    omega

end ProductPass

end NearSquareRoot
end Computability
end OAI
