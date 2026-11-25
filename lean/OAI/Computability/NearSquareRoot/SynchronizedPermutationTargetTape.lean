import OAI.Computability.NearSquareRoot.SynchronizedPermutationTarget
import OAI.Computability.NearSquareRoot.SynchronizedPlacedPermutationTape
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Generation of the physical source coordinates for both permutation opcodes

The unary extent supplied by the placement header pays for conversion of the
permuted binary word to a unary rank. Reversal and stage-bit exchange use the
same most-significant-first word convention as the local matrix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication Code Bits Carry Strip Staff RadixAddressTape SynchronizedBorrowing

variable {J : Type} {s : Regime J}

private theorem classifiedEq {n : J → ℕ} (N : Realizes s n) (c : ℕ) :
    Classified s (fun j => n j = c) := by
  have z := (Regime.Has.pair (g := fun j => tally (n j)) N
    (Regime.fixed (r := s) (tally c))).ez (Iter.linked (X := Unit) (Y := Unit))
  exact ⟨_, by simpa only [tally_length] using z, fun _ => by simp⟩

private theorem wordValue {w : J → Word} (W : s.Has w) {budget : J → ℕ}
    (B : Realizes s budget) (h : ∀ j, value (w j) ≤ budget j) :
    Realizes s (fun j => value (w j)) :=
  (show Figure s (fun j => value (w j)) from ⟨w,W,fun _ => rfl⟩).pay ((diameter _ B).mono h)

private theorem halfLength (flag : Bool) (i : Tally) (w : Word) :
    (halfReply (flag,i,w)).2.length ≤ w.length + 1 := by
  simp only [halfReply, cutLists, List.length_append, List.length_take, List.length_cons,
    List.length_tail, List.length_drop]
  omega

/-- Evaluate either opcode on arbitrary numerical inputs. The padding extent is
already available in unary, while the reversal and swap work on binary words. -/
theorem permutationTarget_realizes {k tag arg t : J → ℕ}
    (K : Realizes s k) (R : Realizes s (fun j => 2 ^ k j))
    (Tag : Realizes s tag) (Arg : Realizes s arg) (T : Realizes s t) :
    Realizes s (fun j => permutationTarget (k j) (tag j) (arg j) (t j)) := by
  let w := fun j => (short (k j) (t j)).reverse
  have W : s.Has w := ((Figure.of_spoken T).write K).ez Easy.reverse
  have low := wordValue W R (fun j => by simpa [w, short_length] using (value_lt (w j)).le)
  have smaller := (Regime.Has.pair (g := fun j => tally (t j)) (f := fun j => tally (2^k j)) T R).ez
    ((Iter.small_easy (X := Unit) (Y := Unit)).compose Iter.negate)
  have selector : s.Has (fun j => decide (2 ^ k j ≤ t j)) := by
    convert smaller using 1
    funext j
    by_cases h : t j < 2 ^ k j <;> simp [Iter.small, h, Nat.not_le.mpr, Nat.le_of_not_gt]
  let z := fun j => halfReply (decide (2 ^ k j ≤ t j), tally (arg j), w j)
  have Z : s.Has z := (selector.pair (Regime.Has.pair (g := fun j => tally (arg j)) Arg W)).ez easy_halfReply
  have zdigits : s.Has (fun j => (z j).2.reverse) := (Z.ez Easy.snd).ez Easy.reverse
  have number := wordValue zdigits (R.plus R) (fun j => by
    have h := halfLength (decide (2 ^ k j ≤ t j)) (tally (arg j)) (w j)
    have len : (z j).2.reverse.length ≤ k j + 1 := by simpa [z, w, short_length] using h
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) len
    calc
      _ ≤ 2^(z j).2.reverse.length := (value_lt _).le
      _ ≤ 2^(k j + 1) := hpow
      _ = _ := by simp [pow_succ, Nat.mul_two])
  have half := R.select (Realizes.fix 0) (Classified.learn _ (Z.ez Easy.fst))
  have routed := (half.plus number).select T (Arg.below K)
  have result := (low.select T (T.below R)).select (routed.select T (classifiedEq Tag 18))
    (classifiedEq Tag 0)
  convert result using 1
  funext j
  by_cases h₀ : tag j = 0 <;> by_cases h₁ : tag j = 18 <;>
    by_cases h₂ : arg j < k j <;> by_cases h₃ : t j < 2 ^ k j <;>
    simp [permutationTarget, z, w, short, h₀, h₁, h₂, h₃, Nat.mod_eq_of_lt]
  rfl

theorem placedOpcode_has {start v a k tag arg row col : J → ℕ}
    (S : Realizes s start) (V : Realizes s v) (A : Realizes s a) (K : Realizes s k)
    (R : Realizes s (fun j => 2^k j)) (Tag : Realizes s tag) (Arg : Realizes s arg)
    (Row : Realizes s row) (Col : Realizes s col) :
    s.Has (fun j => PlacedPermutationTape.coordinates (placedPermTarget
      (start j) (v j) (a j) (2^k j) (permutationTarget (k j) (tag j) (arg j)) (row j) (col j))) :=
  PlacedPermutationTape.placedPermTarget_has S V A R Row Col (fun _ =>
    permutationTarget_realizes K R Tag Arg)

/-- Raw fields in order are width, tag, argument, the four placement parameters,
then physical row and column. The machine consumes the full encoded header. -/
abbrev OpcodeQuery := PlacedPermutationTape.Query (Tally × Tally × Tally)

abbrev ValidOpcodeQuery := {q : OpcodeQuery // q.2.1.2.2.length = 2 ^ q.1.1.length}

def opcodeReply (q : OpcodeQuery) : Tally × Tally :=
  PlacedPermutationTape.reply
    (fun h : Tally × Tally × Tally => permutationTarget h.1.length h.2.1.length h.2.2.length) q

/-- Serialize a physical matrix row in the packet accepted by the tape program. -/
def sourceQuery {a b c : ℕ} (k tag arg : ℕ) (batch : Fin 15) (p : Fin b × (Fin a ⊕ Fin c)) :
    ValidOpcodeQuery :=
  ⟨((tally k,tally tag,tally arg),
      ((tally (first b batch),tally (SynchronizedBorrowing.size b batch)),(tally a,tally (2^k))),
      tally (cellCoordinates p).1, tally (cellCoordinates p).2), by simp⟩

/-- The output packet spells the source used by the placed permutation matrix,
including fixed points in scratch and padded columns. -/
theorem opcodeReply_source {a b c k : ℕ} (ha : 0 < a) (har : a ≤ 2^k)
    (hr : 2*2^k ≤ 8*a) (batch : Fin 15) (tag arg : ℕ) (p : Fin b × (Fin a ⊕ Fin c)) :
    opcodeReply (sourceQuery k tag arg batch p).val =
      PlacedPermutationTape.coordinates (cellCoordinates (placedPermutation hr batch
        (borrowedPermutation har (opcodePermutation k tag arg)) p)) := by
  rw [placedOpcode_coordinates ha har hr]
  simp [opcodeReply, sourceQuery, PlacedPermutationTape.reply]

private def opcodeRegime : Regime ValidOpcodeQuery :=
  ⟨fun q => Code.size q.val, fun q => send q.val, Dom.base _⟩

private theorem opcodeField (f : OpcodeQuery → Tally) (hf : Easy f) :
    Realizes opcodeRegime (fun q => (f q.val).length) := by
  have q : opcodeRegime.Has (fun q => q.val) := opcodeRegime.self
  simpa only [Realizes, Function.comp_def, recover_tally] using q.ez hf

/-- One finite deterministic multitape program evaluates every placed
permutation query, including the inverse-direction opcodes. The time and the
number of visited cells are polynomial in the size of the encoded raw fields. -/
theorem placedOpcode_machine :
    PolyTreeMachine (fun q : ValidOpcodeQuery => Code.size q.val)
      (fun q => send q.val) (fun q => send (opcodeReply q.val)) := by
  apply polyTreeMachine_of_BT _ (Dom.base _)
  have extent (q : ValidOpcodeQuery) : q.val.2.1.2.2.length = 2 ^ q.val.1.1.length := q.property
  have radius : Realizes opcodeRegime (fun q => 2 ^ q.val.1.1.length) := by
    simpa only [extent] using
      opcodeField (fun q => q.2.1.2.2) (by fun_prop)
  have h := placedOpcode_has (s := opcodeRegime)
    (opcodeField (fun q => q.2.1.1.1) (by fun_prop))
    (opcodeField (fun q => q.2.1.1.2) (by fun_prop))
    (opcodeField (fun q => q.2.1.2.1) (by fun_prop))
    (opcodeField (fun q => q.1.1) (by fun_prop)) radius
    (opcodeField (fun q => q.1.2.1) (by fun_prop))
    (opcodeField (fun q => q.1.2.2) (by fun_prop))
    (opcodeField (fun q => q.2.2.1) (by fun_prop))
    (opcodeField (fun q => q.2.2.2) (by fun_prop))
  change opcodeRegime.Has (fun q => opcodeReply q.val)
  simpa only [opcodeReply, PlacedPermutationTape.reply, extent] using h

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
