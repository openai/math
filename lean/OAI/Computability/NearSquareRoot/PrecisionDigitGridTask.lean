import OAI.Computability.NearSquareRoot.PrecisionDigitEncoding
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Match

/-! # Loading variable-width radix digits into uniform complex records

The fraction and component rulers are manufactured once from the address
width. The list ruler then controls copying this header for each physical slot;
a final lockstep scan shifts and resizes each digit and writes both components.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open NearSquareRoot.FixedPoint IntegerMultiplication.Brief

private def affineRuler (a c : ℕ) (t : Tally) : Tally :=
  (t.map fun _ => tally a).flatten ++ tally c

private theorem affine_easy (a c : ℕ) : Easy (affineRuler a c) := by
  unfold affineRuler
  fun_prop

private theorem affine_tally (a c k : ℕ) :
    affineRuler a c (tally k) = tally (a*k+c) := by
  simp [affineRuler, tally, List.flatten_replicate_replicate, Nat.mul_comm]

private def rulers (k : ℕ) := (tally (fractionBits k), tally (componentBits k+1))

private theorem prepare_rulers :
    Easy (fun t : Tally => (affineRuler 70 1 t, affineRuler 96 5 t)) :=
  (affine_easy ..).pair (affine_easy ..)

private theorem lock_const (xs : List Word) (r : Tally × Tally) :
    lock encodeDigit [] ([], []) (xs, List.replicate xs.length r) =
      xs.map (fun x => encodeDigit (x, r)) := by
  have h := fair id (fun _ : Word => r) xs ([] : Word) (([],[]) : Tally × Tally)
  simpa [lock, List.map_map, Function.comp_def] using congrArg (List.map encodeDigit) h

/-- The `N` copies of the two precision rulers and all numerical bit records
fit the linear budget. The inputs are the actual measured address width and the
boxed little-endian digits, both carried from the same query. -/
theorem encode_grid_rows {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (p : I → Tree) (xs : I → List Word)
    (run : Carries (measure n) p (send ∘ xs))
    (kRun : Carries (measure n) p (fun i => send (tally (addressBits (n i)))))
    (hlen : ∀ i, (xs i).length = capacity (n i)) :
    Carries (measure n) p (fun i => send ((xs i).map (fun w =>
      encodeDigit (w, tally (fractionBits (addressBits (n i))),
        tally (componentBits (addressBits (n i))+1))))) := by
  let k := addressBits ∘ n
  have header : Carries (measure n) p (fun i => send (rulers (k i))) := by
    have h := Carries.func (y := fun i=> tally (k i)) (here n) kRun.out _ prepare_rulers
    simpa only [affine_tally, rulers, componentBits, fractionBits, Nat.add_assoc] using kRun.chain h
  have count := run.chain (Carries.func (y := xs) (here n) run.out ruler (Easy.ruler Easy.identity))
  let args (i : I) := (ruler (xs i), rulers (k i))
  have gen := (Code.generate (X := Tally × Tally)).on args
  have copies : Carries (measure n) p (fun i => send (List.replicate (xs i).length (rulers (k i)))) := by
    apply (count.twice header).sequence
    simp only [args, ruler_length] at gen
    refine ⟨here n,_,gen,20000,fun i => ?_⟩
    rw [size_prod]
    simp only [rulers,size_tally,tally_length,componentBits,fractionBits,hlen]
    unfold Brief.measure
    norm_cast
    have vol := (packed_volume (hn i)).2
    have cap := (capacity_bounds (hn i)).2.le
    have nc := count_le (hn i)
    have kb := addressBits_le (hn i)
    have ww := width_le (n i)
    dsimp only [k, Function.comp_apply]
    nlinarith only [vol,cap,nc,kb,ww]
  have together := run.twice copies
  let packet (i : I) := (xs i, List.replicate (xs i).length (rulers (k i)))
  have finish := together.chain (Carries.func (y := packet) (here n) together.out _
    (easy_lock encodeDigit encodeDigit_easy [] ([],[])))
  simpa only [packet, lock_const, rulers, k, Function.comp_apply] using finish

/-- Read one MSF operand and write all initialized complex records, including
the canonical representation of zero in every padding slot. -/
theorem encoded_scan {I : Type} (x : I → Word) (hx : ∀ i, 2 ≤ (x i).length)
    (hv : ∀ i, ValidShape (x i).length) :
    Carries (measure (fun i => (x i).length)) (send ∘ x) (send ∘ encodedBoxed ∘ x) := by
  let n (i : I) := (x i).length
  exact encode_grid_rows n hx _ (boxed ∘ x) (boxed_scan x hx hv)
    ((lit x (fun _ => rfl)).chain (header_addressBits n hx)) (fun i => by
      dsimp only [Function.comp_apply, boxed]
      rw [BoxMaskedRecords.length_expand]
      exact BoxOrder.length_shape (hv i))

/-- Parse and initialize both operands of the same length on the stack. -/
theorem encoded_pair_scan {I : Type} (p : I → Interface.Pair)
    (hw : ∀ i, (p i).2.length = (p i).1.length)
    (hn : ∀ i, 2 ≤ (p i).1.length) (hv : ∀ i, ValidShape (p i).1.length) :
    Carries (measure (fun i => (p i).1.length)) (send ∘ p)
      (fun i => send (encodedBoxed (p i).1, encodedBoxed (p i).2)) := by
  have u := encoded_scan (fun i => (p i).1) hn hv
  have v := encoded_scan (fun i => (p i).2) (fun i => hw i ▸ hn i) (fun i => hw i ▸ hv i)
  simp only [hw] at v
  exact (u.first v.small).chain (v.second u.out)

/-- A single finite-tape machine initializes both complex arrays, in linear
time and with a linear bound on all visited tape cells. -/
theorem encoded_pair_machine : ∃ N : ℕ,
    let Input := {p : Interface.Pair // p.1.length = p.2.length ∧ N ≤ p.1.length}
    PairToTree (fun p : Input => p.val) (fun p => send (encodedBoxed p.val.1,encodedBoxed p.val.2))
      (fun p => p.val.1.length) := by
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp eventually_validShape
  let N := max 2 M
  let Input := {p : Interface.Pair // p.1.length = p.2.length ∧ N ≤ p.1.length}
  have big (p : Input) : 2 ≤ p.val.1.length := (le_max_left 2 M).trans p.property.2
  have val (p : Input) : ValidShape p.val.1.length := hM _ ((le_max_right 2 M).trans p.property.2)
  have hw (p : Input) : p.val.2.length = p.val.1.length := p.property.1.symm
  exact ⟨N,release_pair_scan (fun p : Input => p.val) _ _ (fun _=>rfl) hw
    (encoded_pair_scan _ hw big val)⟩

end DigitPacking

end NearSquareRoot
end Computability
end OAI
