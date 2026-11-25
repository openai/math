import OAI.Computability.NearSquareRoot.SynchronizedLowerProgram

/-! # Generating the fifteen borrowed-fiber batches for every axis of a block

An instruction records its axis, batch and underlying fixed-bit circuit opcode.
The order of the generated instructions is the matrix multiplication order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code AxisWord

abbrev Descriptor := Tally × Tally × Inst

/-- The mathematically indexed word, also recording exactly which copy is executed. -/
def typed {m : ℕ} (k : Fin m → ℕ) : List (Fin m × Fin 15 × Inst) :=
  (List.finRange m).flatMap fun i => (List.finRange 15).flatMap fun j =>
    (fixedWord (tally (k i))).map fun x => (i,j,x)

def encode {m : ℕ} (p : Fin m × Fin 15 × Inst) : Descriptor :=
  (tally p.1.val, tally p.2.1.val, p.2.2)

private def oneBatch (z : (Tally × Tally) × Tally) : List Descriptor :=
  (fixedWord z.1.2).map fun x => (z.1.1, z.2, x)

private def oneAxis (p : Tally × Tally) : List Descriptor :=
  (Iter.lineup (tally 15)).flatMap fun j => oneBatch (p,j)

def block (k : List Tally) : List Descriptor :=
  (Iter.lineup (ruler k)).flatMap fun i => oneAxis (i, Iter.pick [] (k,i))

private theorem oneBatch_poly : Poly oneBatch := by
  let addFields (p : (Tally × Tally) × Inst) : Descriptor := (p.1.1, p.1.2, p.2)
  have h : Poly addFields := Easy.fst.poly.fstCompose.pair (Easy.fst.poly.sndCompose.pair Easy.snd.poly)
  let prep (z : (Tally × Tally) × Tally) := ((z.1.1, z.2),fixedWord z.1.2)
  have hprep : Poly prep := ((Easy.fst.poly.fstCompose).pair Easy.snd.poly).pair
    (Easy.fst.poly.sndCompose.compose fixedWord_poly)
  change Poly (fun z => polyPush addFields (prep z))
  exact hprep.compose (Poly.push ([],[]) (inst 0) h)

private theorem oneAxis_poly : Poly oneAxis :=
  ((Code.Poly.identity.pair (Code.Poly.const (Iter.lineup (tally 15)))).compose
    (Poly.push ([],[]) [] oneBatch_poly)).compose Easy.flatten.poly

/-- The bounded stack implementation constructs every axis number and batch number. -/
theorem block_poly : Poly block := by
  have h := (Easy.snd (X := List Tally) (Y := Tally)).poly.pair (Iter.facile ([] : Tally)).poly
  exact ((Code.Poly.identity.pair ((Easy.ruler Easy.identity).poly.compose Iter.poly_line)).compose
    (Poly.push ([] : List Tally) ([] : Tally) (h.compose oneAxis_poly))).compose Easy.flatten.poly

theorem block_machine : PolyTreeMachine size send (fun k => send (block k)) :=
  polyTreeMachine_of_BT (block_poly.on (Dom.base _)) (Dom.base _)

/-- The output tape describes every opcode in every mathematical batch in order. -/
theorem block_eq_typed {m : ℕ} (k : Fin m → ℕ) :
    block (List.ofFn (fun i => tally (k i))) = (typed k).map encode := by
  let ks := List.ofFn (fun i => tally (k i))
  have hsize : (ruler ks).length = m := by simp [ks]
  have hline : Iter.lineup (ruler ks) = (List.finRange m).map (fun i => tally i.val) := by
    rw [← recover_tally (ruler ks), hsize, Iter.lined, List.ofFn_eq_map]
  have h15 : Iter.lineup (tally 15) = (List.finRange 15).map (fun i => tally i.val) := by
    rw [Iter.lined, List.ofFn_eq_map]
  have he (i : Fin m) : Iter.pick ([] : Tally) (ks,tally i.val) = tally (k i) := by
    have hi : i.val < ks.length := by simp [ks]
    rw [Iter.search _ _ _ hi]
    simp [ks]
  change block ks = _
  simp only [block, hline, oneAxis, h15, oneBatch, typed, List.flatMap_map, List.map_flatMap,
    Function.comp_def, List.map_map, encode, he]

private theorem flatMap_bound {A B : Type*} (w : List A) (f : A → List B) (C : ℕ)
    (hf : ∀ i ∈ w, (f i).length ≤ C) : (w.flatMap f).length ≤ w.length * C := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add
      (hf x List.mem_cons_self) (ih (fun i hi => hf i (List.mem_cons_of_mem _ hi)))

/-- Each operation has an axis and a batch tag. The fifteen tags per axis do
not increase the logarithmic dependence on the radix length. -/
theorem typed_length_le {m : ℕ} (k : Fin m → ℕ) {L : ℕ} (hk : ∀ i, k i ≤ L) :
    (typed k).length ≤ m * (15 * (18 * (1032 * L + 1549))) := by
  let C := 18 * (1032 * L + 1549)
  have hb (i : Fin m) : (fixedWord (tally (k i))).length ≤ C := by
    apply (fixedWord_length_le _).trans
    simp only [tally_length, C]
    gcongr
    exact hk i
  unfold typed
  have h := flatMap_bound (List.finRange m) (fun i => (List.finRange 15).flatMap
    (fun j => (fixedWord (tally (k i))).map (fun x => (i,j,x)))) (15 * C) (by
    intro i _
    simpa using flatMap_bound (List.finRange 15) (fun j => (fixedWord (tally (k i))).map
      (fun x => (i,j,x))) C (fun _ _ => by simpa using hb i))
  simpa using h

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
