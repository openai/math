import OAI.Computability.NearSquareRoot.SynchronizedAxisWord
import OAI.Computability.NearSquareRoot.PhaseProgramRelease

/-! # Generating the short-axis circuit on fixed tapes

The input is a unary radix exponent. The fixed stack program constructs the
actual instruction word, including each adjoint and all 64 repetitions. The
released finite-tape machine writes the whole encoded instruction stream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

open IntegerMultiplication IntegerMultiplication.Code

private theorem flip_poly : Poly flip := by
  unfold flip
  exact Easy.fst.poly.pair (Easy.snd.poly.fstCompose.pair (Easy.snd.poly.sndCompose.compose Iter.negate.poly))

private theorem adj_poly : Poly adj :=
  Easy.reverse.poly.compose (Poly.maps _ flip_poly)

private theorem radix_poly : Poly radix := by
  have h₁ (tag : ℕ) : Poly (fun i : Tally => inst tag i) := by unfold inst; fun_prop
  have h₂ : Poly (fun i : Tally => [inst 1 i, inst 2 i]) := by
    exact ((h₁ 1).pair (((h₁ 2).pair (Code.Poly.const [])).compose Poly.cons)).compose Poly.cons
  have h := (Iter.poly_line.rev.compose (Poly.maps _ h₂)).compose Easy.flatten.poly
  unfold radix
  simp_rw [List.flatMap_def]
  exact ((Code.Poly.const _).pair h).compose Poly.cons

private theorem dilate_poly : Poly dilate := by
  unfold dilate
  exact (((((Code.Poly.const _).app (radix_poly.compose adj_poly)).app (Code.Poly.const _)).app radix_poly).app
    (Code.Poly.const _))

private theorem reflections_poly : Poly reflections := by
  unfold reflections
  exact ((dilate_poly.app (Code.Poly.const _)).app (dilate_poly.compose adj_poly)).app (Code.Poly.const _)

private theorem repeat_poly (n : ℕ) : Poly (fun w : List Inst => (List.replicate n w).flatten) := by
  induction n with
  | zero => simpa using (Code.Poly.const ([] : List Inst) (X := List Inst))
  | succ n ih =>
    simpa [List.replicate_succ] using Poly.identity.app ih

private theorem amplify_poly : Poly amplify := by
  unfold amplify
  exact (reflections_poly.compose (repeat_poly 64)).app dilate_poly

/-- One physical stack program generates the exact restored instruction list. -/
theorem restored_poly : Poly restored := by
  unfold restored
  exact ((((Code.Poly.const _).app (amplify_poly.compose adj_poly)).app (Code.Poly.const _)).app amplify_poly).app
    (Code.Poly.const _)

private theorem tally_size_dom : Dom id (fun k : ℕ => size (tally k)) :=
  ⟨1, 2, fun k => by simp [size_tally]⟩

/-- Polynomial time in the radix exponent, on the stack spelling of the unary input. -/
theorem restored_task : Task.BT id (fun k : ℕ => send (tally k)) (fun k => send (restored (tally k))) :=
  restored_poly.on tally_size_dom

/-- A single fixed finite-tape machine outputs the complete instruction list.
Its entire trace and the set of visited cells have polynomial size in the unary exponent. -/
theorem restored_machine :
    PolyTreeMachine id (fun k : ℕ => send (tally k)) (fun k => send (restored (tally k))) :=
  polyTreeMachine_of_BT restored_task tally_size_dom

private theorem repeat_length (n : ℕ) (w : List Inst) :
    (List.replicate n w).flatten.length = n * w.length := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, Nat.succ_mul, ih, Nat.add_comm]

/-- Exact number of instructions, counting the adjoints and both reflection words. -/
theorem restored_length (k : Tally) : (restored k).length = 1032 * k.length + 1549 := by
  have hr : (radix k).length = 1 + 2 * k.length := by
    simp [radix, List.length_flatMap, Nat.mul_comm, List.sum_replicate]
    omega
  simp only [restored, amplify, reflections, dilate, adj, List.length_append, List.length_map,
    List.length_reverse, List.length_cons, List.length_nil, repeat_length, hr]
  omega

private def FieldsBounded (k : ℕ) (w : List Inst) : Prop :=
  ∀ i ∈ w, i.1.length ≤ 9 ∧ i.2.1.length ≤ k

private theorem FieldsBounded.append {k : ℕ} {w v : List Inst} (hw : FieldsBounded k w)
    (hv : FieldsBounded k v) : FieldsBounded k (w ++ v) :=
  fun i hi => (List.mem_append.mp hi).elim (hw i) (hv i)

private theorem FieldsBounded.adj {k : ℕ} {w : List Inst} (hw : FieldsBounded k w) :
    FieldsBounded k (AxisWord.adj w) := by
  intro i hi
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
  exact hw x (List.mem_reverse.mp hx)

private theorem FieldsBounded.repeat {k : ℕ} {w : List Inst} (hw : FieldsBounded k w)
    (n : ℕ) : FieldsBounded k (List.replicate n w).flatten := by
  intro i hi
  obtain ⟨v, hv, hi⟩ := List.mem_flatten.mp hi
  exact hw i ((List.eq_of_mem_replicate hv) ▸ hi)

private theorem bounded_const (k tag : ℕ) (ht : tag ≤ 9) : FieldsBounded k [inst tag] := by
  intro i hi
  obtain rfl := List.mem_singleton.mp hi
  simp [inst, ht]

private theorem bounded_radix (k : Tally) : FieldsBounded k.length (radix k) := by
  intro i hi
  rw [radix, List.mem_cons] at hi
  rcases hi with rfl | hi
  · simp [inst]
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp ht)
  have hp := p.isLt.le
  rcases List.mem_cons.mp hi with rfl | hi
  · simp [inst, hp]
  · obtain rfl := List.mem_singleton.mp hi
    simp [inst, hp]

private theorem bounded_restored (k : Tally) : FieldsBounded k.length (restored k) := by
  have r := bounded_radix k
  have d : FieldsBounded k.length (dilate k) :=
    ((((bounded_const _ _ (by decide)).append r.adj).append (bounded_const _ _ (by decide))).append r).append
      (bounded_const _ _ (by decide))
  have v : FieldsBounded k.length (reflections k) :=
    ((d.append (bounded_const _ _ (by decide))).append d.adj).append (bounded_const _ _ (by decide))
  have b : FieldsBounded k.length (amplify k) := (v.repeat 64).append d
  exact ((((bounded_const _ _ (by decide)).append b.adj).append (bounded_const _ _ (by decide))).append b).append
    (bounded_const _ _ (by decide))

/-- Every emitted opcode is one of the ten local instructions, and its unary argument
is at most the supplied radix exponent. -/
theorem restored_fieldsBounded (k : Tally) (x : Inst) (hx : x ∈ restored k) :
    x.1.length ≤ 9 ∧ x.2.1.length ≤ k.length :=
  bounded_restored k x hx

private theorem bounded_size {k : ℕ} (w : List Inst) (hw : FieldsBounded k w) :
    size w ≤ w.length * (2*k + 24) + 1 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    obtain ⟨htag, harg⟩ := hw x (by simp)
    have htail := ih fun i hi => hw i (List.mem_cons_of_mem _ hi)
    simp only [size_cons, size_prod, size_tally, size_bit, List.length_cons, Nat.succ_mul]
    nlinarith [htail]

/-- A concrete bound on every encoded output symbol. The constant 24 includes both
unary terminators, the adjoint bit, and the instruction and list constructors. -/
theorem restored_size (k : Tally) :
    size (restored k) ≤ (1032 * k.length + 1549) * (2 * k.length + 24) + 1 := by
  simpa only [restored_length] using bounded_size _ (bounded_restored k)

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
