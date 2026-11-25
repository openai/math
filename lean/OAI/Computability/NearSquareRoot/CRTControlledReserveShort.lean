import OAI.Computability.NearSquareRoot.CRTPositionShort
import OAI.Computability.NearSquareRoot.CRTPositionDescriptorEval
import OAI.Computability.NearSquareRoot.CRTControlledReserveShortTape
import OAI.Computability.IntegerMultiplication.Strip.Header
import OAI.Computability.NearSquareRoot.CRTControlledSizes

/-! # Canonical short matching factors

The first factor uses the first `⌈k/4⌉` lower endpoints in address order.
The second factor uses the remaining transpositions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveShort

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

variable {k : ℕ}

/-- Lower endpoints in increasing physical bit-position order. -/
def lowerList (p : Equiv.Perm (Fin k)) : List (Fin k) :=
  (List.finRange k).filter (fun j => decide (j < p j))

/-- Endpoints assigned to the first matching. -/
def firstEnds (p : Equiv.Perm (Fin k)) :=
  ((lowerList p).take ((k+3)/4)).toFinset

private theorem lowerList_toFinset (p : Equiv.Perm (Fin k)) : (lowerList p).toFinset = lowerEnds p := by
  ext j
  simp [lowerList, lowerEnds]

private theorem lowerList_nodup (p : Equiv.Perm (Fin k)) : (lowerList p).Nodup :=
  (List.nodup_finRange _).filter _

theorem firstEnds_subset (p : Equiv.Perm (Fin k)) : firstEnds p ⊆ lowerEnds p := by
  rw [← lowerList_toFinset]
  intro j h
  apply List.mem_toFinset.mpr
  exact List.mem_of_mem_take (List.mem_toFinset.mp h)

theorem firstEnds_card (p : Equiv.Perm (Fin k)) :
    (firstEnds p).card = min (lowerEnds p).card ((k+3)/4) := by
  rw [firstEnds, List.toFinset_card_of_nodup ((lowerList_nodup p).take), List.length_take,
    ← lowerList_toFinset, List.toFinset_card_of_nodup (lowerList_nodup p), min_comm]

def first (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) := portion p hp (firstEnds p)

def second (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) := portion p hp (firstEnds p)ᶜ

theorem short_bounds (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    (first p hp).trans (second p hp) = p ∧
      (∀ i, first p hp i = i ∨ second p hp i = i) ∧
      ∀ q ∈ [first p hp, second p hp], Function.Involutive q ∧
        (lowerEnds q).card ≤ (k+3)/4 ∧ k/2-2 ≤ (fixedPositions q).card :=
  short_portions p hp _ (firstEnds_subset p) (firstEnds_card p)

/-- Two ordered short factors for each of the two executable cycle reflections. -/
def four (p : Equiv.Perm (Fin k)) : List (Equiv.Perm (Fin k)) :=
  let a := Reflections.first p
  let b := Reflections.second p
  [first a (forwardMirror_involutive p), second a (forwardMirror_involutive p),
    first b (shiftedMirror_involutive p), second b (shiftedMirror_involutive p)]

theorem four_factor (p : Equiv.Perm (Fin k)) :
    (four p).foldr Equiv.trans (Equiv.refl _) = p := by
  let a := Reflections.first p
  let b := Reflections.second p
  have ha := (short_bounds a (forwardMirror_involutive p)).1
  have hb := (short_bounds b (shiftedMirror_involutive p)).1
  exact (congrArg₂ Equiv.trans ha hb).trans (Reflections.factor p)

theorem four_short (p q : Equiv.Perm (Fin k)) (hq : q ∈ four p) :
    Function.Involutive q ∧ (lowerEnds q).card ≤ (k+3)/4 ∧ k/2-2 ≤ (fixedPositions q).card := by
  let a := Reflections.first p
  let b := Reflections.second p
  have ha := (short_bounds a (forwardMirror_involutive p)).2.2
  have hb := (short_bounds b (shiftedMirror_involutive p)).2.2
  change q ∈ [first a _, second a _] ++ [first b _, second b _] at hq
  exact (List.mem_append.mp hq).elim (ha q) (hb q)

theorem split_table (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    split (Reflections.table p) = (Reflections.table (first p hp), Reflections.table (second p hp)) := by
  rw [split_value]
  apply Prod.ext <;> apply congrArg List.ofFn <;> funext j
  · simp only [first, portion_apply, firstEnds, lowerList, List.mem_toFinset]
    split_ifs <;> rfl
  · simp only [second, portion_apply, Finset.mem_compl, firstEnds, lowerList, List.mem_toFinset]
    split_ifs <;> rfl

/-- A uniform compiler from one physical permutation table to four short matching tables. -/
def fourTables (t : Reflections.Table) : List Reflections.Table :=
  let z := Reflections.prepare t
  let a := split z.1
  let b := split z.2
  [a.1, a.2, b.1, b.2]

@[fun_prop] theorem poly_fourTables : Poly fourTables := by
  unfold fourTables
  fun_prop

theorem fourTables_table (p : Equiv.Perm (Fin k)) :
    fourTables (Reflections.table p) = (four p).map Reflections.table := by
  simp only [fourTables, four, Reflections.prepare_spec, split_table (Reflections.first p) (forwardMirror_involutive p),
    split_table (Reflections.second p) (shiftedMirror_involutive p), List.map_cons, List.map_nil]

theorem split_uniform {X : Type*} (r : Regime X) {k : X → ℕ} (p : ∀ x, Equiv.Perm (Fin (k x)))
    (hp : ∀ x, Function.Involutive (p x)) (h : r.Has (fun x => Reflections.table (p x))) :
    r.Has (fun x => (Reflections.table (first (p x) (hp x)), Reflections.table (second (p x) (hp x)))) := by
  simpa only [fun x => split_table (p x) (hp x)] using h.thenDo poly_split

theorem fourTables_uniform {X : Type*} (r : Regime X) {k : X → ℕ} (p : ∀ x, Equiv.Perm (Fin (k x)))
    (h : r.Has (fun x => Reflections.table (p x))) :
    r.Has (fun x => (four (p x)).map Reflections.table) := by
  simpa only [fourTables_table] using h.thenDo poly_fourTables

/-- Reading a unary permutation descriptor and emitting all four descriptors costs polynomial
time in the number of bit positions. -/
theorem fourTables_task {X : Type} (k : X → ℕ) (p : ∀ x, Equiv.Perm (Fin (k x))) :
    Task.BT k (fun x => send (Reflections.table (p x)))
      (fun x => send ((four (p x)).map Reflections.table)) := by
  have task := poly_fourTables.on (q := fun x => Reflections.table (p x)) (p := k)
    (show Dom k (fun x => size (Reflections.table (p x))) from ⟨2, 2, fun x => Reflections.table_size (p x)⟩)
  simpa only [fourTables_table] using task

open Filter

/-- The low and high bit reservations for any fixed polynomial degrees fit
simultaneously among the fixed positions of every short factor. -/
theorem eventually_two_reserves (a b : ℕ) :
    ∀ᶠ k : ℕ in atTop, payloadBits a k + payloadBits b k ≤ k/2 - 2 := by
  filter_upwards [eventually_batch_reserves 0 a b, eventually_ge_atTop (8 : ℕ)] with k h hk
  have h' : payloadBits a k + payloadBits b k ≤ k/4 := by simpa using h.2
  omega

theorem eventually_four_reserves (a b : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ p : Equiv.Perm (Fin k), ∀ q ∈ four p,
      payloadBits a k + payloadBits b k ≤ (fixedPositions q).card := by
  filter_upwards [eventually_two_reserves a b] with k h p q hq
  exact h.trans (four_short p q hq).2.2

end Controlled.ReserveShort

end NearSquareRoot
end Computability
end OAI
