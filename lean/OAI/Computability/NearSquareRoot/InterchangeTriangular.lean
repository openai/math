import OAI.Computability.IntegerMultiplication.Port.Lag

/-!
# Descending-row implementation of a triangular address change

A row first scales its diagonal field and then adds rational multiples of
earlier fields. Executing the rows in descending address order preserves the
source values needed by every row. The resulting list consists entirely of
legal P192 scaling and controlled-shift instructions, uniformly in the digit
width, and has zero recursive interchange calls.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeTriangular

open IntegerMultiplication IntegerMultiplication.Port

noncomputable section

variable {J : Type} [DecidableEq J] {d p : ℕ}
variable (slot : Fin d → Spot J) (diag : Fin d → Span p)
    (sub : Fin d → Fin d → Pinpoint p)

private def before (i : Fin d) : List (Fin d) := (Finset.Iio i).toList

private def gathers (i : Fin d) (cols : List (Fin d)) : List (Lag J p) :=
  cols.map fun k => Lag.gather (slot i) (slot k) (sub i k)

private def row (i : Fin d) : List (Lag J p) :=
  Lag.width (slot i) (diag i) :: gathers slot sub i (before i)

private def rows : ℕ → List (Lag J p)
  | 0 => []
  | k+1 => if hk : k < d then row slot diag sub ⟨k,hk⟩ ++ rows k else rows k

/-- A coordinate of the required lower triangular matrix applied to the
original vector of field addresses in the prime-power residue ring. -/
def rowValue (f : ℕ) (x : Duplex J (Tower p f)) (i : Fin d) : Tower p f :=
  (diag i).land f * hear x (slot i) +
    ∑ k ∈ Finset.Iio i, (sub i k).stamp f * hear x (slot k)

private theorem gather_effect (hs : Function.Injective slot) (f : ℕ)
    (x : Duplex J (Tower p f)) (i : Fin d) (cols : List (Fin d)) (hi : i ∉ cols)
    (a : Spot J) :
    hear ((gathers slot sub i cols).foldl (Lag.fire f) x) a =
      if a = slot i then hear x (slot i) +
        (cols.map fun k => (sub i k).stamp f * hear x (slot k)).sum else hear x a := by
  induction cols generalizing x with
  | nil => by_cases e : a = slot i <;> simp [gathers,e]
  | cons k ks ih =>
    simp only [List.mem_cons,not_or] at hi
    simp only [gathers,List.map_cons,List.foldl_cons]
    rw [← gathers, ih _ hi.2]
    have hp (j : Fin d) (hj : j ∈ ks) : slot j ≠ slot i :=
      hs.ne (fun he => hi.2 (he ▸ hj))
    have hm : ks.map (fun j => (sub i j).stamp f *
        hear (Lag.fire f x (.gather (slot i) (slot k) (sub i k))) (slot j)) =
        ks.map (fun j => (sub i j).stamp f * hear x (slot j)) := by
      apply List.map_congr_left
      intro j hj
      simp [Lag.fire, hp j hj]
    rw [hm]
    by_cases ha : a = slot i
    · simp [ha, Lag.fire, add_assoc]
    · simp [ha, Lag.fire]

private theorem row_effect (hs : Function.Injective slot) (f : ℕ)
    (x : Duplex J (Tower p f)) (i : Fin d) (a : Spot J) :
    hear ((row slot diag sub i).foldl (Lag.fire f) x) a =
      if a = slot i then rowValue slot diag sub f x i else hear x a := by
  simp only [row, List.foldl_cons]
  rw [gather_effect slot sub hs _ _ _ _ (by simp [before])]
  by_cases ha : a = slot i
  · simp only [ha, ite_true, rowValue, Lag.fire, placed, before]
    rw [Finset.sum_map_toList]
    apply congrArg (fun z => (diag i).land f * hear x (slot i) + z)
    apply Finset.sum_congr rfl
    intro k hk
    have hki := hs.ne (Finset.mem_Iio.mp hk).ne
    simp [hki]
  · simp [ha,Lag.fire]

private theorem rows_effect (hs : Function.Injective slot) (f k : ℕ)
    (x : Duplex J (Tower p f)) :
    let y := (rows slot diag sub k).foldl (Lag.fire f) x
    (∀ i : Fin d, i.val < k → hear y (slot i) = rowValue slot diag sub f x i) ∧
    (∀ a : Spot J, (∀ i : Fin d, i.val < k → a ≠ slot i) → hear y a = hear x a) := by
  induction k generalizing x with
  | zero => simp [rows]
  | succ k ih =>
    by_cases hk : k < d
    · let j : Fin d := ⟨k,hk⟩
      let z := (row slot diag sub j).foldl (Lag.fire f) x
      have hrow (a : Spot J) : hear z a =
          if a = slot j then rowValue slot diag sub f x j else hear x a :=
        row_effect slot diag sub hs f x j a
      simp only [rows, dite_eq_left hk, List.foldl_append]
      change (∀ i : Fin d, i.val < k+1 → _ = _) ∧ _
      obtain ⟨before', outside⟩ := ih z
      constructor
      · intro i hi
        by_cases hit : i.val = k
        · have hij : i = j := Fin.ext hit
          subst i
          rw [outside (slot j) (fun i hi' => hs.ne (by intro e; subst i; change k < k at hi'; omega))]
          exact (hrow (slot j)).trans (ite_eq_left rfl)
        have hlt : i.val < k := by omega
        rw [before' i hlt]
        have hne {l : Fin d} (h : l ≤ i) : slot l ≠ slot j :=
          hs.ne (fun he => by have h' : l.val ≤ i.val := h; subst l; change k ≤ i.val at h'; omega)
        simp only [rowValue, hrow, hne (le_refl i), ite_false]
        apply congrArg (fun z => (diag i).land f * hear x (slot i) + z)
        apply Finset.sum_congr rfl
        intro l hl
        rw [ite_eq_right (hne (Finset.mem_Iio.mp hl).le)]
      · intro a ha
        rw [outside a (fun i hi => ha i (by omega))]
        exact (hrow a).trans (ite_eq_right (ha j (by change k < k+1; omega)))
    · simp only [rows, dite_eq_right hk]
      obtain ⟨h1,h2⟩ := ih x
      exact ⟨fun i _ => h1 i (by have := i.isLt; omega),
        fun a ha => h2 a (fun i hi => ha i (by omega))⟩

/-- A single finite list for all field widths. `order` is the physical order
of the P192 two-wing layout; any ordered subset of its fields may participate. -/
theorem compile (r : J → ℕ) (hs : Function.Injective slot)
    (order : ∀ i j, i < j → Lag.early r (slot i) (slot j)) :
    ∃ program : List (Lag J p), (∀ a ∈ program, a.legal r ∧ a.prices = 0) ∧
      ∀ f (x : Duplex J (Tower p f)),
        let y := program.foldl (Lag.fire f) x
        (∀ i, hear y (slot i) = rowValue slot diag sub f x i) ∧
        (∀ a, (∀ i, a ≠ slot i) → hear y a = hear x a) := by
  refine ⟨rows slot diag sub d, ?_, ?_⟩
  · suffices ∀ k a, a ∈ rows slot diag sub k → a.legal r ∧ a.prices = 0 from this d
    intro k
    induction k with
    | zero => simp [rows]
    | succ k ih =>
      intro a ha
      rw [rows] at ha
      split_ifs at ha with hk
      · rcases List.mem_append.mp ha with ha|ha
        · rcases List.mem_cons.mp ha with rfl|hm
          · exact ⟨trivial,rfl⟩
          · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hm
            exact ⟨order _ _ (by simpa [before] using hj), rfl⟩
        · exact ih a ha
      · exact ih a ha
  · intro f x
    obtain ⟨h₁,h₂⟩ := rows_effect slot diag sub hs f d x
    exact ⟨fun i => h₁ i i.isLt, fun a h => h₂ a (fun i _ => h i)⟩

end
end InterchangeTriangular

end NearSquareRoot
end Computability
end OAI
