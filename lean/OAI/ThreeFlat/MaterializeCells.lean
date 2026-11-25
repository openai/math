import OAI.ThreeFlat.RepeatedCells
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Writing the eleven-word terminal cell rows

The first pass writes a copy of the common three-address, eight-coefficient
row at each physical location. Each private update then writes only the
eight coefficients of its named row. The plan states every individual write.
-/

namespace ThreeFlat.BitNetwork

abbrev RowSlot := Fin 3 ⊕ Fin 8
abbrev RowAddress (q : ℕ) := Fin q × RowSlot
abbrev CellWrite (q : ℕ) (W : Type*) := RowAddress q × W

def replayWrites {A W : Type*} [DecidableEq A] (xs : List (A × W)) (mem : A → W) :
    A → W := xs.foldl (fun m v => Function.update m v.1 v.2) mem

private theorem replay_point {A W : Type*} [DecidableEq A] (xs : List (A × W))
    (mem : A → W) (a : A) (v : W) (consistent : ∀ e ∈ xs, e.1 = a → e.2 = v) :
    replayWrites xs mem a = if a ∈ xs.map Prod.fst then v else mem a := by
  induction xs generalizing mem with
  | nil => simp [replayWrites]
  | cons e es ih =>
    change replayWrites es (Function.update mem e.1 e.2) a = _
    rw [ih _ (fun j hj => consistent j (by simp [hj]))]
    by_cases tail : a ∈ es.map Prod.fst
    · simp [tail]
    · by_cases hit : e.1 = a
      · simp [tail, hit, consistent e (by simp) hit]
      · simp [tail, Ne.symm hit, Function.update_of_ne]

variable {F W : Type*} {q : ℕ}

def cellRows (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) : RowAddress q → W
  | (i, .inl k) => wires i k
  | (i, .inr k) => encode (table i fun b => k.val.testBit b.val)

def defaultWrites (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) : List (CellWrite q W) :=
  (List.finRange q).flatMap fun i => List.ofFn fun k : Fin 11 =>
    let a : RowAddress q := (i, finSumFinEquiv.symm k)
    (a, cellRows wires table encode a)

def privateWrites (encode : F → W) (u : DirtyRow F q) : List (CellWrite q W) :=
  List.ofFn fun j : Fin 8 =>
    ((u.1, .inr j), encode (u.2 fun b => j.val.testBit b.val))

def cellWritePlan (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) (updates : List (DirtyRow F q)) : List (CellWrite q W) :=
  defaultWrites wires table encode ++ updates.flatMap (privateWrites encode)

private theorem replay_default (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) (initial : RowAddress q → W) :
    replayWrites (defaultWrites wires table encode) initial = cellRows wires table encode := by
  funext a
  rw [replay_point _ _ a (cellRows wires table encode a)]
  · apply ite_eq_left
    obtain ⟨i,k⟩ := a
    apply List.mem_map.mpr
    refine ⟨((i, k), cellRows wires table encode (i, k)), List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩, rfl⟩
    exact List.mem_ofFn.mpr ⟨finSumFinEquiv k, by simp⟩
  · intro e he
    obtain ⟨i, _, hk⟩ := List.mem_flatMap.mp he
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hk
    rintro rfl
    rfl

private theorem replay_private (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) (u : DirtyRow F q) :
    replayWrites (privateWrites encode u) (cellRows wires table encode) =
      cellRows wires (Function.update table u.1 u.2) encode := by
  funext a
  rw [replay_point _ _ a (cellRows wires (Function.update table u.1 u.2) encode a)]
  · obtain ⟨i,k|k⟩ := a
    · simp [privateWrites, cellRows]
    · by_cases hi : u.1 = i
      · apply ite_eq_left
        apply List.mem_map.mpr
        exact ⟨(_, _), List.mem_ofFn.mpr ⟨k,rfl⟩, by simp [hi]⟩
      · simp [privateWrites, cellRows, Ne.symm hi, Function.update_of_ne]
  · intro e he
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
    rintro rfl
    simp [cellRows]

/-- Every final address or coefficient is precisely the value prescribed by the
repeated template and its private updates. The initial contents are irrelevant. -/
theorem replay_cellWritePlan (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) (updates : List (DirtyRow F q)) (initial : RowAddress q → W) :
    replayWrites (cellWritePlan wires table encode updates) initial =
      cellRows wires (writeOverrides updates table) encode := by
  have append (xs ys : List (CellWrite q W)) (mem : RowAddress q → W) :
      replayWrites (xs ++ ys) mem = replayWrites ys (replayWrites xs mem) := by
    simp [replayWrites]
  unfold cellWritePlan
  rw [append, replay_default]
  induction updates generalizing table with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, append, replay_private]
    exact ih _

theorem cellWritePlan_length (wires : Fin q → Fin 3 → W) (table : Fin q → PrivateTable F)
    (encode : F → W) (updates : List (DirtyRow F q)) :
    (cellWritePlan wires table encode updates).length = q * 11 + updates.length * 8 := by
  simp [cellWritePlan, defaultWrites, privateWrites, List.length_flatMap, Nat.mul_comm]

end ThreeFlat.BitNetwork

end OAI
