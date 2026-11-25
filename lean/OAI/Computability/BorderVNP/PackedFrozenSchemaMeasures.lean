import OAI.Computability.BorderVNP.PackedFrozenProgramSchemas
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost

/-! # Exact scalar and row counts of the physical frozen tape combinators

The word count traverses the actual ordered source list and sums each stored tag
list. The pin counts include the entire reserved finite types, including holes.
Parallel copying and chronological append act additively on all four counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Shortening CellPacketGeometry.History

variable {R B R' B' : Type}

/-- Parallel children repeat the complete ordered source list once per child. -/
theorem Schema.parallel_length (S : Schema R B) (k : ℕ) :
    (S.parallel k).rows.length = k*S.rows.length := by
  have h (xs : List (Fin k)) : (xs.flatMap (fun i => S.rows.map (i,·))).length = xs.length*S.rows.length := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,ih,List.length_cons,Nat.succ_mul]; omega
  simpa only [Schema.parallel,List.length_finRange] using h (List.finRange k)

/-- All tag lists are retained with every parallel copy, including disabled candidates. -/
theorem Schema.parallel_words (S : Schema R B) (k : ℕ) :
    tagWords (S.parallel k) = k*tagWords S := by
  let sum := fun xs : List (Fin k × R) => (xs.map (fun z => (S.tags z.2).length)).sum
  have h (xs : List (Fin k)) : sum (xs.flatMap (fun i => S.rows.map (i,·))) = xs.length*tagWords S := by
    induction xs with
    | nil => simp [sum]
    | cons a xs ih =>
      simp only [sum,tagWords,List.flatMap_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,
        List.length_cons,Nat.succ_mul] at ih ⊢
      omega
  simpa only [sum,tagWords,Schema.parallel,List.length_finRange] using h (List.finRange k)

/-- Chronological append preserves every slot, in order. -/
theorem Schema.append_length (S : Schema R B) (T : Schema R' B') :
    (S.append T).rows.length = S.rows.length+T.rows.length := by simp [Schema.append]

/-- The two stored blocks' scalar tag words occupy disjoint successive source intervals. -/
theorem Schema.append_words (S : Schema R B) (T : Schema R' B') :
    tagWords (S.append T) = tagWords S+tagWords T := by
  simp only [tagWords,Schema.append,List.map_append,List.sum_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr]

/-- Four finite source costs needed by the routing geometry and packet compiler. -/
inductive Measure where
  /-- The entire type of possible record slots. -/
  | slots
  /-- Number of entries traversed by the public physical roster. -/
  | rows
  /-- Number of scalar positions represented by that roster's relocation tags. -/
  | words
  /-- The entire type of immutable scalar-bit pins. -/
  | payload

/-- Read the cost of the actual named physical format. -/
def Measure.count : Measure → Format → ℕ
  | .slots,S => Fintype.card S.Rows
  | .rows,S => S.schema.rows.length
  | .words,S => tagWords S.schema
  | .payload,S => Fintype.card S.Payload

/-- Complete finite cost of all child copies. -/
theorem Measure.parallel (M : Measure) (S : Format) (k : ℕ) : M.count (S.parallel k) = k*M.count S := by
  cases M
  · change Fintype.card (Fin k × S.Rows) = _
    simp [count]
  · exact S.schema.parallel_length k
  · exact S.schema.parallel_words k
  · change Fintype.card (Fin k × S.Payload) = _
    simp [count]

/-- Complete finite cost of a chronological splice. -/
theorem Measure.append (M : Measure) (S T : Format) : M.count (S.append T) = M.count S+M.count T := by
  cases M
  · change Fintype.card (S.Rows ⊕ T.Rows) = _
    simp [count]
  · exact S.schema.append_length T.schema
  · exact S.schema.append_words T.schema
  · change Fintype.card (S.Payload ⊕ T.Payload) = _
    simp [count]

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The three actual fresh block types introduced by one combining node. -/
noncomputable def freshFormat (A : Type) [Fintype A] (old np w : ℕ) : Format :=
  Format.ofSchema ((LayerRows.schema old D np w).append
    ((Birth.schema e (0,false) A w).append (HookTape.schema old D w)))

/-- The actual node writer preserves all prior child slots and appends exactly
the retained interval, birth, and hook formats. -/
theorem Measure.round (M : Measure) (A : Type) [Fintype A] (k old np w : ℕ) (S : Format) :
    M.count (Format.round e A k old np w S) = k*M.count S+M.count (freshFormat e A old np w) := by
  change M.count ((S.parallel k).append (freshFormat e A old np w)) = _
  rw [M.append,M.parallel]

end Packing.Inherited.FrozenTape

namespace Packing.Inherited.FrozenTape.ProgramSchemas

open Crossing Shortening Shortening.PublicDenseReceipt PackedHistoryCircuit.Normalized

variable {D m b : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {h H ν : ℝ}
    (path : SourcePath b e h H ν) (last high k : ℕ) (E : ℕ → ℕ) (np w : ℕ)

/-- Fresh source cost at an attained inner index. Indices outside the path have
no physical node and contribute no block. -/
noncomputable def innerIncrement (M : Measure) (j : ℕ) : ℕ :=
  if hj : j < b then M.count (freshFormat e (Seeds path last high ⟨j,hj⟩)
    (k*E j) (Parallel.nestedCapacity k np (j+1)) w) else 0

/-- All four measures follow the exact integer recurrence of the true inner
format, with the row counts and tag words read directly from the stored schema. -/
theorem inner_count (M : Measure) (base : Format) {j : ℕ} (hj : j ≤ b) :
    M.count (inner path last high k E np w base j) =
      combineSlots k (innerIncrement path last high k E np w M) (M.count base) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have lt : j < b := hj
    rw [inner_next path last high k E np w base ⟨j,lt⟩,innerRound,Measure.round,combineSlots,ih lt.le]
    simp only [innerIncrement,dite_eq_left lt]

end Packing.Inherited.FrozenTape.ProgramSchemas

end BorderVNP
end Computability
end OAI
