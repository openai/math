import OAI.Optimization.LinearProgramming.Recovery.LP

/-! Size of the inputs to the actual repeated subspace calls in Section 2.3. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix Presentation Geometry
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d n : ℕ}

/-- All entries of both matrices in one presentation satisfy `P`. -/
def Presentation.entriesSatisfy (u : Presentation K n) (P : K → Prop) : Prop :=
  (∀ i j, P (u.equations i j)) ∧ ∀ i j, P (u.output i j)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Presentation.restrict_entries {u : Presentation K n} {P : K → Prop} (h : u.entriesSatisfy P)
    (hz : P 0) (s : Finset (Fin n)) : (u.restrict s).entriesSatisfy P := by
  refine ⟨?_,h.2⟩
  intro i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · change P (Fin.append (fun r a => u.equations r a) (fun k => if k ∈ s then 0 else u.output k)
        (Fin.castAdd n k) j)
    rw [Fin.append_left]; exact h.1 k j
  · change P (Fin.append (fun r a => u.equations r a) (fun k => if k ∈ s then 0 else u.output k)
        (Fin.natAdd u.rows k) j)
    rw [Fin.append_right]
    by_cases hk : k ∈ s
    · simp only [ite_eq_left hk]; exact hz
    · simp only [ite_eq_right hk]; exact h.2 k j

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem slackColumns_entries (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) {P : K → Prop}
    (h0 : P 0) (h1 : P 1) (hA : ∀ i j, P (-A i j)) (hb : ∀ i, P (b i)) :
    ∀ i j, P (slackColumns A b i j) := by
  intro i j
  refine Fin.cases ?_ (fun r => ?_) i
  · exact Fin.cases h1 (fun _ => h0) j
  · exact Fin.cases (hb r) (hA r) j

omit [IsStrictOrderedRing K] in
/-- Each queried system uses the original column matrix or its transpose, with at most one
block of coordinate equations. In particular, the row/variable dimensions and input heights
do not grow with the history of the greedy deletion pass. -/
theorem solveLP_query_layout (decide : Presentation K (m+1) → Bool) (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (u : Presentation K (m+1)) (hu : u ∈ (solveLP decide A b).queries)
    {P : K → Prop} (h0 : P 0) (h1 : P 1) (hA : ∀ i j, P (-A i j)) (hb : ∀ i, P (b i)) :
    u.rows ≤ m + d + 2 ∧ u.nVars ≤ m + d + 2 ∧ u.entriesSatisfy P := by
  let B := slackColumns A b
  let primal := fromColumns B
  let dual := fromKernel Bᵀ
  let side := if decide primal then primal else dual
  have hB := slackColumns_entries A b h0 h1 hA hb
  have hp : primal.entriesSatisfy P := ⟨fun i => i.elim0, hB⟩
  have identityEntries (i j : Fin (m+1)) : P ((1 : Matrix (Fin (m+1)) (Fin (m+1)) K) i j) := by
    rw [Matrix.one_apply]
    split <;> assumption
  have hd : dual.entriesSatisfy P := ⟨fun i j => hB j i, identityEntries⟩
  change u ∈ primal :: (deleteCoordinates (fun s => decide (side.restrict s))
    ((List.finRange (m+1)).erase 0) Finset.univ).2.map (restrict side) at hu
  rcases List.mem_cons.mp hu with rfl | hm
  · exact ⟨by simp [primal,fromColumns],by simp [primal,fromColumns]; omega,hp⟩
  · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hm
    cases h : decide primal with
    | false =>
      have e : side = dual := by simp [side,h]
      rw [e]
      exact ⟨by change d+1+(m+1) ≤ _; omega, by change m+1 ≤ _; omega, Presentation.restrict_entries hd h0 _⟩
    | true =>
      have e : side = primal := by simp [side,h]
      rw [e]
      exact ⟨by change 0+(m+1) ≤ _; omega, by change d+1 ≤ _; omega, Presentation.restrict_entries hp h0 _⟩

end Recovery
end LinearProgramming
end Optimization
end OAI
