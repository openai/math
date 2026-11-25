import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchRounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Union
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Removing connected patches with small edge boundary

Edges carry distinct identifiers, allowing parallel edges and loops. Boundaries
count identifiers, with both orientations admitted. The existence of candidates
in induced subgraphs is the input supplied by the planar separator argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V E : Type*}

/-- The simple graph underlying a list of oriented edge endpoints. -/
def underlying (tail head : E → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e, (tail e = u ∧ head e = v) ∨ (tail e = v ∧ head e = u)
  symm := by
    constructor
    rintro u v ⟨huv, e, he⟩
    exact ⟨huv.symm, e, he.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Connectivity is tested within the patch. -/
def Connected (tail head : E → V) (P : Finset V) : Prop :=
  ((underlying tail head).induce (P : Set V)).Connected

variable [DecidableEq V] [Fintype E]

/-- Edges leaving a patch in the graph induced by the remaining vertices. -/
def boundary (tail head : E → V) (R P : Finset V) : Finset E :=
  Finset.univ.filter fun e =>
    (tail e ∈ P ∧ head e ∈ R \ P) ∨ (head e ∈ P ∧ tail e ∈ R \ P)

/-- A candidate in one removal round. -/
def Candidate (tail head : E → V) (K : ℕ) (ε : ℝ) (R P : Finset V) : Prop :=
  P.Nonempty ∧ P ⊆ R ∧ Connected tail head P ∧ P.card ≤ K ∧
    ((boundary tail head R P).card : ℝ) ≤ ε * P.card

/-- The edges induced by `R` whose endpoints lie in distinct partition blocks. -/
noncomputable def crossing (tail head : E → V) (R : Finset V)
    (blocks : Finset (Finset V)) : Finset E := by
  classical
  exact Finset.univ.filter fun e =>
    tail e ∈ R ∧ head e ∈ R ∧ ¬ ∃ P ∈ blocks, tail e ∈ P ∧ head e ∈ P

/-- A complete removal history. The index records the resulting family of patches. -/
inductive Peeling (tail head : E → V) (K : ℕ) (ε : ℝ) :
    Finset V → Finset (Finset V) → Prop
  | empty : Peeling tail head K ε ∅ ∅
  | cons {R P blocks} : Candidate tail head K ε R P → Peeling tail head K ε (R \ P) blocks →
      Peeling tail head K ε R (insert P blocks)

/-- The separator consequence needed for repeated removal. -/
theorem exists_peeling (tail head : E → V) (K : ℕ) (ε : ℝ) (vertices : Finset V)
    (hc : ∀ R ⊆ vertices, R.Nonempty → ∃ P, Candidate tail head K ε R P) :
    ∃ blocks, Peeling tail head K ε vertices blocks := by
  suffices h : ∀ R ⊆ vertices, ∃ blocks, Peeling tail head K ε R blocks by
    exact h vertices (Finset.Subset.refl _)
  intro R
  induction R using Finset.strongInductionOn
  rename_i R ih
  intro hR
  rcases R.eq_empty_or_nonempty with rfl | hn
  · exact ⟨∅, .empty⟩
  obtain ⟨P, hP⟩ := hc R hR hn
  have hstrict : R \ P ⊂ R := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
    obtain ⟨v, hv⟩ := hP.1
    intro he
    have : v ∈ R \ P := by rw [he]; exact hP.2.1 hv
    exact (Finset.mem_sdiff.mp this).2 hv
  obtain ⟨blocks, hblocks⟩ := ih _ hstrict (Finset.sdiff_subset.trans hR)
  exact ⟨insert P blocks, .cons hP hblocks⟩

/-- Shrinking the ambient induced subgraph can only discard boundary edges. -/
theorem boundary_mono (tail head : E → V) (P : Finset V) {R S : Finset V} (h : R ⊆ S) :
    boundary tail head R P ⊆ boundary tail head S P := by
  intro e he
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at he ⊢
  exact he.imp (fun ⟨ht, hh, hp⟩ => ⟨ht, h hh, hp⟩) (fun ⟨hh, ht, hp⟩ => ⟨hh, h ht, hp⟩)

/-- A surviving, disjoint candidate still satisfies its removal budget later in that round. -/
theorem Candidate.shrink {tail head : E → V} {K : ℕ} {ε : ℝ} {R S P : Finset V}
    (hP : Candidate tail head K ε R P) (hS : S ⊆ R) (hPS : P ⊆ S) :
    Candidate tail head K ε S P :=
  ⟨hP.1, hPS, hP.2.2.1, hP.2.2.2.1,
    (Nat.cast_le.mpr (Finset.card_le_card (boundary_mono tail head P hS))).trans hP.2.2.2.2⟩

/-- At a removal step, every crossing edge is charged to the new patch or stays
a crossing edge of the remaining induced graph. -/
theorem crossing_insert_subset [DecidableEq E] (tail head : E → V) (R P : Finset V)
    (blocks : Finset (Finset V)) :
    crossing tail head R (insert P blocks) ⊆
      boundary tail head R P ∪ crossing tail head (R \ P) blocks := by
  classical
  intro e he
  simp only [crossing, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨htR, hhR, hsep⟩ := he
  by_cases ht : tail e ∈ P
  · have hh : head e ∉ P := fun h => hsep ⟨P, Finset.mem_insert_self .., ht, h⟩
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inl ⟨ht, Finset.mem_sdiff.mpr ⟨hhR, hh⟩⟩⟩)
  by_cases hh : head e ∈ P
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Or.inr ⟨hh, Finset.mem_sdiff.mpr ⟨htR, ht⟩⟩⟩)
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨htR, ht⟩, Finset.mem_sdiff.mpr ⟨hhR, hh⟩, ?_⟩
  rintro ⟨Q, hQ, htQ, hhQ⟩
  exact hsep ⟨Q, Finset.mem_insert_of_mem hQ, htQ, hhQ⟩

/-- Every peeling partitions the original vertex set into disjoint, connected,
bounded-size pieces and cuts at most the total edge budget. -/
theorem Peeling.partition {tail head : E → V} {K : ℕ} {ε : ℝ}
    {R : Finset V} {blocks : Finset (Finset V)} (h : Peeling tail head K ε R blocks) :
    blocks.biUnion id = R ∧ (↑blocks : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ P ∈ blocks, P.Nonempty ∧ Connected tail head P ∧ P.card ≤ K) ∧
      ((crossing tail head R blocks).card : ℝ) ≤ ε * R.card := by
  classical
  induction h with
  | empty =>
    simp [crossing]
  | @cons R P blocks hP _ ih =>
    rcases ih with ⟨hcover, hdisj, hsize, hbudget⟩
    have hblock : ∀ Q ∈ blocks, Q ⊆ R \ P := by
      intro Q hQ v hv
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨Q, hQ, hv⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.biUnion_insert, id_eq, hcover, Finset.union_sdiff_of_subset hP.2.1]
    · intro A hA B hB hne
      rw [Finset.mem_coe, Finset.mem_insert] at hA hB
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact (hne rfl).elim
      · exact Finset.disjoint_left.mpr fun x hx hxB => (Finset.mem_sdiff.mp (hblock _ hB hxB)).2 hx
      · exact Finset.disjoint_left.mpr fun x hx hxP => (Finset.mem_sdiff.mp (hblock _ hA hx)).2 hxP
      · exact hdisj hA hB hne
    · intro Q hQ
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact ⟨hP.1, hP.2.2.1, hP.2.2.2.1⟩
      · exact hsize Q hQ
    · have hc : (R \ P).card + P.card = R.card := Finset.card_sdiff_add_card_eq_card hP.2.1
      have hcast : ((R \ P).card : ℝ) + (P.card : ℝ) = (R.card : ℝ) := by exact_mod_cast hc
      have hcut := (Finset.card_le_card (crossing_insert_subset tail head R P blocks)).trans
        (Finset.card_union_le _ _)
      calc
        ((crossing tail head R (insert P blocks)).card : ℝ) ≤
          (boundary tail head R P).card + ((crossing tail head (R \ P) blocks).card : ℝ) := by
            exact_mod_cast hcut
        _ ≤ ε * P.card + ε * (R \ P).card := add_le_add hP.2.2.2.2 hbudget
        _ = ε * R.card := by rw [← mul_add, add_comm, hcast]

/-- A family of small-boundary candidates in every nonempty remainder yields
a partition with the global crossing-edge estimate. -/
theorem exists_partition (tail head : E → V) (K : ℕ) (ε : ℝ) (vertices : Finset V)
    (hc : ∀ R ⊆ vertices, R.Nonempty → ∃ P, Candidate tail head K ε R P) :
    ∃ blocks : Finset (Finset V),
      blocks.biUnion id = vertices ∧ (↑blocks : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ P ∈ blocks, P.Nonempty ∧ Connected tail head P ∧ P.card ≤ K) ∧
      ((crossing tail head vertices blocks).card : ℝ) ≤ ε * vertices.card := by
  obtain ⟨blocks, h⟩ := exists_peeling tail head K ε vertices hc
  exact ⟨blocks, h.partition⟩

/-- Linearize one simultaneous round. Monotonicity of the edge boundary makes
every other chosen patch remain admissible when the first is removed. -/
theorem Peeling.prependRound {tail head : E → V} {K : ℕ} {ε : ℝ}
    (chosen : Finset (Finset V)) (R : Finset V) {blocks : Finset (Finset V)}
    (hdisj : (chosen : Set (Finset V)).PairwiseDisjoint id)
    (hc : ∀ P ∈ chosen, Candidate tail head K ε R P)
    (hrest : Peeling tail head K ε (R \ chosen.biUnion id) blocks) :
    Peeling tail head K ε R (chosen ∪ blocks) := by
  classical
  induction chosen using Finset.induction_on generalizing R with
  | empty => simpa using hrest
  | @insert P chosen hnot ih =>
    have hP := hc P (Finset.mem_insert_self ..)
    have hpair : (chosen : Set (Finset V)).PairwiseDisjoint id := by
      intro Q hQ T hT hne
      exact hdisj (Finset.mem_insert_of_mem hQ) (Finset.mem_insert_of_mem hT) hne
    have hnext : ∀ Q ∈ chosen, Candidate tail head K ε (R \ P) Q := by
      intro Q hQ
      have hQ' := hc Q (Finset.mem_insert_of_mem hQ)
      apply hQ'.shrink Finset.sdiff_subset
      intro x hx
      refine Finset.mem_sdiff.mpr ⟨hQ'.2.1 hx, ?_⟩
      have hd : Disjoint Q P := hdisj (Finset.mem_insert_of_mem hQ)
        (Finset.mem_insert_self ..) (fun h => hnot (h ▸ hQ))
      exact Finset.disjoint_left.mp hd hx
    have hrem : (R \ P) \ chosen.biUnion id = R \ (insert P chosen).biUnion id := by
      ext x
      simp only [Finset.biUnion_insert, id_eq, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← hrem] at hrest
    rw [Finset.insert_union]
    exact .cons hP (ih _ hpair hnext hrest)

/-- All candidates on an induced vertex set. -/
noncomputable def candidatesOn (tail head : E → V) (K : ℕ) (ε : ℝ) (R : Finset V) :
    Finset (Finset V) := by
  classical
  exact R.powerset.filter (Candidate tail head K ε R)

@[simp] theorem mem_candidatesOn {tail head : E → V} {K : ℕ} {ε : ℝ} {R P : Finset V} :
    P ∈ candidatesOn tail head K ε R ↔ Candidate tail head K ε R P := by
  classical
  simp only [candidatesOn, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨And.right, fun h => ⟨h.2.1, h⟩⟩

/-- The union of all patch families selected by the deterministic round rule. -/
noncomputable def canonicalBlocks (key : V ↪ ℕ) (tail head : E → V) (K : ℕ) (ε : ℝ)
    (R : Finset V) (n : ℕ) : Finset (Finset V) :=
  ((patchRounds key (candidatesOn tail head K ε) R n).foldr (· ∪ ·) ∅)

/-- The lexicographic round algorithm realizes a complete peeling in at most
the number of vertices many rounds. -/
theorem canonical_peeling (key : V ↪ ℕ) (tail head : E → V) (K : ℕ) (ε : ℝ)
    (vertices : Finset V) (hc : ∀ R ⊆ vertices, R.Nonempty → ∃ P, Candidate tail head K ε R P)
    {n : ℕ} (hn : vertices.card ≤ n) :
    Peeling tail head K ε vertices (canonicalBlocks key tail head K ε vertices n) := by
  classical
  let C := candidatesOn tail head K ε
  have h : ∀ (m : ℕ) (R : Finset V), R ⊆ vertices → R.card ≤ m →
      Peeling tail head K ε R (canonicalBlocks key tail head K ε R m) := by
    intro m
    induction m with
    | zero =>
      intro R _ hcard
      have he : R = ∅ := Finset.card_eq_zero.mp (by omega)
      subst R
      exact .empty
    | succ m ih =>
      intro R hsub hcard
      let selectedR := roundSelected key C R
      let nextR := nextRemaining key C R
      have hsel : ∀ P ∈ selectedR, Candidate tail head K ε R P :=
        fun _ hp => mem_candidatesOn.mp ((mem_selected key).mp hp).1
      have hnext : nextR ⊆ R := Finset.sdiff_subset
      have hcard' : nextR.card ≤ m := by
        rcases R.eq_empty_or_nonempty with rfl | hnR
        · simp [nextR, nextRemaining]
        obtain ⟨P, hp⟩ := hc R hsub hnR
        obtain ⟨Q, hQ⟩ := selected_nonempty key (show (C R).Nonempty from ⟨P, mem_candidatesOn.mpr hp⟩)
        have hstrict : nextR ⊂ R := by
          refine Finset.sdiff_ssubset ?_ ?_
          · intro x hx
            obtain ⟨T, hT, hxt⟩ := Finset.mem_biUnion.mp hx
            exact (hsel _ hT).2.1 hxt
          · obtain ⟨x, hx⟩ := (hsel _ hQ).1
            exact ⟨x, Finset.mem_biUnion.mpr ⟨Q, hQ, hx⟩⟩
        have := Finset.card_lt_card hstrict
        omega
      exact Peeling.prependRound selectedR R (fun _ hP _ hQ hne => selected_disjoint key hP hQ hne)
        hsel (ih nextR (hnext.trans hsub) hcard')
  exact h n vertices (Finset.Subset.refl _) hn

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
