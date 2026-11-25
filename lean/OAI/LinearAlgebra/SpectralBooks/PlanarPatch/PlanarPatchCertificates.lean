import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchRounds

/-!
# Vertex certificates for simultaneous planar patch removal

Each vertex reports its one-based removal round and the least vertex name of
its patch. In round `t + 1` the verifier uses all vertices reporting a round
strictly greater than `t`. The checks force these reported residual sets to
coincide with the true residuals, even before exhaustion is known.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V : Type*} [DecidableEq V]
variable (key : V ↪ ℕ) (candidates : Finset V → Finset (Finset V))

/-- The label carried by all vertices removed in a given patch. -/
def leastName (P : Finset V) : ℕ :=
  if h : P.Nonempty then (P.map key).min' (h.map) else 0

/-- The vertex set that the reported removal times give after `t` rounds. -/
def reportedRemaining (R : Finset V) (record : V → ℕ × ℕ) (t : ℕ) : Finset V :=
  R.filter fun v => t < (record v).1

/-- A vertex performs its membership and minimum-name checks in each round up
to and including the round it reports. -/
def RecordsValid (R : Finset V) (N : ℕ) (record : V → ℕ × ℕ) : Prop :=
  (∀ v ∈ R, 0 < (record v).1 ∧ (record v).1 ≤ N) ∧
  ∀ v ∈ R, ∀ t < (record v).1,
    let B := roundSelected key candidates (reportedRemaining R record t)
    ((record v).1 = t + 1 ↔ ∃ P ∈ B, v ∈ P) ∧
      ∀ P ∈ B, v ∈ P → (record v).2 = leastName key P

variable {R : Finset V} {N : ℕ} {record : V → ℕ × ℕ}

/-- Induction on rounds recovers the actual remaining graph from accepted records. -/
theorem reportedRemaining_eq_of_valid (hc : RecordsValid key candidates R N record) (t : ℕ) :
    reportedRemaining R record t = residual key candidates R t := by
  induction t with
  | zero =>
    ext v
    exact Finset.mem_filter.trans ⟨And.left, fun hv => ⟨hv, (hc.1 v hv).1⟩⟩
  | succ t ih =>
    rw [residual_succ, ← ih, nextRemaining]
    ext v
    simp only [reportedRemaining, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨hv, ht⟩
      have ht' : t < (record v).1 := by omega
      exact ⟨⟨hv, ht'⟩, fun h => (by omega : (record v).1 ≠ t + 1) ((hc.2 v hv t ht').1.2 h)⟩
    · rintro ⟨⟨hv, ht⟩, hm⟩
      have hne : (record v).1 ≠ t + 1 := fun h => hm ((hc.2 v hv t ht).1.1 h)
      exact ⟨hv, by omega⟩

variable (hsound : ∀ ⦃S P⦄, P ∈ candidates S → P.Nonempty ∧ P ⊆ S)
    (hexists : ∀ ⦃S⦄, S.Nonempty → (candidates S).Nonempty)

include hsound in
/-- For every selected patch the checks force the two reported integers at each vertex. -/
theorem record_eq_of_valid (hc : RecordsValid key candidates R N record)
    {t : ℕ} {P : Finset V} {v : V}
    (hP : P ∈ roundSelected key candidates (residual key candidates R t)) (hvP : v ∈ P) :
    record v = (t + 1, leastName key P) := by
  have hvr := (roundSelected_sound key candidates hsound hP).2 hvP
  rw [← reportedRemaining_eq_of_valid key candidates hc t] at hP hvr
  obtain ⟨hvR, ht⟩ := Finset.mem_filter.mp hvr
  have h := hc.2 v hvR t ht
  exact Prod.ext (h.1.2 ⟨P,hP,hvP⟩) (h.2 P hP hvP)

include hsound hexists in
/-- Two valid certificates agree on every vertex of the input. -/
theorem recordsValid_unique {a b : V → ℕ × ℕ}
    (ha : RecordsValid key candidates R N a) (hb : RecordsValid key candidates R N b)
    (v : V) (hv : v ∈ R) : a v = b v := by
  obtain ⟨⟨t, P⟩, ⟨_, hP, hvP⟩, _⟩ := existsUnique_removal key candidates hsound hexists hv
  exact (record_eq_of_valid key candidates hsound ha hP hvP).trans
    (record_eq_of_valid key candidates hsound hb hP hvP).symm

include hsound in
private theorem mem_residual_until {v : V} {P : Finset V} {s : ℕ}
    (hP : P ∈ roundSelected key candidates (residual key candidates R s))
    (hvP : v ∈ P) (t : ℕ) : v ∈ residual key candidates R t ↔ t ≤ s := by
  refine ⟨fun hv => le_of_not_gt fun hst => ?_, fun hts => ?_⟩
  · exact Finset.disjoint_left.mp (disjoint_later_residual key candidates hst hP) hvP hv
  · exact residual_antitone key candidates R hts ((roundSelected_sound key candidates hsound hP).2 hvP)

include hsound hexists in
/-- The true removal time and least patch name give a valid certificate whenever
the allowed number of rounds is at least the initial number of vertices. -/
theorem exists_recordsValid (hN : R.card ≤ N) :
    ∃ record : V → ℕ × ℕ, RecordsValid key candidates R N record := by
  classical
  choose b hb using fun v : R => (existsUnique_removal key candidates hsound hexists v.property).exists
  let record (v : V) : ℕ × ℕ :=
    if h : v ∈ R then ((b ⟨v,h⟩).1 + 1, leastName key (b ⟨v,h⟩).2) else (0,0)
  have hrecord (v : V) (hv : v ∈ R) :
      record v = ((b ⟨v,hv⟩).1 + 1, leastName key (b ⟨v,hv⟩).2) := by simp [record, hv]
  have hsets (t : ℕ) : reportedRemaining R record t = residual key candidates R t := by
    ext v
    rw [reportedRemaining, Finset.mem_filter]
    by_cases hv : v ∈ R
    · obtain ⟨_, hP, hvP⟩ := hb ⟨v,hv⟩
      rw [hrecord v hv, mem_residual_until key candidates hsound hP hvP]
      exact (and_iff_right hv).trans Nat.lt_succ_iff
    · simp only [hv, false_and, false_iff]
      exact fun h => hv (residual_antitone key candidates R (Nat.zero_le t) h)
  refine ⟨record, ?_, ?_⟩
  · intro v hv
    rw [hrecord v hv]
    exact ⟨Nat.succ_pos _, (hb ⟨v,hv⟩).1.trans_le hN⟩
  · intro v hv t _
    dsimp only
    rw [hsets, hrecord v hv]
    let i : R := ⟨v,hv⟩
    obtain ⟨_, hP, hvP⟩ := hb i
    constructor
    · constructor
      · intro ht
        have h : (b i).1 = t := Nat.succ.inj ht
        exact ⟨(b i).2, h ▸ hP, hvP⟩
      · rintro ⟨Q, hQ, hvQ⟩
        have h := removal_unique key candidates hsound hP hvP hQ hvQ
        exact congrArg Nat.succ (congrArg Prod.fst h).symm
    · intro Q hQ hvQ
      have h := removal_unique key candidates hsound hP hvP hQ hvQ
      exact congrArg (leastName key) (congrArg Prod.snd h).symm

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
