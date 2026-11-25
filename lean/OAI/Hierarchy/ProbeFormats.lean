import OAI.Hierarchy.ProbeLocalFlattening

namespace OAI
/-! # One common radius and positive tolerance for every bounded wired local format -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical
noncomputable section

/-- All local test formats at a bounded site/role/observation cardinality have a
finite code. Costs of the physical link kinds are evaluated afterwards at M; the
code contains only their tags, their incidences and the two directed port maps. -/
abbrev FiniteFormat (bound k kinds : ℕ) :=
  Σ s : Fin (bound+1), Σ c : Fin (bound+1), Σ e : Fin (bound+1),
  Σ a : Fin (bound+1), Σ l : Fin (bound+1),
    Fin (c.val+1) × (Fin (e.val+1) → Chord (s.val+1)) × (Fin a.val → Fin (e.val+1)) ×
    (Fin (e.val+1) → Fin kinds) × (Fin (c.val+1) → Fin (s.val+1)) ×
    (Fin (c.val+1) → Fin k → Bool → Fin (s.val+1)) × (Fin (c.val+1) → Fin (c.val+1) → Bool) ×
    (Fin l.val → Fin (c.val+1) × Fin (c.val+1) ×
      (Fin (e.val+1) ⊕ (Unit ⊕ (Fin k × Bool × Fin (e.val+1)))))

/-- This includes empty format lists; inactive newly purchased sockets can therefore
be given the same common tolerance as all their active relatives. -/
theorem finite_tolerances {J : Type*} [Fintype J] (good : J → ℕ → ℝ → Prop)
    (monotone : ∀ j M, ∀ {a b : ℝ}, a ≤ b → good j M b → good j M a)
    (each : ∀ j, ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ good j M ε) :
    ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ ∀ j, good j M ε := by
  classical
  choose N works using each
  refine ⟨Finset.univ.sup N,?_⟩
  intro M wide
  choose ε pos certified using fun j => works j M ((Finset.le_sup (f:=N) (Finset.mem_univ j)).trans wide)
  let choices := insert 1 (Finset.univ.image ε)
  have nonempty : choices.Nonempty := Finset.insert_nonempty ..
  have small : ∀ j, choices.min' nonempty ≤ ε j := fun j =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩))
  have positive : 0 < choices.min' nonempty := by
    have mem := choices.min'_mem nonempty
    rcases Finset.mem_insert.mp mem with one | more
    · rw [one]; norm_num
    · obtain ⟨j,_,eq⟩ := Finset.mem_image.mp more
      rw [←eq]; exact pos j
  exact ⟨choices.min' nonempty,positive,fun j => monotone j M (small j) (certified j)⟩

/-- Uniform finite-format specialization, with the decision criterion evaluated on
the price box and the finite, actual spectrum discrepancy of each format. -/
theorem common_flattening_tolerance {F J : Type*} [Field F] [Fintype J]
    (S : J → ℕ) (E A : J → Type*) [∀ j, Nonempty (Fin (S j))]
    [∀ j, Fintype (E j)] [∀ j, Nonempty (E j)] [∀ j, Fintype (A j)]
    (edge : ∀ j, E j → Chord (S j)) (req : ∀ j, A j → E j)
    (box : ∀ j, ℕ → Set (E j → ℝ)) (frame : ∀ j, ℕ → (E j → ℝ) → Prop)
    (format : ∀ j, ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ box j M,
      Probe.discrepancy F (edge j) (req j) p ≤ ε → frame j M p) :
    ∃ N : ℕ, ∀ M ≥ N, ∃ ε : ℝ, 0 < ε ∧ ∀ j, ∀ p ∈ box j M,
      Probe.discrepancy F (edge j) (req j) p ≤ ε → frame j M p := by
  apply finite_tolerances (fun j M ε => ∀ p ∈ box j M, Probe.discrepancy F (edge j) (req j) p ≤ ε → frame j M p)
    (fun j M _ _ le realize p inside small => realize p inside (small.trans le)) format

end
end Hierarchy.AdaptiveProbe

end OAI
