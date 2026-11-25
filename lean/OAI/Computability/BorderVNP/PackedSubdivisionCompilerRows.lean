import OAI.Computability.BorderVNP.PackedCompilerRows
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms

/-! # Compiler row bounds after physical cable subdivision

Retaining an old site adds only equality rows. Each newly born interior site
has one equality row and empty box storage. Hence subdividing the actual cables
preserves the two fixed template bounds independently of the hop count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing CellSparse Shortening
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide routes).Edge ↪ Fin n)
    (portID : P ↪ Fin np) {K : Type*} [Field K] {k : ℕ} (e : PaidIdentity K D k)

/-- The original program keeps its one-copy tables and gains only bounded
equality rows when its physical incidence words move to the selected hops. -/
theorem originalProgram_compilerRows (v : N.Site) (s : Site) (h : s.CompilerRows e) :
    (originalProgram N routes v oldID newID portID s).CompilerRows e :=
  ⟨s.schema_retain h.1 _ _,s.rowBound_retain h.2.1 (by omega) _ _,h.2.2.retain _ _⟩

/-- A newly inserted relay has exactly one equality row, including on a
zero-width cable, and its one-copy table list is empty. -/
theorem relaySite_compilerRows (j : (a : N.Edge) × Fin (routes.interior a)) :
    (relaySite N routes newID portID j).CompilerRows e := by
  apply Site.CompilerRows.of_initial
  · intro r hr
    change r ∈ [relayRecord N routes newID portID j] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨trivial,trivial⟩
  · intro r hr
    change r ∈ [relayRecord N routes newID portID j] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Nat.le_refl 9
  · intro fs hs
    exact False.elim (List.not_mem_nil hs)

/-- The actual subdivided program at every physical site satisfies the same
invariant as the program on the original cable network. -/
theorem subdividePrivatePrograms_compilerRows (prior : Site.Programs N)
    (h : ∀ v, (prior v).program.CompilerRows e) (z : (N.subdivide routes).Site) :
    (subdividePrivatePrograms N routes oldID newID portID prior z).program.CompilerRows e := by
  cases z with
  | inl v => exact originalProgram_compilerRows N routes oldID newID portID e v _ (h v)
  | inr j => exact relaySite_compilerRows N routes newID portID e j

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
