import OAI.Computability.BorderVNP.TeamContractionReadout
import OAI.Computability.BorderVNP.TeamSiteConsistencyPaths
import OAI.Computability.BorderVNP.TeamSiteEvents

/-! # Exact shared links, local branch scripts and signed weights

A physical witness spells a checked history by reading the same interior links
and consuming precisely its native event choices, including the old-word guesses.
Each site sign is the sign reached by its actual accumulator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape TeamSiteConsistency TeamContraction.Wires TeamSite TeamSiteEvents
open scoped BigOperators Classical

variable {R teams t d link inner n p regs pub a e w m g : ℕ} {Q Γ : Type}
variable {P : TeamOpcode.Program p regs pub a} {lib : Fin a → Macro Q Γ m g}
variable {G : Wiring R teams t d link inner n (Edge teams regs w e (w+1))}
variable {pin : Fin d → Bool} {ext : Exterior R teams link → Bool} {team : Fin (R+1)}

/-- The link assignment, each complete native choice spelling, and each nonzero local
sign agree between an actual physical universal witness and a checked team history. -/
structure Spells (z : RawHistory teams regs w e) (s : SiteWitness G P lib pin ext team) : Prop where
  /-- The concrete assignment on the shared register and sorter fields. -/
  links : s.1 = z.links
  /-- Every guessed word and every native choice bit appears in the physical script. -/
  bits : ∀ j, chunkBits (z.blocks j) = (s.2 j).val.1
  /-- Actual terminal sign of the accumulator on every real site. -/
  sign : ∀ j, chunkSign (some false) (z.blocks j) = some (s.2 j).val.2

/-- The integer contribution in a checked history factors over exactly its real sites. -/
theorem rawWeight_prod (z : RawHistory teams regs w e) :
    z.weight = ∏ j, (TeamPrivateCall.sign (chunkSign (some false) (z.blocks j))).value := by
  rw [RawHistory.weight,← List.ofFn_comp', Fin.prod_ofFn]

/-- Exactly the histories without an absorbed zero in any real processor have nonzero weight. -/
theorem rawWeight_ne_zero_iff (z : RawHistory teams regs w e) :
    z.weight ≠ 0 ↔ ∀ j, (chunkSign (some false) (z.blocks j)).isSome = true := by
  rw [rawWeight_prod,Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_const]
  apply forall_congr'
  intro j
  cases chunkSign (some false) (z.blocks j) with
  | none => decide
  | some b => cases b <;> decide

/-- The sign of the physical tensor factor is the product of the actual native signs. -/
theorem Spells.weight {z : RawHistory teams regs w e} {s : SiteWitness G P lib pin ext team}
    (h : Spells z s) : siteWeight s = z.weight := by
  rw [siteWeight,rawWeight_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [h.sign]
  cases (s.2 j).val.2 <;> rfl

/-- Every checked history has at most one physical witness with the specified spellings. -/
theorem Spells.physical_unique {z : RawHistory teams regs w e} {s₁ s₂ : SiteWitness G P lib pin ext team}
    (h₁ : Spells z s₁) (h₂ : Spells z s₂) : s₁ = s₂ := by
  obtain ⟨f₁,s₁⟩ := s₁
  obtain ⟨f₂,s₂⟩ := s₂
  obtain rfl : f₁ = f₂ := h₁.links.trans h₂.links.symm
  apply congrArg (Sigma.mk f₁)
  funext j
  apply Subtype.ext
  exact Prod.ext ((h₁.bits j).symm.trans (h₂.bits j)) (Option.some.inj ((h₁.sign j).symm.trans (h₂.sign j)))

/-- A nonzero history specifies its physical scripts and terminal sign bits exactly;
only membership of those exact pairs in the actual replay-leaf sets remains to check. -/
theorem spells_exists_iff (z : RawHistory teams regs w e) (hz : z.weight ≠ 0) :
    (∃ s : SiteWitness G P lib pin ext team, Spells z s) ↔
      ∀ j, (chunkBits (z.blocks j), (chunkSign (some false) (z.blocks j)).getD false) ∈
        physicalLeaves G Layout.input (Processor.code P lib) Processor.negative Processor.start
          36 pin ext z.links team j := by
  have hs := (rawWeight_ne_zero_iff z).mp hz
  constructor
  · rintro ⟨⟨f,s⟩,h⟩
    obtain rfl : f = z.links := h.links
    intro j
    rw [h.bits j,h.sign j]
    exact (s j).property
  · intro h
    refine ⟨⟨z.links,fun j => ⟨_,h j⟩⟩,rfl,fun _ => rfl,?_⟩
    intro j
    cases eq : chunkSign (some false) (z.blocks j) with
    | none => have := hs j; simp [eq] at this
    | some b => simp [eq]

end TeamContraction

end BorderVNP
end Computability
end OAI
