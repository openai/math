import OAI.Computability.BorderVNP.TeamContractionSpelling

/-! # Signed reindexing from actual finite site leaves to checked native executions

The branch scripts, raw links and accumulator signs determine the finite-site witness.
When the endpoint replay produces a unique checked history for those spellings, this
identification composes with the native RAM history equivalence, preserving signs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP RAMTape TeamSiteConsistency TeamContraction.Wires TeamSite TeamSiteEvents
open scoped BigOperators Classical

variable {R teams t d link inner n p regs pub a e w m g : ℕ} {Q Γ : Type}
variable {M : Setup teams w p regs pub a e} {lib : Fin a → Macro Q Γ m g}
variable {G : Wiring R teams t d link inner n (Edge teams regs w e (w+1))}
variable {pin : Fin d → Bool} {ext : Exterior R teams link → Bool} {team : Fin (R+1)}

/-- The verified physical parsing and the checked row reconstruction supply these two
directions. Their common relation contains the exact machine input bits and sign, so
finite terminal paths are never counted by a guessed multiplicity. -/
structure SpellingBijection (M : Setup teams w p regs pub a e) (G : Wiring R teams t d link inner n (Edge teams regs w e (w+1)))
    (lib : Fin a → Macro Q Γ m g) (pin : Fin d → Bool) (ext : Exterior R teams link → Bool) (team : Fin (R+1)) : Prop where
  /-- Each actual collection of successful processor scripts recovers one native history. -/
  sound : ∀ s : SiteWitness G M.program lib pin ext team, ∃! z : M.Histories, Spells z.val s
  /-- Each nonzero history runs its exact script successfully on every real processor. -/
  complete : ∀ z : M.NonzeroHistories, ∃ s : SiteWitness G M.program lib pin ext team, Spells z.val.val s

variable (b : SpellingBijection M G lib pin ext team)

/-- The explicit bijection from physical finite scripts and shared bits to nonzero
checked histories. It retains the original links, private choices and endpoint sign. -/
noncomputable def SpellingBijection.rawEquiv : SiteWitness G M.program lib pin ext team ≃ M.NonzeroHistories where
  toFun s := ⟨(b.sound s).choose, ((b.sound s).choose_spec.1.weight ▸ siteWeight_ne_zero s)⟩
  invFun z := (b.complete z).choose
  left_inv s := (b.complete _).choose_spec.physical_unique (b.sound s).choose_spec.1
  right_inv z := Subtype.ext (((b.sound _).choose_spec.2 _ (b.complete z).choose_spec).symm)

/-- Every bit and sign agree pointwise under the physical-to-raw identification. -/
theorem SpellingBijection.spells_equiv (s : SiteWitness G M.program lib pin ext team) :
    Spells (b.rawEquiv s).val.val s := (b.sound s).choose_spec.1

/-- Physical accepted witnesses correspond to genuine nonzero RAM paths on the entire
shared mutable memory, with their complete native tapes and original word bounds. -/
noncomputable def SpellingBijection.nativeEquiv :
    SiteWitness G M.program lib pin ext team ≃ NonzeroPath M.machine M.limit.val M.cap.val M.privateClock :=
  b.rawEquiv.trans M.nonzeroEquiv

/-- Physical terminal weights agree pointwise with the product of signs on actual RAM instructions. -/
theorem SpellingBijection.native_weight (s : SiteWitness G M.program lib pin ext team) :
    siteWeight s = pathWeight (b.nativeEquiv s).val.val :=
  (b.spells_equiv s).weight.trans (M.rawEquivNative_weight (b.rawEquiv s).val)

include b in
/-- Reindexing the actual finite integer sum along the proved path equivalence preserves
the full native signed RAM value, including the harmless zero contributions. -/
theorem SpellingBijection.sum_eq_native :
    (∑ s : SiteWitness G M.program lib pin ext team, siteWeight s) =
      nativeValue M.machine M.limit.val M.cap.val M.privateClock := by
  let := Fintype.ofFinite (NativePath M.machine M.limit.val M.cap.val M.privateClock)
  rw [nativeValue_nonzero]
  apply Finset.sum_equiv b.nativeEquiv (by simp)
  intro s _
  exact b.native_weight s

end TeamContraction

end BorderVNP
end Computability
end OAI
