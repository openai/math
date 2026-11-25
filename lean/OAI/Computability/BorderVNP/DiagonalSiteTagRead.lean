import OAI.Computability.BorderVNP.PackedRetainedWork
import OAI.Computability.BorderVNP.DiagonalPowerSites

/-! # Pointwise sparse observations of a tagged site, with its original choices fixed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site

open Diagonal.CellEntries
open scoped Classical

variable {Param Gadget : Type*}

/-- The actual observation fiber for one fixed input and the original
private choices belonging to this site. A successful occurrence of a zero
field scalar remains a passing tag with its true matrix identifier. -/
structure TagRead (site : Site) (input : Fin site.incoming → Bool)
    (compatible : (Fin site.work → Bool) → Prop) (tag : Entry Param Gadget) (number : Gadget ↪ ℕ) where
  /-- Canonical original choices followed by all forced staging bits. -/
  work : Fin site.work → Bool
  /-- Actual ordered observations of the sparse private program. -/
  observations : List (Bool × Option ℕ)
  /-- The selected work contains the prescribed independent private choices. -/
  chosen : compatible work
  /-- Passing is exactly this work vector and the nonzero tagged entry. -/
  read : ∀ g os, compatible g → (site.observe (bits g input) = some os ↔
    tag ≠ 0 ∧ g = work ∧ os = observations)
  /-- Native scalar-ID counts agree at every position, before specialization. -/
  count : tag ≠ 0 → ∀ g, (observations.filterMap Prod.snd).count (number g) = (counters tag).2 g

variable {site current : Site} {tag : Entry Param Gadget} {number : Gadget ↪ ℕ}
    {compatible : (Fin site.work → Bool) → Prop}

/-- Compare original private choices in the offset-zero birth region of
a retained site. -/
def Retention.original (r : site.Retention current) (w : Fin current.work → Bool) : Fin site.work → Bool :=
  fun i => w (i.castLE r.work_le)

/-- Appending the actual forced inputs preserves the complete tagged
observation fiber, including its order and each selected scalar count. -/
def TagRead.retained (r : site.Retention current) (loc : site.Local) (input : Fin current.incoming → Bool)
    (h : TagRead site (r.readInput input) compatible tag number) :
    TagRead current input (fun g => compatible (r.original g)) tag number where
  work := r.complete input h.work
  observations := h.observations
  chosen := by
    have old : r.original (r.complete input h.work) = h.work :=
      funext fun j => r.complete_prefix input h.work j
    exact old.symm ▸ h.chosen
  read g os hg := by
    rw [r.observe_iff loc input os g]
    constructor
    · rintro ⟨v,seen,hv⟩
      have old : r.original g = v := by
        rw [←hv]
        exact funext fun j => r.complete_prefix input v j
      obtain ⟨pass,eq,report⟩ := (h.read v os (old ▸ hg)).mp seen
      exact ⟨pass,hv.symm.trans (congrArg (r.complete input) eq),report⟩
    · rintro ⟨pass,rfl,rfl⟩
      exact ⟨h.work,(h.read _ _ h.chosen).mpr ⟨pass,rfl,rfl⟩,rfl⟩
  count := h.count

/-- A passing prescribed birth tag has exactly one compatible successful
work vector, even if many other independent bottom witnesses pass. -/
theorem TagRead.unique {input : Fin site.incoming → Bool} (h : TagRead site input compatible tag number)
    (passed : tag ≠ 0) : ∃! g, compatible g ∧ ∃ os, site.observe (bits g input) = some os := by
  refine ⟨h.work,⟨h.chosen,h.observations,(h.read _ _ h.chosen).mpr ⟨passed,rfl,rfl⟩⟩,?_⟩
  rintro g ⟨hg,os,seen⟩
  exact ((h.read g os hg).mp seen).2.1

end Packing.Inherited.Site

end BorderVNP
end Computability
end OAI
