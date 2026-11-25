import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedInheritedProfileValue
import OAI.Computability.BorderVNP.PackedInheritedRowNames

/-! # Exact local contraction for every installed site of a combining round

The public interval order determines the list of inherited equality checks.
Permuting that list preserves all observations and thus every weight, while
the profile and paid birth programs directly realize the new physical factors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open InheritedProfile CellSparse
open scoped Classical

/-- Retaining the same cut rows in a different enumeration preserves every signed observation. -/
theorem Site.retain_observe_perm (s : Site) (n : ℕ) {a b : List Slice}
    (h : a.Perm b) (bank : ℕ → Bool) : (s.retain n a).observe bank = (s.retain n b).observe bank := by
  simp only [Site.observe_retain]
  congr 1
  exact propext (forall_congr' fun _ => imp_congr_left h.mem_iff)

/-- The contraction therefore survives reordering the newly emitted intrinsic interval list. -/
theorem Site.retain_value_perm {R : Type*} [AddCommMonoid R] (s : Site) (n : ℕ) {a b : List Slice}
    (h : a.Perm b) (weight : List (Bool × Option ℕ) → R) (input : Fin n → Bool) :
    (s.retain n a).value weight input = (s.retain n b).value weight input := by
  change (∑ g : Fin (s.work+s.incoming) → Bool, ((s.retain n a).observe (bits g input)).elim 0 weight) =
    ∑ g : Fin (s.work+s.incoming) → Bool, ((s.retain n b).observe (bits g input)).elim 0 weight
  exact Finset.sum_congr rfl fun g _ => congrArg (fun o => Option.elim o 0 weight) (s.retain_observe_perm n h (bits g input))

variable {D m ne ns np oe : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] [Fintype S] {bits : P → ℕ} (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (binName : S → ℕ) (position : e.Entry → ℕ) (oldID : p.layout.Edge ↪ Fin oe)
    (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)
    (hin : ∀ v, (old v).incoming = incoming p.layout v) (loc : ∀ v, (old v).Local)
    (sorted : ∀ v, (cuts v).Perm (layerCuts e p bin perm binName positive first q v oldID edgeID portID))

local notation3 "G₀" => (output e p bin perm positive first q).layout
local notation3 "installed₀" => roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts
local notation3 "size₀" => roundSites_incoming e p bin perm positive first q binName position siteID edgeID portID old cuts

include hin loc sorted in
/-- All installed sparse state is local to its finite work and input extents. -/
theorem roundSites_local (v : (G₀).Site) : (installed₀ v).Local := by
  change SiteShape e p S at v
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · exact (old v).local_retain (loc v) (cuts v) _
      ((Layer.covers_perm (sorted v) (layer_covers e p bin perm binName positive first q v oldID edgeID portID)).castOld (hin v))
  · exact origin_local e p bin perm positive first q a siteID edgeID portID
  · exact terminal_local e p bin perm positive first q a siteID edgeID portID binName t
  · exact PaidSite.physical_local e p bin perm positive first q a i v edgeID portID position

variable (values : ℕ → K) (paid : ∀ i, values (position i) = e.entry i)
    (models : ∀ v, (old v).Models p.layout oldID portID v (hin v) (fieldWeight values) p.table)

include loc sorted paid models in
/-- Every retained and newly created site's actual program realizes exactly its
field-valued local factor after the full sum over its private auxiliary bits. -/
theorem roundSites_models (v : (G₀).Site) :
    (installed₀ v).Models G₀ edgeID portID v (size₀ v) (fieldWeight values) (output e p bin perm positive first q).table := by
  change SiteShape e p S at v
  rcases v with v | ⟨a,(_ | t | ⟨i,v⟩)⟩
  · intro z x
    exact ((old v).retain_value_perm (incoming G₀ (.inl v)) (sorted v) (fieldWeight values) _).trans
      (retained_models e p bin perm binName positive first q v oldID edgeID portID (old v) (hin v) (loc v)
        (fieldWeight values) (models v) z x)
  · exact origin_models e p bin perm positive first q a siteID edgeID portID (fieldWeight values) (by simp [fieldWeight])
  · exact terminal_models e p bin perm positive first q a siteID edgeID portID binName t (fieldWeight values) (by simp [fieldWeight])
  · exact PaidSite.models_birth e p bin perm positive first q a i v edgeID portID position values paid

end Packing.Inherited

end BorderVNP
end Computability
end OAI
