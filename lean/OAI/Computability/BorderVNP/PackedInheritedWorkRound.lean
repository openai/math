import OAI.Computability.BorderVNP.PackedInheritedExtent
import OAI.Computability.BorderVNP.PackedInheritedWorkRouting
import OAI.Computability.BorderVNP.PackedBankRoundSites
import OAI.Computability.BorderVNP.PackedInheritedPaidEmit

/-! # Arithmetic widths of the actual selected sewing step

The previous full extents are the work fields of retained sites. Origin,
terminal and paid sites instead receive the intrinsic work of their accepted
histogram. The same fixed circuit works for every physical stage and every
selected branch in its rectangles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep Shortening.SeedIntervals
open InheritedProfile BankJoint ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D m s n ne np w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] (seed : A ↪ Fin n)
variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
variable (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
variable (q : Counts e p bin perm) (binName : A → ℕ) (position : e.Entry → ℕ)
variable (oldID : p.layout.Site ↪ Fin s)
local notation3 "G₀" => (output e p bin perm positive first q).layout
variable (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

local notation3 "installed" => roundSites e p bin perm positive first q binName position (siteRows e p oldID seed)
  edgeID portID old cuts

/-- For every physical site, its program's literal work prefix is exactly the
routed previous extent or the template work computed from this histogram. -/
theorem installed_work (v : (G₀).Site) : (installed v).work =
    Sum.elim (fun t => (old t).size) (fun z => intrinsicWork e (blocks p.layout bin perm m z.1) (q z.1).val z.2) v := by
  rcases v with t | ⟨a,⟨⟩ | t | ⟨i,t⟩⟩
  · rfl
  · exact (work_profile e _ _ (profileCounts_total e _ q a) (.inl ())).symm
  · exact (work_profile e _ _ (profileCounts_total e _ q a) (.inr t)).symm
  · exact (PaidSite.raw_work e i t _ _).symm

variable {σ : Type*} [Fintype σ] (prev : Frame σ (Fin s × Fin w))
variable (counts : Frame σ (A × Option (Fin e.count) × Fin w))

/-- Construct the actual work table using only the previous extent words and
the current matched/profile count words. The gates precede every choice of
physical pack, saved histogram, cut ordering and installed site program. -/
theorem exists_round :
    ∃ f : Frame σ (Fin (siteCapacity e s n) × Fin w),
      f.size ≤ prev.size + counts.size + 2 + Fintype.card A * birthNodes e * (100*(w+1)^2) ∧
      ∀ {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
        (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
        (q : Counts e p bin perm) (binName : A → ℕ) (position : e.Entry → ℕ) (oldID : p.layout.Site ↪ Fin s)
        {ne np : ℕ} (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
        (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice) (x : σ → Bool),
        let state := roundSites e p bin perm positive first q binName position (siteRows e p oldID seed)
          edgeID portID old cuts
        Covers oldID (fun v => (old v).size) prev x →
        (∀ a i, value (fun j => counts.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val) →
        (∀ v, (state v).size < 2^w) → Covers (siteRows e p oldID seed) (fun v => (state v).work) f x := by
  obtain ⟨born,hs,hborn⟩ := exists_birth e counts
  refine ⟨route e seed prev born,?_,?_⟩
  · have h := route_size e seed prev born
    omega
  · intro P _ bits p bin perm positive first q binName position oldID ne np edgeID portID old cuts x state hp hc room
    let newWork (a : A) (v : TemplateSite e) := intrinsicWork e (blocks p.layout bin perm m a) (q a).val v
    have hwork (v) : (state v).work = Sum.elim (fun t => (old t).size) (fun z => newWork z.1 z.2) v :=
      installed_work e seed p bin perm positive first q binName position oldID edgeID portID old cuts v
    have hnew (a : A) (v : TemplateSite e) : value (fun j => born.eval x ((a,v),j)) = newWork a v := by
      have h := hborn x a v
      dsimp only [Function.comp_def] at h
      simp only [hc,Option.elim_none,Option.elim_some] at h
      apply h
      have hwork' := hwork (.inr ⟨a,v⟩)
      change (state (.inr ⟨a,v⟩)).work = newWork a v at hwork'
      exact hwork'.symm.trans_lt ((Nat.le_add_right _ _).trans_lt (room (.inr ⟨a,v⟩)))
    exact (funext hwork).symm ▸ route_covers e seed prev born p oldID x (fun t => (old t).size) newWork hp hnew

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
