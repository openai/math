import OAI.Computability.BorderVNP.PackedSignFreeSites
import OAI.Computability.BorderVNP.PackedFlatCompilerRows
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms

/-! # Sign-free private factors along the true selected histories

The crossing identity's scalar is read through its reported entry ID. No
negative local multiplier is introduced by retaining a source program,
installing a paid site, subdividing a cable, or flattening the selected banks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (routes : N.WireRoutes) (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide routes).Edge ↪ Fin n)
    (portID : P ↪ Fin np)

/-- The selected original sites retain their one-copy factors, and each new
hop is a pure equality with an empty factor list. -/
theorem subdividePrivatePrograms_signFree (prior : Site.Programs N) (h : ∀ v, (prior v).program.SignFree)
    (z : (N.subdivide routes).Site) :
    (subdividePrivatePrograms N routes oldID newID portID prior z).program.SignFree := by
  rcases z with v | j
  · exact h v
  · intro fs hs
    exact False.elim (List.not_mem_nil hs)

end Packing.Inherited.Subdivision

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Shortening.CombiningStep
open Diagonal.ExternalSew Diagonal.CellEntries Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D m k d d' : ℕ} [NeZero D] {P I K B : Type} [Fintype P] [Fintype I] [Fintype B] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}
    (e : PaidIdentity K D m) (s : Stage m B d' child) (q : s.Index e)
    (old : ∀ j, Site.Programs (child j).pack.layout)
    {ns ne np : ℕ} (siteID : (s.result e q).pack.layout.Site ↪ Fin ns)
    (edgeID : (s.result e q).pack.layout.Edge ↪ Fin ne) (portID : (Fin k × P) ↪ Fin np)
    (seedName : ((I → Deck (d'+1)) × B) → ℕ) (position : e.Entry → ℕ)

namespace Stage

/-- At each retained or fresh site, the executable program on this attained
histogram uses only sign-free factors. -/
theorem privatePrograms_signFree (prior : ∀ j v, (old j v).program.SignFree)
    (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old siteID edgeID portID seedName position v).program.SignFree := by
  rw [s.privatePrograms_program e q old siteID edgeID portID seedName position v]
  exact roundSites_signFree e s.input s.label s.perm s.orient (0,false) q seedName position
    siteID edgeID portID _ _ (fun u => prior u.1 u.2) v

end Stage

namespace Program

variable {rounds : ℕ} {A : ℕ → Type*} {Bin : Fin rounds → Type} [∀ i, Fintype (Bin i)]
    {depth : ℕ → ℕ} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    {e} (F : Program (B := Bin) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- Every site of the true selected dense replay preserves the absence of a
local sign factor from the original independent banks. -/
theorem replayPrivatePrograms_signFree (n : ℕ) (hn : n ≤ rounds) (a : Leaves k (A 0) n)
    (initial : Site.Programs (parallelLeaves (fun x => (view 0 x).pack) n a).layout)
    (bottom : ∀ v, (initial v).program.SignFree) (q : (F.system.histories n hn a).Index) :
    ∀ v, (F.replayPrivatePrograms store rows number n hn a initial q v).program.SignFree :=
  F.replayPrivatePrograms_induction store rows number (fun _ s => s.SignFree)
    (fun i c q old h => (F.stage i c).privatePrograms_signFree e q old (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number h) n hn a initial bottom q

/-- Flattening the actual bank histories in their copy order retains sign-free
private factors at every returned site. -/
theorem flatPrivatePrograms_signFree (flat : Fin (k^rounds) → A 0)
    (initial : ∀ i, Site.Programs (view 0 (flat i)).pack.layout) (q : F.Hist flat)
    (base : ∀ i v, (initial i v).program.SignFree) :
    ∀ v, (F.flatPrivatePrograms store rows number flat initial q v).program.SignFree :=
  F.replayPrivatePrograms_signFree store rows number rounds le_rfl (leavesEquiv k _ rounds flat)
    (nestedPrivatePrograms _ _ flat initial)
    (nestedPrivatePrograms_forall (fun x => (view 0 x).pack) Site.SignFree _ flat initial base) q

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
