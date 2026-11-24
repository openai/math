import OAI.Computability.VPVNP.PairSimulationEntryWork
import OAI.Computability.VPVNP.ShrinkHistory
import OAI.Computability.VPVNP.RefreshHistory

/-!
# Map work at selected shrink and refresh records

The degree in an actual map record is exactly the number of copies in its
motif call. The input coordinates are read from independently supplied old,
new and absorbed half-wire arguments. No global consistency of those
arguments is required.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel MotifConversion

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

section Shrink

variable {V H Tag L : Type} {d c d' pad : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ) (sel : ∀ m, P.ShrinkChoice number w B.shrink m)

set_option maxHeartbeats 1600000 in
-- Elaborating the packed resident types reduces the full six-party layout.
/-- Use the recorded six-party row's own demand and supply fields. The
result has the exact degree recorded by the chosen layout. -/
noncomputable def recordedShrinkCall (hc : 2 ≤ c) (hd : 0 < d) (l : Bool) (subdiv : Fin 4 → ℕ)
    {next : Equiv.Perm (V × Tag)} (I : P.ShrinkIndex l subdiv next d' pad)
    (hsub : ∀ t, 0 < subdiv t) (site : (V × Tag) × L) (m : P.ResidentMap l site)
    (x : Placed (P.shrinkPlace l) (P.oldWireNetwork w).Half site)
    (h : Placed (P.shrinkInternalOwner l) (internalLabel
      (fun m ↦ P.shrinkSupplyWidths number w B.shrink m (sel m)) l) site)
    (z : (P.shrinkOutput l subdiv (fun m t ↦
      P.shrinkSupplyWidths number w B.shrink m (sel m) (l, t)) I).Half site) :
    MapInvocation B ((P.shrinkSiteRecords number w B.shrink sel l site).degree m) :=
  .shrink ⟨P.shrinkDemandWidths number w m.1.1, (sel m.1.1).val, m.1.2,
    P.shrinkLocalDemandArg hc hd number order w l m.1.1 m.1.2 (m.2.symm ▸ x),
    P.shrinkLocalSupplyArg l subdiv _ I hsub m.1.1 m.1.2 (m.2.symm ▸ h) (m.2.symm ▸ z)⟩ le_rfl

end Shrink

open Refresh DegreeRefresh MotifDemandPadding MotifSelector

section Refresh

variable {g : ℕ} (X : State S.portExponent (S.portExponent + g))
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh)

/-- At a refreshed port, only row zero is a motif call. The remaining two
rows test equalities and perform no parameter lookup. -/
noncomputable def recordedRefreshCall (v : (X.Base × Fin (2 ^ S.portExponent)) × BitWord g)
    (m : Fin 3)
    (x : HalfBits tieSource tieTarget (blockDemandWidths (splitSlots X)
      (bitWordFinEquiv _) (splitWidths X) (v.1.1, v.2)) v.1.2)
    (y : Half S.portSupply (fun e ↦ MotifSelector.Word (supplyWidths B.refresh
      (blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) (v.1.1, v.2))
      (choice (v.1.1, v.2)).val e)) v.1.2) :
    MapInvocation B ((refreshLocalRecords X S.graph (Nat.two_pow_pos _)
      (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
      (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2 choice v).degree m) := by
  by_cases h : m = 0
  · subst m
    exact .refresh ⟨_, (choice (v.1.1, v.2)).val, v.1.2, x, y⟩ le_rfl
  · exact .noLookup

end Refresh

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
