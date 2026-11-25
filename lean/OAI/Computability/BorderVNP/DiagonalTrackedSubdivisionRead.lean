import OAI.Computability.BorderVNP.DiagonalTrackedPowerRead

/-! # Reading the retained power bit at its actual subdivision endpoint -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing Packing.Inherited PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
attribute [local instance] portFintype
set_option maxHeartbeats 1300000

variable {D exp : ℕ} {P Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    {bits : P → ℕ} {N : Network D P bits}

/-- Read the first hop at the retained source, including loops, and the final hop
at the retained destination. Other edges do not enter the specified local table. -/
noncomputable def PowerInput.beforeSubdivision (route : Network.WireRoutes N) (v : N.Site)
    (x : PowerInput (N.subdivide route)) : PowerInput N :=
  ⟨fun e => if N.src e = v then x.edges ⟨e,0⟩ else x.edges ⟨e,Fin.last _⟩,x.ports⟩

/-- Subdivision reads the actual endpoint bit on either outcome of the chosen power slot. -/
theorem Tracked.subdivide_power_read (t : Tracked Team Param Gadget exp N) (route : Network.WireRoutes N)
    (w : PowerSlot Team Param exp) (x : PowerInput (N.subdivide route)) :
    (t.subdivide route).powerRead w x = t.powerRead w (x.beforeSubdivision route (t.words.site w)) := by
  let v := t.words.site w
  let edge := fun u : Incident N v => (x.beforeSubdivision route v).edges u.val
  let chosen := t.words.selected v edge (fun p => x.ports p.val) w
  have yes (b : Bool) : decide ((if b then (1 : ℕ) else 0) ≠ 0) = b := by cases b <;> rfl
  change decide ((if t.words.selected v _ (fun p => x.ports p.val) w then (1 : ℕ) else 0) ≠ 0) = chosen
  rw [yes]
  apply congrArg (fun a => t.words.selected v a (fun p => x.ports p.val) w)
  funext u
  by_cases h : N.src u.val = t.words.site w <;> simp [edge,PowerInput.beforeSubdivision,v,h] <;> rfl

namespace EnrichedSiteReplay

universe u

variable {m d : ℕ} [NeZero D] {K : Type} [Field K] [Fintype P] {e : PaidIdentity K D m}
  {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {A : ℕ → Type u} {view : S.GeometricView d P bits A}
  {F : S.EnrichedProgram d view} {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution F input route)

/-- Undo the equality transports surrounding the actual installed subdivision
and read at the corresponding original input site. -/
noncomputable def installedPowerInput (i : Fin (S.fanIn^S.rounds)) (v : (input i).layout.Site)
    (x : PowerInput (view 0 (run.flat i)).pack.layout) : PowerInput (input i).layout :=
  let data := run.initialSites i
  let orig := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let out := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  orig.powerInput ((out.powerInput x).beforeSubdivision (data.routes.routes S.radius) (orig.site v))

theorem installed_power_read (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout)
    (w : PowerSlot Team Param exp) (x : PowerInput (view 0 (run.flat i)).pack.layout) :
    (installed run i t).powerRead w x = t.powerRead w (installedPowerInput run i (t.words.site w) x) := by
  let data := run.initialSites i
  let orig := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let out := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  let r := data.routes.routes S.radius
  exact (out.powerRead ((orig.tracked t).subdivide r) w x).trans
    (((orig.tracked t).subdivide_power_read r w (out.powerInput x)).trans (orig.powerRead t w _))

end EnrichedSiteReplay
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
