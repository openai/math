import OAI.Computability.BorderVNP.DiagonalFlatReplay
import OAI.Computability.BorderVNP.ShortenSiteExecution

/-! # Actual site-to-site epochs acting on conditioned parameter polynomials -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing Catalog
open scoped Classical BigOperators BorderVNP.Epoch.Cube

private def sameStorage {D : ℕ} {P : Type*} {bits : P → ℕ} {N M : Network D P bits}
    (eqn : N = M) : Storage N M := eqn ▸ Storage.id N

variable {D m rounds k : ℕ} [NeZero D] {E Team Param Gadget P : Type} [Field E]
    [Fintype Team] [Fintype Param] [Fintype P] {exp : ℕ} {bits : P → ℕ} {e : PaidIdentity E D m}
    {h H ν : ℝ} {path : StagePath rounds e (Cube D) h H ν} {C : Fin rounds → ℕ}
    {last high : ℕ} {hk : 0 < k} {machine : SiteMachine path C last high hk P bits}
    {low : ℕ} {L weight error A Cout : ℝ} {cap : ℕ} {hh : 0 < h}
    {input : Fin (k^rounds) → Pack D P bits E} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
    (run : SiteExecution (low := low) machine hh input route weight error A Cout cap)

namespace SiteReplay

/-- The leaf tags travel from the actual input pack, through its precise
subdivision, onto the prepared state selected by this site execution. -/
noncomputable def installed (i : Fin (k^rounds)) (t : Tracked Team Param Gadget exp (input i).layout) :
    Tracked Team Param Gadget exp (run.flat i).val.pack.layout := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let stored := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact stored.tracked ((original.tracked t).subdivide (data.routes.routes h))

/-- The genuine equality factors add one assignment per carried wire word. -/
theorem installed_tensor {R : Type*} [CommSemiring R] (i : Fin (k^rounds)) (t : Tracked Team Param Gadget exp (input i).layout)
    (values : Gadget → R) (x : Ports bits) :
    ((installed run i t).valued values).tensor x = (t.valued values).tensor x := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let stored := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact (stored.tracked_tensor _ values x).trans
    (((original.tracked t).subdivide_tensor (data.routes.routes h) values x).trans
      (original.tracked_tensor t values x))

/-- Direct storage in the site machine leaves all wire labels intact. -/
noncomputable def storage (machine : SiteMachine path C last high hk P bits) : ProgramStorage machine.F :=
  ProgramStorage.ofLayoutEq machine.F fun i c q =>
    congrArg (fun p => p.pack.layout) (machine.stored i c q).symm

variable (pos : e.Entry → Gadget) (t : ∀ i, Tracked Team Param Gadget exp (input i).layout)

/-- The actual flat output and its unary readback at the profile chosen by
the geometric execution's own enumeration. -/
noncomputable def term (j : Fin run.expansion.terms) :
    Tracked (Fin (k^rounds) × Team) Param Gadget exp (run.expansion.pack j).layout :=
  Replay.terminal machine.F (storage machine) pos run.flat
    (fun i => installed run i (t i)) (run.enum j)

/-- Every attained site epoch, including its equality subdivisions and
final rounding, acts on arbitrary conditioned source entries and preserves
their polynomial sum on the exact same physical networks as (6.1). -/
theorem sum_terms (values : Gadget → E) (lookup : ∀ i, values (pos i) = e.entry i)
    (x : Ports (fun p : Fin (k^rounds) × P => bits p.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((term run pos t j).valued values).tensor x := by
  let leaf := fun i => installed run i (t i)
  refine Eq.trans (Finset.prod_congr rfl fun i _ => (installed_tensor run i (t i) values (fun p => x (i,p))).symm) ?_
  refine (Replay.terminal_sum machine.F (storage machine) pos values lookup run.flat leaf x).trans ?_
  exact (run.enum.sum_comp (fun q => ((Replay.terminal machine.F (storage machine) pos run.flat leaf q).valued values).tensor x)).symm

end SiteReplay
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
