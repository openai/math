import OAI.Computability.BorderVNP.DiagonalSpecializedDenseSiteEpoch
import OAI.Computability.BorderVNP.PackedHistoryNormalizedEnriched

/-! # Field-specialized replay on the enriched public site machine

The branch states can contain an entire assigned public pin vector, its sparse
directory and auxiliary metadata. The replay follows the very program that reads
these states. Its indices are the actual stored histograms of that program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedSiteReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing PackedHistoryCircuit.Normalized
open scoped Classical BigOperators BorderVNP.Epoch.Cube
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
attribute [local instance] portFintype

universe u

variable {D m d exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E]
  [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
  {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {A : ℕ → Type u} {view : S.GeometricView d P bits A}
  {F : S.EnrichedProgram d view} {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution F input route)

/-- Transport leaf factors and unary positions from the original network through
the equality subdivision stored in this enriched public machine state. -/
noncomputable def installed (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout) :
    Tracked Team Param Gadget exp (view 0 (run.flat i)).pack.layout := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let out := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact out.tracked ((original.tracked t).subdivide (data.routes.routes S.radius))

/-- Reading the tagged values through the true subdivision gives the original
specialized tensor for each supplied free-port tuple. -/
theorem installed_tensor (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout)
    (values : Gadget → E) (x : Ports bits) :
    ((installed run i t).valued values).tensor x = (t.valued values).tensor x := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let out := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact (out.tracked_tensor _ values x).trans
    (((original.tracked t).subdivide_tensor (data.routes.routes S.radius) values x).trans
      (original.tracked_tensor t values x))

/-- The actual sparse output cable IDs determine the physical dense save on every
enriched transition. The extra data in a branch are retained by the true `F.advance`. -/
noncomputable def storage (save : F.SaveNames) : DenseReplay.Saved F :=
  fun i c q => by
    rw [save.stored i c q]
    exact Storage.dense _ (save.number i c q)

variable (save : F.SaveNames) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (t : ∀ i, Tracked Team Param Gadget exp (input i).layout)

/-- The specialized terminal on an actual enriched-history index, before any
ordinal conversion. The same index addresses the terminal motion and pin transcript. -/
noncomputable def term (q : F.Hist run.flat) :
    Tracked (Fin (S.fanIn^S.rounds) × Team) Param Gadget exp (flattenPack S.rounds (F.terminal run.flat q).pack).layout :=
  Replay.publicFlat F.system (fun n a => (view n a).pack.layout)
    (DenseReplay.move F y hy pos (storage save)) S.rounds le_rfl run.flat
    (fun i => installed run i (t i)) q

/-- The complete product of the supplied leaf values is obtained by summing over
the actual full enriched histories, with all public pin and directory data attached. -/
theorem sum_terms (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun z : Fin (S.fanIn^S.rounds) × P => bits z.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ q, ((term run save y hy pos t q).valued values).tensor x := by
  let leaf := fun i => installed run i (t i)
  refine Eq.trans (Finset.prod_congr rfl fun i _ =>
    (installed_tensor run i (t i) values (fun p => x (i,p))).symm) ?_
  exact Replay.publicFlat_sum F.system (fun n a => (view n a).pack.layout)
    (DenseReplay.move F y hy pos (storage save)) values (DenseReplay.move_exact F y hy pos (storage save) values lookup)
    S.rounds le_rfl run.flat leaf x

/-- Access the same terminal at the enumerated output ordinal, for clients
which operate on the public flat expansion. -/
noncomputable def ordinal (j : Fin run.expansion.terms) :
    Tracked (Fin (S.fanIn^S.rounds) × Team) Param Gadget exp (run.expansion.pack j).layout :=
  term run save y hy pos t (run.enum j)

/-- The finite output numbering preserves the entire enriched replay sum. -/
theorem sum_ordinals (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun z : Fin (S.fanIn^S.rounds) × P => bits z.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((ordinal run save y hy pos t j).valued values).tensor x :=
  (sum_terms run save y hy pos t values lookup x).trans
    (run.enum.sum_comp (fun q => ((term run save y hy pos t q).valued values).tensor x)).symm

end Diagonal.CellEntries.EnrichedSiteReplay

end BorderVNP
end Computability
end OAI
