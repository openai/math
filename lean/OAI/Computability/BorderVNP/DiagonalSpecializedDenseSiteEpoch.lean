import OAI.Computability.BorderVNP.DiagonalSpecializedSiteEpoch
import OAI.Computability.BorderVNP.DiagonalSpecializedDense
import OAI.Computability.BorderVNP.ShortenDenseSiteEpoch
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords

/-! # Cross-field replay on the physical dense site epoch

The reference field determines every sorted cable slot, sample selector and minimizing
terminal motion. Independent input tags and a relation-preserving specialization of
the crossing entries are installed on those same layouts. The summation uses the
execution's own enumeration of dense histories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.DenseSiteReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing
open PackedHistoryCircuit.Normalized
open scoped Classical BigOperators BorderVNP.Epoch.Cube
open private sameStorage from OAI.Computability.BorderVNP.DiagonalSiteExecution
attribute [local instance] portFintype

variable {D m d exp : ℕ} [NeZero D] {K E Team Param Gadget P : Type} [Field K] [Field E]
  [Fintype Team] [Fintype Param] [Fintype P] {bits : P → ℕ}
  {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {M : PackedHistoryCircuit.Normalized.SiteMachine S d P bits}
  {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : PackedHistoryCircuit.Normalized.SiteExecution S M input route)

/-- Install independent scalar tags through the equality subdivision of the actual leaf. -/
noncomputable def installed (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout) :
    Tracked Team Param Gadget exp (run.flat i).val.pack.layout := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let saved := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact saved.tracked ((original.tracked t).subdivide (data.routes.routes S.radius))

/-- The subdivision preserves the evaluated leaf polynomial, for every external assignment. -/
theorem installed_tensor (i : Fin (S.fanIn^S.rounds)) (t : Tracked Team Param Gadget exp (input i).layout)
    (values : Gadget → E) (x : Ports bits) :
    ((installed run i t).valued values).tensor x = (t.valued values).tensor x := by
  let data := run.initialSites i
  let original := sameStorage (congrArg Pack.layout (run.originalPack i).symm)
  let saved := sameStorage (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact (saved.tracked_tensor _ values x).trans
    (((original.tracked t).subdivide_tensor (data.routes.routes S.radius) values x).trans
      (original.tracked_tensor t values x))

/-- The public stage sends each edge to the dense rank of its actual stored row number. -/
noncomputable def storage (M : PackedHistoryCircuit.Normalized.SiteMachine S d P bits) : DenseReplay.Saved M.F :=
  fun i c q => by
    change Storage ((M.F.stage i c).result e q).pack.layout (M.F.advance i c q).val.pack.layout
    rw [M.stored i c q]
    exact Storage.dense _ (M.after i c (M.F.stage i c) q).number

variable (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (t : ∀ i, Tracked Team Param Gadget exp (input i).layout)

/-- Tagged specialized summand at the finite ordinal of the true stored and flattened
reference site layout, preserving the same row-major external ports and unary labels. -/
noncomputable def term (j : Fin run.expansion.terms) :
    Tracked (Fin (S.fanIn^S.rounds) × Team) Param Gadget exp (run.expansion.pack j).layout :=
  Replay.publicFlat M.F.system (fun _ a => a.val.pack.layout)
    (DenseReplay.move M.F y hy pos (storage M)) S.rounds le_rfl run.flat
    (fun i => installed run i (t i)) (run.enum j)

/-- Evaluate the actual finite set of stored histories on independent tagged leaves
in the specialization field. No geometric choices are made over that field. -/
theorem sum_terms (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun p : Fin (S.fanIn^S.rounds) × P => bits p.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((term run y hy pos t j).valued values).tensor x := by
  let leaf := fun i => installed run i (t i)
  refine Eq.trans (Finset.prod_congr rfl fun i _ => (installed_tensor run i (t i) values (fun p => x (i,p))).symm) ?_
  refine (Replay.publicFlat_sum M.F.system (fun _ a => a.val.pack.layout)
    (DenseReplay.move M.F y hy pos (storage M)) values (DenseReplay.move_exact M.F y hy pos (storage M) values lookup)
    S.rounds le_rfl run.flat leaf x).trans ?_
  exact (run.enum.sum_comp (fun q => ((Replay.publicFlat M.F.system (fun _ a => a.val.pack.layout)
    (DenseReplay.move M.F y hy pos (storage M)) S.rounds le_rfl run.flat leaf q).valued values).tensor x)).symm

variable (values : Gadget → E)

/-- Use the original site coordinates on the independently valued leaf. -/
noncomputable def inputRoutes (i : Fin (S.fanIn^S.rounds)) :
    SiteRoutes ((t i).valued values) (Cube D) (S.high d) S.budget :=
  (route i).withTables ((t i).valued values).table

/-- Use the reference minimizing motion and actual stored endpoint addresses on the
specialized output. Only the scalar tables have been installed from the specialization. -/
noncomputable def outputRoutes (j : Fin run.expansion.terms) :
    SiteRoutes ((term run y hy pos t j).valued values) (Cube D) (d+1) S.budget :=
  (run.expansion.routes j).withTables ((term run y hy pos t j).valued values).table

/-- Width and spatial concentration are measured on the same true terminal routes. -/
theorem output_measurements (j : Fin run.expansion.terms) :
    let r := outputRoutes run y hy pos t values j
    let shadow := M.F.terminal run.flat (run.enum j)
    r.nonlocalWidth = (run.expansion.routes j).nonlocalWidth ∧
      r.incidenceConcentration = (run.expansion.routes j).incidenceConcentration ∧
      r.nonlocalWidth ≤ S.finalWidth*shadow.length ∧ r.incidenceConcentration ≤ S.finalConcentration*shadow.concentration :=
  ⟨rfl,rfl,(run.out (run.enum j)).width_le,(run.out (run.enum j)).concentration_le⟩

/-- The reference potential inequality applies without changing the density order,
calibrated saving, selected motion or the absolute epoch level. -/
theorem potential_bound (j : Fin run.expansion.terms) :
    (outputRoutes run y hy pos t values j).potential S.weight / (S.fanIn:ℝ)^S.rounds ≤
      maximumLeaf S.positiveFanIn id (fun i => (inputRoutes (route := route) t values i).potential S.weight)/2 +
        S.error*Fintype.card (Cube D → Deck (S.high d+1)) := run.expansion.bound j

/-- Both sparse and expanded input record fields obey the same calibrated bound on
the identical output enumeration and physical row order. -/
theorem records_bound (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (cap : ℕ)
    (hm : ∀ i u, localRecords ((t i).valued values).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove (S.high d) ((inputRoutes (route := route) t values i).origin v) = u) ≤ cap) :
    ∀ (j : Fin run.expansion.terms) u,
      1+localRecords ((term run y hy pos t j).valued values).layout ex
        (run.expansionRecords fields j).prior (run.expansionRecords fields j).payload
        (fun v => reduceMove (d+1) ((outputRoutes run y hy pos t values j).origin v) = u) ≤
        S.recordFactor*(1+cap) :=
  run.expansionRecords_bound fields ex cap hm

end Diagonal.CellEntries.DenseSiteReplay

end BorderVNP
end Computability
end OAI
