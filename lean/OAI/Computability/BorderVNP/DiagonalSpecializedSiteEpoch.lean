import OAI.Computability.BorderVNP.DiagonalSiteExecution
import OAI.Computability.BorderVNP.DiagonalSpecializedFlatReplay
import OAI.Computability.BorderVNP.ShortenEpochRoundExecutionRecords

/-! # Cross-field replay at the site epoch boundary

The reference execution supplies the geodesic equality subdivisions, the
chosen histories, and their final integral site routes. The specialized
crossing entries and independent leaf tags determine the tensors on those
very layouts. In particular the field of interpretation may be selected
after the geometric constants and program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open Shortening Crossing

/-- Install arbitrary tables of another scalar type on a site pack. All integral
site labels, active cables, allowed moves and endpoint alignments are preserved. -/
def withTables {D d : ℕ} {I P R S : Type*} [Fintype I] {bits : P → ℕ}
    {p : Pack D P bits R} {L : ℝ} (r : SiteRoutes p I d L) (t : p.layout.Tables S) :
    SiteRoutes (⟨p.layout,t⟩ : Pack D P bits S) I d L where
  origin := r.origin
  active := r.active
  step := r.step
  aligned := r.aligned

end Cover.SiteRoutes

namespace Diagonal.CellEntries.CrossSiteReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing Catalog
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m rounds k : ℕ} [NeZero D] {K E Team Param Gadget P : Type} [Field K] [Field E]
    [Fintype Team] [Fintype Param] [Fintype P] {exp : ℕ} {bits : P → ℕ} {e : PaidIdentity K D m}
    {h H ν : ℝ} {path : StagePath rounds e (Cube D) h H ν} {C : Fin rounds → ℕ}
    {last high : ℕ} {hk : 0 < k} {machine : SiteMachine path C last high hk P bits}
    {low : ℕ} {L weight error A Cout : ℝ} {cap : ℕ} {hh : 0 < h}
    {input : Fin (k^rounds) → Pack D P bits K} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
    (run : SiteExecution (low := low) machine hh input route weight error A Cout cap)
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (t : ∀ i, Tracked Team Param Gadget exp (input i).layout)

/-- The complete specialized tagged summand on the exact chosen site histogram,
including the given input subdivision and row-major flattening of external bits. -/
noncomputable def term (j : Fin run.expansion.terms) :
    Tracked (Fin (k^rounds) × Team) Param Gadget exp (run.expansion.pack j).layout :=
  Replay.specializedTerminal machine.F (SiteReplay.storage machine) y hy pos run.flat
    (fun i => SiteReplay.installed run i (t i)) (run.enum j)

/-- Each supplied tuple of external bits gives the same formal parameter polynomial
after summing all reference histograms, in the field of the chosen specialization. -/
theorem sum_terms (values : Gadget → E) (lookup : ∀ i, values (pos i) = y i)
    (x : Ports (fun p : Fin (k^rounds) × P => bits p.2)) :
    (∏ i, ((t i).valued values).tensor (fun p => x (i,p))) =
      ∑ j, ((term run y hy pos t j).valued values).tensor x := by
  let leaf := fun i => SiteReplay.installed run i (t i)
  refine Eq.trans (Finset.prod_congr rfl fun i _ =>
    (SiteReplay.installed_tensor run i (t i) values (fun p => x (i,p))).symm) ?_
  refine (Replay.specializedTerminal_sum machine.F (SiteReplay.storage machine) y hy pos values
    lookup run.flat leaf x).trans ?_
  exact (run.enum.sum_comp (fun q => ((Replay.specializedTerminal machine.F (SiteReplay.storage machine)
    y hy pos run.flat leaf q).valued values).tensor x)).symm

variable (values : Gadget → E)

/-- The true original site routing on the interpreted independent leaf entries. -/
noncomputable def inputRoutes (i : Fin (k ^ rounds)) :
    SiteRoutes ((t i).valued values) (Cube D) high L :=
  (route i).withTables ((t i).valued values).table

/-- The same final flattening and site rounding on the specialized summand. -/
noncomputable def outputRoutes (j : Fin run.expansion.terms) :
    SiteRoutes ((term run y hy pos t j).valued values) (Cube D) low L :=
  (run.expansion.routes j).withTables ((term run y hy pos t j).valued values).table

/-- Both final geometric measurements apply on the exact same public histories.
The transported routes give the reference rounding's charged width and incidence
concentration, with its original individual upper bounds. -/
theorem output_measurements (j : Fin run.expansion.terms) :
    let r := outputRoutes run y hy pos t values j
    let shadow := machine.F.terminal run.flat (run.enum j)
    r.nonlocalWidth = (run.expansion.routes j).nonlocalWidth ∧
      r.incidenceConcentration = (run.expansion.routes j).incidenceConcentration ∧
      r.nonlocalWidth ≤ A * shadow.length ∧ r.incidenceConcentration ≤ Cout * shadow.concentration :=
  ⟨rfl,rfl,(run.out (run.enum j)).width_le,(run.out (run.enum j)).concentration_le⟩

/-- Equation (6.1) on the actual reference routing and the actual tagged output,
without changing the selected depth, threshold, histograms or constants. -/
theorem potential_bound (j : Fin run.expansion.terms) :
    (outputRoutes run y hy pos t values j).potential weight / (k : ℝ)^rounds ≤
      maximumLeaf hk id (fun i => (inputRoutes (route := route) t values i).potential weight) / 2 +
        error * Fintype.card (Cube D → Deck (high+1)) := run.expansion.bound j

/-- Every specified input record follows the original true histogram into the
specialized flat output. Both descriptor and expanded counting modes retain
the same uniform per-tile bound, for arbitrary input metadata. -/
theorem records_bound (hdepth : path.depths last high 0 = high)
    (fields : ∀ i, RecordData (input i).layout) (ex : Bool) (M : ℕ)
    (hm : ∀ i u, localRecords ((t i).valued values).layout ex (fields i).prior (fields i).payload
      (fun v => reduceMove high ((inputRoutes (route := route) t values i).origin v) = u) ≤ M) :
    ∀ (j : Fin run.expansion.terms) u,
      1 + localRecords ((term run y hy pos t j).valued values).layout ex
        (run.expansionRecords fields j).prior (run.expansionRecords fields j).payload
        (fun v => reduceMove low ((outputRoutes run y hy pos t values j).origin v) = u) ≤
        epochRecordFactor (Cube D) L h (fun i => C i*k) cap * (1+M) :=
  run.expansionRecords_bound hdepth fields ex M hm

end Diagonal.CellEntries.CrossSiteReplay

end BorderVNP
end Computability
end OAI
