import OAI.Hierarchy.PhysicalTraceContraction
import OAI.Hierarchy.FactorBucketInputs

namespace OAI
/-! # Scheduling the repeated physical compressor in terminal archive order -/

namespace Hierarchy.TraceDistribution.Physical
open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open FactorPinIntervals
open scoped BigOperators Classical
noncomputable section

variable {F : Type} [Field F] [Fintype F] {k low w pc regs words S base fuel N : ℕ}
    (B : PhysicalStage.Block F) (hk : 2≤k+1)
    (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w) (s : ℕ) (fits : B.blockCharge*s≤k+1)

/-- Original physical lane carrying a source pin. Its numeric ordinal is computed by division. -/
abbrev bucketOrdinal (j : Fin S) : Fin (2^(k+1)) :=
  finFunctionFinEquiv (PairedCursor.owner (layout M t hF st) j).2

abbrev physicalPlan := (nativeRun B hk M t hF st s fits).plan

variable (h : (physicalPlan B hk M t hF st s fits).History) (archive : ((physicalPlan B hk M t hF st s fits).finish h).Site ≃ Fin N)

/-- Use the actual archive row ordinal of the physical ancestor, including the
word-labelled edge model of the repeated compressor. -/
def origin (j : Fin S) : Fin N :=
  archive ((physicalPlan B hk M t hF st s fits).destination h (PairedCursor.owner (layout M t hF st) j))

theorem origin_pair (i : ℕ) (hi : 2*i+1<S) :
    origin B hk M t hF st s fits h archive ⟨2*i,by omega⟩=
    origin B hk M t hF st s fits h archive ⟨2*i+1,hi⟩ :=
  congrArg archive (repeated_native_pair B hk M t hF st s fits h i hi)

def ordinalFactor (b : ((physicalPlan B hk M t hF st s fits).finish h).Boundary) (x : Fin S→Bool) (f : Fin N) : F :=
  let v := archive.symm f
  (physicalPlan B hk M t hF st s fits).cells h (seed B hk (layout M t hF st) x) v (((physicalPlan B hk M t hF st s fits).finish h).graph.atVertex b v)

theorem ordinalFactor_local (b : ((physicalPlan B hk M t hF st s fits).finish h).Boundary) (x y : Fin S→Bool) (f : Fin N)
    (equal : ∀ j, origin B hk M t hF st s fits h archive j=f → x j=y j) :
    ordinalFactor B hk M t hF st s fits h archive b x f=
      ordinalFactor B hk M t hF st s fits h archive b y f := by
  apply congrFun (repeated_local B hk (layout M t hF st) s fits h (archive.symm f) x y ?_)
  intro j atRow
  exact equal j ((congrArg archive atRow).trans (archive.apply_symm_apply f))

theorem ordinalFactor_prod (b : ((physicalPlan B hk M t hF st s fits).finish h).Boundary) (x : Fin S→Bool) :
    (∏ f, ordinalFactor B hk M t hF st s fits h archive b x f) =
      ∏ v, (physicalPlan B hk M t hF st s fits).cells h (seed B hk (layout M t hF st) x) v (((physicalPlan B hk M t hF st s fits).finish h).graph.atVertex b v) :=
  Equiv.prod_comp archive.symm (fun v =>
    (physicalPlan B hk M t hF st s fits).cells h (seed B hk (layout M t hF st) x) v
      (((physicalPlan B hk M t hF st s fits).finish h).graph.atVertex b v))

/-- Expansion of the real archive's descriptor visits exactly the owning input
bits, in their original order. -/
theorem ordinal_interval_bits (f : Fin N) :
    (intervalList (physicalPlan B hk M t hF st s fits) h (fun b : Fin (2^(k+1)) => (0,finFunctionFinEquiv.symm b))
      (archive.symm f)).flatMap (fun b => blockBits S (2*2^low) b.val)=
      intervalBits (origin B hk M t hF st s fits h archive) f := by
  let site : Fin (2^(k+1)) → PairedCursor.Site (k+1) := fun b => (0,finFunctionFinEquiv.symm b)
  apply expand_descriptors _ (by positivity) _ (bucketOrdinal M t hF st) (native_interval_index M t hF st)
  · exact (List.pairwise_lt_finRange _).filter _
  · intro j
    have own : site (bucketOrdinal M t hF st j)=PairedCursor.owner (layout M t hF st) j :=
      Prod.ext rfl (Equiv.symm_apply_apply finFunctionFinEquiv _)
    have move : (physicalPlan B hk M t hF st s fits).destination h (site (bucketOrdinal M t hF st j))=
        (physicalPlan B hk M t hF st s fits).destination h (PairedCursor.owner (layout M t hF st) j) := congrArg ((physicalPlan B hk M t hF st s fits).destination h) own
    refine (intervalList_mem (physicalPlan B hk M t hF st s fits) h site (archive.symm f) (bucketOrdinal M t hF st j)).trans ?_
    exact ⟨fun eqn => (congrArg archive (move.symm.trans eqn)).trans (archive.apply_symm_apply f),
      fun eqn => move.trans ((archive.symm_apply_apply _).symm.trans (congrArg archive.symm eqn))⟩

end
end Hierarchy.TraceDistribution.Physical

end OAI
