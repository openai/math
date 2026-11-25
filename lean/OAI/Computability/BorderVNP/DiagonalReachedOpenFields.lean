import OAI.Computability.BorderVNP.DiagonalCandidateReportedFrame

/-! # Reading the original writer frame from its own reached opening -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM BorderVNP.Cube RoutingISA RoutingISA.Evaluator Packing BottomReports
open RoutingISA.Evaluator.SignedPrep FiniteEvaluator DiagonalTallyCellReports DiagonalTallyAllocation

variable {w team base ctl offsets live ports bundles b actual : ℕ} (t : SignedTaskArena.Layout)
    (owner : Fin bundles → Fin t.cube.cells) (headers : Fin bundles → BundleHeader)
    {supply : Fin t.cube.cells → ℕ} {input out : ℕ → ℕ}
local notation3 (prettyPrint := false) "H" => t.openInputs team base offsets ctl live ports bundles b owner headers

/-- The original writer frame has the very fields used by its returning
bundle and cell-control scans. Each such low word is retained through the
host scatter and the bundle table writes. -/
theorem FrozenControlEntry.writerOpenFields
    (stage : FrozenControlEntry t H base actual ctl offsets w supply input out) :
    t.OpenFields team base offsets ctl live ports bundles input := by
  have ready : OpenSuffix.Ready H base out w := stage.frame ▸ stage.ready
  let posted := (H).bundleImage base out
  have frameLow (i : ℕ) (small : i<112) (a13 : i≠13) (a46 : i≠46) :
      input (base+i)=posted (base+i) := by
    have top : base+i<t.cube.header.header := by have := stage.retained.primary; omega
    exact (stage.retained.lower _ top (by omega) (by omega)).symm.trans
      (t.open_bundle_low owner headers stage.placement _ (top.trans_le t.open_table_order.1)).symm
  have label (i : Fin 100) (n13 : i.val≠13) (n46 : i.val≠46) :
      input (base+i.val)=posted (base+i.val) := frameLow _ (by have := i.isLt; omega) n13 n46
  have atZero : input base=posted base := by simpa only [Nat.add_zero] using frameLow 0 (by decide) (by decide) (by decide)
  obtain ⟨cur,cellCount,banks,ends,cables,liveBase,portsCount,ctrl⟩ := ready.fields.frame
  have count : input (base+66)=bundles := by
    have top : base+66<t.cube.header.header := by have := stage.retained.primary; omega
    have dest := CubeAllocation.host_dest t.cube base out stage.placement.pointer stage.placement.bank stage.placement.ends
    have host : OpenSuffix.hostImage base out (base+66)=out (base+66) :=
      HostScatter.Layout.prefix_outside _ _ _ _ (fun i hi side own =>
        .inl ((top.trans_le t.open_table_order.1).trans_le (dest i hi side own).1))
    exact (stage.retained.lower _ top (by omega) (by omega)).symm.trans (host.symm.trans ready.bundleLoaded.2.2.1)
  refine ⟨atZero.trans cur,(label 15 (by decide) (by decide)).trans cellCount,count,
    (label 72 (by decide) (by decide)).trans banks,(label 87 (by decide) (by decide)).trans ends,
    (label 7 (by decide) (by decide)).trans cables,(label 65 (by decide) (by decide)).trans liveBase,?_,
    (label 92 (by decide) (by decide)).trans ctrl⟩
  exact (congrArg₂ Nat.mul (label 1 (by decide) (by decide)) (label 67 (by decide) (by decide))).trans portsCount

end TeamContraction

end BorderVNP
end Computability
end OAI
