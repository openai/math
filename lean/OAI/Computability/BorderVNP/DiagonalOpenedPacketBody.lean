import OAI.Computability.BorderVNP.DiagonalSignedRetainedPacket

/-! # The published packet body at the attained signed control cut -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM FiniteEvaluator Packing Packing.RoutingOutputs PackedHistoryCircuit

variable {w team offsets ctl live ports bundles b : ℕ} {sa : SignedTaskArena.Layout}
    (owner : Fin bundles → Fin sa.cube.cells) (headers : Fin bundles → Packing.BottomReports.BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {entry : Memory w}
local notation3 (prettyPrint := false) "frame" => readings pub 0
local notation3 (prettyPrint := false) "H" => sa.openInputs team (readings pub 0) offsets ctl live ports bundles b owner headers

/-- Every published packet word above the control table and below the
secondary cube header is unchanged at the return of the four signed
opening programs. No report or argument return is required. -/
theorem opened_body_from_publication (opened : Returns controls pub mac s entry)
    {initial written : ℕ → ℕ}
    (keep : CubeAllocation.HostRetention sa.cube frame initial written (readings entry))
    (ready : OpenSuffix.Ready H frame (readings entry) w) (place : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (above : frame+112 ≤ ctl) (j : ℕ) (lo : ctl+37 ≤ j) (hi : j<sa.cube.header.header) :
    readings opened.val.2.2 j=initial j := by
  have body := ((OpenSuffix.run H ready).sound opened.property).2
  exact (congrFun body j).trans ((sa.open_image_low owner headers place j (hi.trans_le sa.open_table_order.1)
    (by omega)).trans (keep.lower _ hi (by omega) (by omega)))

/-- The same control RAM also agrees with the pre-placement geometry RAM
throughout that interval. Private-slot overwrites precede the returned
region, and the compact raw directory fits below the geometry output. -/
theorem opened_body_from_geometry {origin cables cells entries rect desc gap next : ℕ}
    {geometry placed : Memory w} (rows : List Directory.Row)
    (slots : (privateLayout frame origin cables cells entries desc gap).Image (readings geometry) entries (readings placed))
    (low : frame+112 ≤ next) (space : next+7*rows.length ≤ origin)
    {written : ℕ → ℕ} (keep : CubeAllocation.HostRetention sa.cube frame
      (readings (Directory.ISA.publish placed frame next rows)) written (readings entry))
    (opened : Returns controls pub mac s entry)
    (ready : OpenSuffix.Ready H frame (readings entry) w) (place : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (control : ctl=controlsBase origin cables cells entries rect) (j : ℕ) (lo : ctl+37 ≤ j) (hi : j<sa.cube.header.header) :
    readings opened.val.2.2 j=readings geometry j := by
  subst ctl
  let base := controlsBase origin cables cells entries rect
  have above : origin ≤ base := by dsimp only [base,controlsBase,bases]; omega
  have after := opened_body_from_publication owner headers opened keep ready place (by omega) j lo hi
  have raw := directoryPublished_control (live:=rect) rows slots low space (j-base)
  change Directory.ISA.publish placed frame next rows (base+(j-base))=geometry (base+(j-base)) at raw
  have split : base+(j-base)=j := by change base+37 ≤ j at lo; omega
  rw [split] at raw
  exact after.trans (congrArg Fin.val raw)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
