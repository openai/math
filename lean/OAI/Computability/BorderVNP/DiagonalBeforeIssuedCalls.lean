import OAI.Computability.BorderVNP.DiagonalIssuedDispatch
import OAI.Computability.BorderVNP.DiagonalSupportedIssuedFacts
import OAI.Computability.BorderVNP.DiagonalSupportedIssuedSource

/-! # The physical owner and cell facts kept with a pre-continuation sparse source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.CoreDirectory

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open RoutingISA RoutingISA.Evaluator RoutingISA.CellDispatch DiagonalTallyCellReports CellMacro.Generator
open scoped Classical

variable {D cn cd cb ch cK sym R : ℕ} {P X Raw Hist : Type} [Fintype P] {bits : P → ℕ}
    {N : Hist → Network D P bits} {blocks : Hist → ℕ} (B : ∀ q, CoreDirectory (N q) cn cd (blocks q) cb ch cK R)
    (pin : Raw → Ports bits) (reported : ∀ q,Fin (B q).siteRows → ℕ)
    (bundles : ∀ q, Fin (B q).cells → List Bundle)
    (shape : Raw → (q : Hist) → (B q).Route sym → Fin (R+1) → ReportLayout)
    (received : ∀ i q v, ReceivedRows (shape i q v) (B q).cells)

local notation3 (prettyPrint := false) "src(" i "," q "," v "," z ")" =>
  (received i q v).assigned (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) (Subtype.val v) z
local notation3 (prettyPrint := false) "order(" i "," q "," v "," z ")" =>
  (received i q v).physicalReportEquiv (N q) (B q).cell (B q).siteID (B q).edgeID (B q).portID (B q).programs (B q).owners
    (B q).slot (pin i) (reported q) (bundles q) (Subtype.val v) z (received i q v).cells (fun _ => rfl)


open RoutingISA.CompactMachine VPVNP.BurstRAM
set_option maxHeartbeats 1000000
set_option maxRecDepth 4500
variable {dims digits : ℕ}
    (preparation : PreparedFields Raw Hist (Fin ((R+1)*dims*digits) → Bool)
      (fun q => (B q).Route sym) (Proposals B shape received))
local notation3 (prettyPrint := false) "input" => preparation.1
local notation3 (prettyPrint := false) "h₀" => preparation.2.1
local notation3 (prettyPrint := false) "v₀" => preparation.2.2.1
local notation3 (prettyPrint := false) "rc" => received input h₀ v₀
local notation3 (prettyPrint := false) "K₀" => B h₀
local notation3 (prettyPrint := false) "physical" => order(input,h₀,v₀,(fun _ _ => false)) preparation.2.2.2.2

/-- Local observations before selecting the private continuation. Both the owner
column and the logical cell refer to the same original routed RAM and report. -/
structure IssuedReceipt (u : Fin (R+1)) {w : ℕ} (pub : Arg → Word w) (mem : Memory w)
    (address : ℕ) (who : Fin (K₀).cells → Fin (R+1)) (logical : ℕ → CellInput) where
  ownerTable : OwnerTable pub mem ⟨u.val,address,(K₀).cells⟩ (PositiveTeam.ownerWord who)
  source : ∀ i : Fin ((rc).cells u).length, logical ((rc).order ⟨u,i⟩).val =
    (rc).sourceCall (N h₀) (K₀).cell (K₀).siteID (K₀).edgeID (K₀).portID (K₀).programs (K₀).owners (K₀).slot
      (pin input) (reported h₀) (bundles h₀) (v₀).val (fun _ _ => false) physical u i

end Cube.Physical.NativeAssignments.CoreDirectory

end BorderVNP
end Computability
end OAI
