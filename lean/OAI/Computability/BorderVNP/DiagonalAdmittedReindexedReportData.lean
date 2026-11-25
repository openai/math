import OAI.Computability.BorderVNP.DiagonalAdmittedReportedRouteData
import OAI.Computability.BorderVNP.DiagonalRoutedReportProposals

/-! # Transporting a physical report and its route through one source equivalence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports


/-- A source report assignment together with the physical layout and the
precise ordered list of cells to which it applies. -/
abbrev ReportInputKey := (l : ReportLayout) × (cells : List (ReportCell l)) × ReportAssignments cells

/-- Record the layout, cell sequence and the sampled values in that order. -/
def ReportInputKey.ofRows {l : ReportLayout} {cells : List (ReportCell l)} (rows : ReportAssignments cells) :
    ReportInputKey := ⟨l,cells,rows⟩

private theorem reindexObservation {A B X Teams Key : Type*}
    (original : X ≃ A) (recode : A ≃ B) (read : X → Teams → Key → Prop)
    (aKey : A → Teams → Key) (bKey : B → Teams → Key)
    (same : ∀ b u, aKey (recode.symm b) u=bKey b u)
    (known : ∀ a u, read (original.symm a) u (aKey a u)) (b : B) (u : Teams) :
    read ((original.trans recode).symm b) u (bKey b u) :=
  (congrArg (read (original.symm (recode.symm b)) u) (same b u)).mp (known (recode.symm b) u)

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (ar : CubeArena.Layout)
local notation "cap" => declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s
variable (width : L.header=PositiveFields.width reserve ar.n ar.header.d
      (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally)
    {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (S : SourceReports ar owners) (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

local notation "Fields" => PositiveFields reserve ar.n ar.header.d cap (R+1) dim tally
local notation3 (prettyPrint := false) "p(" c ")" => (⟨profile,c,claim⟩ : Fields)
local notation3 (prettyPrint := false) "head" => fun c : RawBroadcast ar => (p(c)).bits
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable (allowed : RawBroadcast ar → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)
local notation3 (prettyPrint := false) "runs(" c ")" => ((ext : HeaderExterior L (p(c)).bits) ×
  pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p(c),ext⟩) rawPin)

variable (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim allowed template entries)

set_option maxHeartbeats 800000 in
/-- Reindex the source of the complete route-and-report package. The
directory and the actual report bits move together, so this applies even
when the two source indices use different dependent representations. -/
noncomputable def AdmittedPinnedFrames.reportRouteDataReindex
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners, allowed (routeBroadcast ar owners q).val)
    {Route : Type} {Report : Route → Type}
    (recode : S.Proposals ≃ (Σ v : Route, Report v))
    (key : (Σ v : Route, Report v) → Fin (R+1) → ReportInputKey)
    (same : ∀ z u, ReportInputKey.ofRows ((recode.symm z).2 u)=key z u) :
    {e : (Σ c : RawBroadcast ar, runs(c)) ≃ (Σ v : Route, Report v) //
      ∀ v reports u, pinnedReportCutAt G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
        rawPin profile claim (e.symm ⟨v,reports⟩) u ((key ⟨v,reports⟩ u).2.2)} := by
  let data := candidates.reportRouteData G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
    owners S rawPin profile claim allowed template entries checked honest
  let input (a : S.Proposals)
      (u : Fin (R+1)) := ReportInputKey.ofRows (a.2 u)
  let observed (full : Σ c : RawBroadcast ar, runs(c)) (u : Fin (R+1)) (k : ReportInputKey) :=
    pinnedReportCutAt G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
      rawPin profile claim full u k.2.2
  have recorded : ∀ a u, observed (data.val.symm a) u (input a u) := by
    rintro ⟨q,rs⟩ u
    dsimp only [observed,input,ReportInputKey.ofRows]
    exact data.property q rs u
  exact ⟨data.val.trans recode,fun v r u => reindexObservation data.val recode observed input key same recorded ⟨v,r⟩ u⟩

/-- Projecting the reindexed package changes only the naming of its
source. The underlying physical preparation is the original admitted one. -/
theorem AdmittedPinnedFrames.reportRouteData_reindex_val
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners, allowed (routeBroadcast ar owners q).val)
    {Route : Type} {Report : Route → Type}
    (recode : S.Proposals ≃ (Σ v : Route, Report v))
    (key : (Σ v : Route, Report v) → Fin (R+1) → ReportInputKey)
    (same : ∀ z u, ReportInputKey.ofRows ((recode.symm z).2 u)=key z u) :
    (candidates.reportRouteDataReindex G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
      owners S rawPin profile claim allowed template entries checked honest recode key same).val =
    (candidates.preparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
      owners S rawPin profile claim allowed template entries checked honest).trans recode := rfl


end TeamContraction

end BorderVNP
end Computability
end OAI
