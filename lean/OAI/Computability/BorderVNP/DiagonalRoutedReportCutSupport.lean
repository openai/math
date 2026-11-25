import OAI.Computability.BorderVNP.DiagonalSupportedParsedFields
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved
import OAI.Computability.BorderVNP.DiagonalSourceReturnedInputs

/-! # Restoring the whole indexed prefix on joint pre-call support -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open TeamContraction TeamContraction.ProcessorSlots CellMacro.Generator BorderVNP.Cube

variable {X : Type} {R n w axes box lanes selectors symbols : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {positive support : X → Prop} (U : {x // positive x} → Fin (R+1) → PinStart gen n w)
    (prepared : ∀ x : {x // positive x}, support x.val ↔ jointSupport id (U x))
    (T : {x // positive x ∧ support x} → Fin (R+1) → PositiveTeam id gen n w)
    (same : ∀ x u, (T x u).start=U ⟨x.val,x.property.1⟩ u)


private theorem castPrefix_pair {A B : PinStart gen n w} (h : A=B) (p : A.Prefix id) :
    (⟨B, Equiv.cast (congrArg (fun M : PinStart gen n w => M.Prefix id) h) p⟩ :
      Σ M : PinStart gen n w, M.Prefix id) = ⟨A,p⟩ := by
  subst B
  rfl

/-- The inverse restriction to supported teams recovers the entire indexed
starting machine and prefix, including the native pin return and every visit. -/
theorem positivePrefixes_symm_pair (a : (x : {x // positive x}) × ((u : Fin (R+1)) → (U x u).Prefix id))
    (u : Fin (R+1)) :
    let z := (positivePrefixes U prepared T same).symm a
    (⟨(T z.1 u).start,z.2 u⟩ : Σ M : PinStart gen n w, M.Prefix id) = ⟨U a.1 u,a.2 u⟩ := by
  let x : {x // positive x ∧ support x} := ⟨a.1.val,a.1.property,(prepared a.1).2 (fun v => ⟨a.2 v⟩)⟩
  exact castPrefix_pair (same x u).symm (a.2 u)

end RoutingISA.Evaluator.PinStart

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve axes groups cap dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ i, (args i).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ i, (G.transferFrame i (args i).header (args i).dst).Fits w (base i))
    (width : L.header=PositiveFields.width reserve axes groups cap (R+1) dim tally)

local notation "Fields" => PositiveFields reserve axes groups cap (R+1) dim tally
local notation "Cube" => Physical.Broadcast axes groups cap
local notation "Claim" => (Fin ((R+1)*dim*tally) → Bool)
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable {box lanes selectors symbols : ℕ} {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)

variable {Hist : Type} {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
    (code : Hist ↪ (Fin reserve → Bool))
    (valid : ∀ (i : Fin d → Bool) (p : PositiveFields reserve axes groups cap (R+1) dim tally),
      ParsedPreCall G args live L fixed hw size base fit width U ib hb sb pinWidth id i p → ∃ q, code q=p.profile)
    (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
      (Σ c : Physical.Broadcast axes groups cap,
        ParsedPreCall G args live L fixed hw size base fit width U ib hb sb pinWidth id i ⟨code q,c,claim⟩) ≃
      Σ v : Route q,Report i q v)

local notation3 (prettyPrint := false) "prep" => jointPreparedFields (id := id) (gen := gen) G args live L fixed hw size base fit width U ib hb sb
  pinWidth code valid routed

variable {support : (Exterior R r link → Bool) → Prop}
    (prepared : ∀ x : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext},
      support x.val ↔ PinStart.jointSupport id (U x))
    (T : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext ∧ support ext} →
      Fin (R+1) → PositiveTeam id gen n w)
    (same : ∀ x u, (T x u).start=U ⟨x.val,x.property.1⟩ u)

local notation3 (prettyPrint := false) "decoded" => supportedPreparedFields G args live L fixed hw size base fit width
  U ib hb sb pinWidth code valid routed prepared T same


set_option maxHeartbeats 325000 in
/-- Joining the profile, relay, and proposed header reconstructs the actual
supported team and its entire prefix from the routed decoder, as one
dependent pair. Consequently every intermediate return may be read on it. -/
theorem supportedPreparedFields_symm_pair (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) :
    let z := (decoded).symm ⟨i,q,v,c,a⟩
    let seen := (routed i q c).symm ⟨v,a⟩
    let ext := (headers).symm ⟨(⟨code q,seen.1,c⟩ : Fields),seen.2.1⟩
    let original : (U ext u).Prefix id := ⟨_,seen.2.2 u⟩
    (⟨(T z.1 u).start,z.2 u⟩ : Σ M : PinStart gen n w, M.Prefix id) = ⟨U ext u,original⟩ :=
  PinStart.positivePrefixes_symm_pair U prepared T same ((prep).symm ⟨i,q,v,c,a⟩) u

open RoutingISA.Evaluator.SignedPrep DiagonalTallyCellReports

set_option maxHeartbeats 400000 in
/-- Restore the fitted reports and the observed argument launcher on the
actual supported positive team's prefix. The layout, source tape and scalar
description are all retained. -/
theorem supportedPreparedFields_reportCut (i : Fin d → Bool) (q : Hist) (v : Route q)
    (c : Claim) (a : Report i q v) (u : Fin (R+1)) {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (cur : ReportCursor) (desc : ℕ) :
    let z := (decoded).symm ⟨i,q,v,c,a⟩
    let seen := (routed i q c).symm ⟨v,a⟩
    let ext := (headers).symm ⟨(⟨code q,seen.1,c⟩ : Fields),seen.2.1⟩
    let original : (U ext u).Prefix id := ⟨_,seen.2.2 u⟩
    Nonempty (ReportArgumentCut ((U ext u).visited original).reports rows cur desc) →
      Nonempty (ReportArgumentCut ((T z.1 u).start.visited (z.2 u)).reports rows cur desc) := by
  let observation (s : Σ M : PinStart gen n w, M.Prefix id) :=
    Nonempty (ReportArgumentCut (s.1.visited s.2).reports rows cur desc)
  exact (congrArg observation (supportedPreparedFields_symm_pair G args live L fixed hw size base fit width U ib hb sb
    pinWidth code valid routed prepared T same i q v c a u)).mpr


end TeamContraction

end BorderVNP
end Computability
end OAI
