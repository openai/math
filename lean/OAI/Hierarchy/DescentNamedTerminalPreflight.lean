import OAI.Hierarchy.DescentTerminalPreflightBook
import OAI.Hierarchy.DescentTerminalPreflightRate
import OAI.Hierarchy.DescentNamedPublicWidthRows
import OAI.Hierarchy.DescentExteriorPrintedCalendar

namespace OAI
/-! # One branch-independent terminal address program for the selected named compiler -/
namespace Hierarchy.DescentSixParty.SeedNamed.Origin
open ThreeFlat.Routing DescentColonies
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open private physicalCapacity from OAI.Hierarchy.DescentNamedSeedChronology
private theorem capacityOnTransport {F : Type} [Field F] {P : Type} {d : ℕ} {bits : P → ℕ}
    {W W' : MarkedWorld F d P bits} {G : PoweredGadget F} {q fee : ℝ} {S : AtomSchedule} {k z wire s : ℕ}
    (r : Reached W G q fee S k 0 z 3 wire s) (eqn : world r = W')
    (bound : physicalCapacity r = 256) : (transport r eqn).placement.cap = 256 := by
  cases eqn
  exact bound
private theorem sourceCapRead {F : Type} [Field F] {cp pins : ℕ} {X : Approximation F cp pins}
    {G : PoweredGadget F} {S : AtomSchedule} {q fee : ℝ} {k z wire s : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (S:=S) (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits) :
    o.source.placement.cap = 256 := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let origin ← Lean.Meta.getFVarFromUserName `o
      let source ← Lean.instantiateMVars (← Lean.Meta.mkAppM ``Origin.source #[origin])
      let sa := source.getAppArgs
      unless sa.size == 16 do throwError "unexpected Origin.source arguments"
      let decl ← Lean.getConstInfo ``Origin.source
      let val ← Lean.Core.instantiateValueLevelParams decl source.getAppFn.constLevels!
      let body := (val.beta sa).consumeMData
      unless body.isAppOf ``transport && body.getAppArgs.size == 17 do
        throwError "Origin.source is not a fully applied transport"
      let ta := body.getAppArgs
      -- Infer the generic proof arguments on the original transport telescope.
      let td ← Lean.getConstInfo ``transport
      let template ← Lean.Meta.forallTelescope td.type fun xs _ => do
        unless xs.size == 17 do throwError "unexpected transport telescope"
        let facts ← Lean.Meta.mkAppM ``capacityOnTransport #[xs[15]!, xs[16]!]
        Lean.Meta.mkLambdaFVars xs (← Lean.instantiateMVars facts)
      -- The existing SeedLink from this particular Origin supplies the capacity bound.
      let seed := Lean.mkAppN (Lean.mkConst ``Origin.seed) sa
      let capArgs := #[sa[0]!, sa[1]!, sa[5]!, sa[7]!, sa[8]!, sa[6]!, sa[9]!,
        sa[2]!, sa[3]!, sa[4]!, sa[11]!, sa[12]!, sa[10]!, sa[13]!, ta[15]!, sa[14]!, seed]
      let capProof := Lean.mkAppN (Lean.mkConst ``Chronology.SeedLink.capacity) capArgs
      goal.assign (Lean.mkApp (template.beta ta) capProof)

end Hierarchy.DescentSixParty.SeedNamed.Origin

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

local notation "s" => S.firstWidth G.b p
open DescentTerminalPreflightSpace
open Computability.BorderVNP.FragmentBucket
namespace Branch

/-- Fixed choices for the physical registers and paid row budget. Geometry and the
original port alphabet determine the remaining hardware dimensions. -/
structure PreflightFormat where
  columns : ℕ
  pointerBits : ℕ
  countBits : ℕ
  paidLanes : ℕ
  actorLanes : ℕ
  paidBits : ℕ
  externalBits : ℕ
  vertices : ℕ
  «arguments» : ℕ
  binSize : ℕ
  pageBits : ℕ
  cableCellBits : ℕ
  printBits : ℕ
  headerRows : ℕ
  paidRows : ℕ

/-- This address specification reads only the original gadget, schedule, and public format. -/
def preflightSpec (k g p tail:ℕ) (L:PreflightFormat) : Spec where
  scalar := ⟨2^k,S.hostSize S.length,L.columns,L.pointerBits,L.countBits⟩
  frozenBits := k*S.length
  cohortBits := 8+S.capGain*S.length
  cohorts := Fintype.card (Port P X.width)*2^(k*S.length)
  groups := S.groupCount S.length
  paidLanes := L.paidLanes
  actorLanes := L.actorLanes
  paidBits := L.paidBits
  externalBits := L.externalBits
  vertices := L.vertices
  «arguments» := L.arguments
  binSize := L.binSize
  pageBits := L.pageBits
  degree := 3
  cap := (capCalendar G.b S.rounds g S.height).prod*256
  signedLanes := 2^tail
  cableCellBits := L.cableCellBits
  grainsPerCable := G.b
  signedPositive := Nat.two_pow_pos _
  printBits := L.printBits
  publicGrains := publicRate G S (p:=p) (k:=k) (tail:=tail)
  headerRows := L.headerRows
  paidRows := L.paidRows

variable {tail:ℕ} (base:S.baseGroups=2^tail) (L:PreflightFormat)
local notation "spec" => preflightSpec X G S k g p tail L
local notation "placement0" => b.target.placement

include b in
/-- Both the technical number of socket rows and their field capacity are attained at the
actual end of the epoch. In particular an isolated host still has three padded sockets. -/
theorem preflight_caps :
    (placement0).degree=(spec).degree ∧ (placement0).cap=(spec).cap ∧ b.path.frozen=(spec).frozenBits :=
by
  have startCap : b.origin.source.placement.cap = 256 := by
    exact Origin.sourceCapRead b.origin
  refine ⟨b.target.branch,?_,b.path.frozen_age⟩
  change (placement0).cap = (capCalendar G.b S.rounds g S.height).prod*256
  simpa only [b.calendar,startCap] using b.path.capacity_eq

include hp base b in
theorem preflight_grains :
    ((placement0).z*G.b)/p=(spec).grainsPerCable ∧ (spec).signedLanes=(spec).groups := by
  constructor
  · change ((placement0).z*G.b)/p=G.b
    rw [b.target.grain,Nat.mul_div_cancel_left _ hp]
  · change 2^tail=S.groupCount S.length
    simp [AtomSchedule.groupCount,base]

theorem preflight_strips : 0<(spec).strips := by
  change 0<3+_;omega

include b in
theorem preflight_census (origin:ℕ) :
    (spec).cohortEnd origin=DescentTerminalCohortArena.stop origin b.path.frozen
      (8+S.capGain*S.length) (Fintype.card (Port P X.width)*2^b.path.frozen) (S.hostSize S.length) := by
  rw [b.path.frozen_age];rfl

include b in
theorem preflight_publicShape (origin:ℕ) :
    (spec).publicWidths origin=publicWidthShape X G S b (tail:=tail) origin ((spec).cableEnd origin) L.headerRows := by
  unfold publicWidthShape
  rw [b.path.frozen_age]
  rfl


end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
