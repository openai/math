import OAI.Computability.BorderVNP.DiagonalNativeArgumentCells
import OAI.Computability.BorderVNP.DiagonalPhysicalPinStart
import OAI.Computability.BorderVNP.DiagonalNativeCalibratedWindow

/-! # Clock and sparse arguments at jointly reachable private-call boundaries -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM TeamContraction CompactMachine BorderVNP.Cube ScheduleClock
open TeamContraction.ProcessorSlots CellMacro.Generator BorderVNP.Cube.Tally
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3600

variable {R n w dim box lanes selectors symbols : ℕ}
    (id : TableEntry dim box lanes selectors symbols → ℕ) (U : Fin (R+1) → PinStart SparseExterior.driver n w)

local notation3 (prettyPrint := false) "mac(" u ")" => install SparseExterior.driver n (U u).routines
local notation "A" => signedInputs id (TeamRows.ownedGroups dim box lanes selectors symbols)
local notation "groups" => scheduleGroups dim (selectorWidth dim selectors lanes)

/-- The complete joint input before the private calls. The independent report choices
need not agree with the subtotals that will be checked later. -/
abbrev JointPrefix := (u : Fin (R+1)) → (U u).Prefix id

/-- Replay exactly the true seven stages on the original physical pin spelling. -/
noncomputable abbrev visits {u} (localRun : (U u).Prefix id) :=
  let pin := (U u).pins localRun.1
  (SignedPrep.visitsEquiv id (U u).pub mac(u) pin.val.2.1 pin.val.2.2).symm localRun.2

/-- The actual post-route argument run, retaining constant installation, owner guesses,
reports and the task publisher, at its original memory and event stream. -/
noncomputable abbrev afterRoute {u} (p : (U u).Prefix id) :=
  let v := visits id U p
  SignedPrep.inputVisitsEquiv id (U u).pub mac(u) (TeamRows.ownedGroups dim box lanes selectors symbols)
    v.routing.val.2.1 v.routing.val.2.2 ⟨v.constants,v.owned,v.controls,v.reports,v.arguments⟩

private theorem prep_ticks {u} (p : (U u).Prefix id) :
    traceCost p.2.val.1 = traceCost (visits id U p).profile.val.1 + traceCost (visits id U p).routing.val.1 +
      traceCost (afterRoute id U p).val.1 := by
  let v := visits id U p
  have h := SignedPrep.cost id (U u).pub mac(u) v
  change traceCost ((SignedPrep.visitsEquiv id (U u).pub mac(u) _ _)
    ((SignedPrep.visitsEquiv id (U u).pub mac(u) _ _).symm p.2)).val.1 = _ at h
  rw [Equiv.apply_symm_apply] at h
  refine h.trans ?_
  simp only [v,afterRoute,SignedPrep.inputVisitsEquiv_val,Transmission.cost_append,Nat.add_assoc]

private theorem prep_after {u} (p : (U u).Prefix id) : p.2.val.2 = (afterRoute id U p).val.2 := by
  have states := SignedPrep.visitsEquiv_outState id (U u).pub mac(u) (visits id U p)
  simpa only [afterRoute,SignedPrep.inputVisitsEquiv_val,visits,Equiv.apply_symm_apply] using states

/-- The memory immediately after the fragment producer and typed-task constructor,
prior to installing the supplementary descriptors and the compressed field. -/
noncomputable def sparseMemory {u} (p : (U u).Prefix id) : Memory w :=
  let v := visits id U p
  let parts := (argumentVisitsEquiv (U u).pub mac(u) v.reports.val.2.1 v.reports.val.2.2).symm v.arguments
  parts.2.1.val.2.2

/-- Logical cells and compressed payloads at the point where the real task builder
published its directory. The private driver restores the occupied spans on these
same bytes. -/
structure SparseSource {u} (p : (U u).Prefix id) where
  /-- Native published tasks, RLE pointers and compressed-cell image at this cut. -/
  source : SparseCallInput (U u).pub (sparseMemory id U p)
  /-- Logical cell and original packed-call clock attached to each occupied native row. -/
  arguments : SparseArgumentCells (pub := (U u).pub) (m := sparseMemory id U p) n source

/-- The immutable reference data for the other teams can be fixed once per exterior.
This extension always uses the given team's actual returning preparation. -/
noncomputable def reference (ok : jointSupport id U) {u} (p : (U u).Prefix id) : JointPrefix id U :=
  Function.update (fun t => (ok t).some) u p

theorem reference_self (ok : jointSupport id U) {u} (p : (U u).Prefix id) :
    reference id U ok p u = p := Function.update_self ..

/-- Reindex an observation on a joint run to a locally returning preparation
without requiring any bound, allocation or source on an unfinishable prefix. -/
noncomputable def onLocal {f : ∀ u, (U u).Prefix id → Sort*} (ok : jointSupport id U)
    (read : ∀ a : JointPrefix id U, ∀ u, f u (a u)) {u} (p : (U u).Prefix id) : f u p :=
  reference_self id U ok p ▸ read (reference id U ok p) u

local notation3 (prettyPrint := false) "logicalCells(" d ")" => fun i =>
  SparseExterior.logicalCell ((SparseSource.arguments d).placed i)
    ((SparseSource.arguments d).extra i) ((SparseSource.arguments d).field i)
local notation3 (prettyPrint := false) "packetBytes(" d ")" => fun i =>
  CellSparse.Packet.input ((logicalCells(d) i).directory) ((SparseSource.arguments d).placed i).privateWires
    ((SparseSource.arguments d).field i).bytes

variable (used : Fin (R+1) → ℕ) (c : PhaseCharges)

/-- The other teams can be kept at their own true pre-call states when a local private
return is inspected. The clock pays the receipt of the original profile, the complete
argument writer and the discovered private calls. The finishing and reader bounds
apply to all local returning suffixes, including a zero-valued residue entry. -/
structure JointClock : Prop where
  early : ∀ (a : JointPrefix id U) u, let v := visits id U (a u)
    used u+traceCost ((U u).pins (a u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤ c.core+c.before
  arguments : ∀ (a : JointPrefix id U) u, let input := afterRoute id U (a u)
    traceCost input.val.1+privateDirectoryTicks (U u).pub input.val.2.2 ≤ c.argumentsCalls
  finish : ∀ (a : JointPrefix id U) u, let p := (a u).2
    ∀ q : Returns callOwnedCells (U u).pub mac(u) p.val.2.1 p.val.2.2,
    ∀ z : Returns (finishExpansion signedOccurrences) (U u).pub mac(u) q.val.2.1 q.val.2.2,
      traceCost z.val.1 ≤ c.finish
  reader : ∀ (a : JointPrefix id U) u, let p := (a u).2
    ∀ q : Returns callOwnedCells (U u).pub mac(u) p.val.2.1 p.val.2.2,
    ∀ z : Returns (finishExpansion signedOccurrences) (U u).pub mac(u) q.val.2.1 q.val.2.2,
    ∀ v : Returns leadEntry (U u).pub mac(u) z.val.2.1 z.val.2.2, traceCost v.val.1 ≤ c.reader

/-- All genuine returning local continuations fit the physical residual clock on
this jointly supported exterior, including prefixes later rejected by a different team. -/
noncomputable def JointClock.window (ok : jointSupport id U) {limit : ℕ}
    (paid : c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ limit)
    (measured : JointClock id U used c) (u : Fin (R+1)) :
    SignedStageWindow id (U u).pub (U u).routines SparseExterior.driver n (U u).bank (U u).memory
      (U u).pins (used u) limit where
  tallyTicks := c.finish
  readerTicks := c.reader
  fitted b p := by
    let a : (U u).Prefix id := ⟨b,p⟩
    have front := measured.early (reference id U ok a) u
    have after := measured.arguments (reference id U ok a) u
    rw [reference_self] at front after
    dsimp only at front after
    have cp := prep_ticks id U a
    have mp := congrArg Prod.snd (prep_after id U a)
    change p.val.2.2 = (afterRoute id U a).val.2.2 at mp
    change traceCost p.val.1 = _ at cp
    change used u+traceCost ((U u).pins b).val.1+_+_ ≤ _ at front
    rw [cp,mp]
    omega
  tally b p := by
    let a : (U u).Prefix id := ⟨b,p⟩
    have cut := measured.finish (reference id U ok a) u
    rw [reference_self] at cut
    exact cut
  reader b x := by
    let e := expansionReturnEquiv (U u).pub mac(u) ((U u).pins b).val.2.1 ((U u).pins b).val.2.2
      epochPlacement groups A signedOccurrences
    obtain ⟨⟨p,q,z⟩,rfl⟩ := e.surjective x
    let a : (U u).Prefix id := ⟨b,p⟩
    have cut := measured.reader (reference id U ok a) u
    rw [reference_self] at cut
    exact cut q z

/-- A single complete public preparation at every other team suffices to identify this
team's physical compact call rows. Its positive continuation uses these actual bytes
and reconstructs their logical private cells at every returning pin and preparation. -/
theorem joint_sparse_continuation (ok : jointSupport id U) {limit : ℕ}
    (paid : c.core+c.before+c.argumentsCalls+c.finish+c.reader ≤ limit)
    (measured : JointClock id U used c)
    (source : ∀ a : JointPrefix id U, ∀ u, SparseSource id U (a u)) (u : Fin (R+1)) :
    ∃ C : PositiveContinuation id SparseExterior.driver n (U u).pub (U u).routines (U u).bank (U u).memory
      (U u).pins (used u) limit,
      ∀ b p, let data := onLocal id U ok source (u := u) ⟨b,p⟩
        (C.cells b p).cell = logicalCells(data) ∧ (C.cells b p).payload = packetBytes(data) := by
  let data (a : (U u).Prefix id) := onLocal id U ok source a
  have rows (a : (U u).Prefix id) := typedRows_on_arguments (visits id U a).arguments
    (SignedPrep.typedParts id (U u).pub mac(u) (visits id U a)).1 (data a).source (data a).arguments
  obtain ⟨C,h⟩ := exists_positive_continuation id (U u).pub (U u).routines SparseExterior.driver n
    (U u).bank (U u).memory (U u).pins (measured.window id U used c ok paid u) (fun b p => (rows ⟨b,p⟩).choose)
  exact ⟨C,fun b p => ⟨(h b p).1.trans (rows ⟨b,p⟩).choose_spec.1,(h b p).2.trans (rows ⟨b,p⟩).choose_spec.2⟩⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
