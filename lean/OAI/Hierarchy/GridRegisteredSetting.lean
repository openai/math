import OAI.Hierarchy.GridRegisteredRunData
import OAI.Hierarchy.GridRegisteredCosts
import OAI.Hierarchy.GridPhysicalSelectorOrder
import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.TickResourceBounds
import OAI.Hierarchy.GridIdleLayout
import OAI.Hierarchy.GridProgrammed
import OAI.Hierarchy.GridThroughScheduled
import OAI.Hierarchy.NativeFactorOrdinal
import OAI.Hierarchy.FactorPinBudget

namespace OAI
/-! # The settings selected by the registered costs of the actual compressed machine

The archive, the input fibers and the two endpoints per rail all refer to the
same native run. The aggregate inequalities in `Room` are scalar length and
resource bounds. The tick allocation, conservation equations, available
passages, active tests and local addresses are derived from them. -/

noncomputable section
namespace Hierarchy.GridRegisteredSetting
open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.LaneCursor
open TraceDistribution TraceAdmission GridThrough FactorPinIntervals Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical

variable {F : Type} [Field F] [Fintype F]

namespace RunData
variable {W pc regs words S base fuel axes low : ℕ}
variable (D : RunData F W pc regs words S base fuel axes low)

abbrev trace := GridSelector.Trace D.run.plan (GridPhysicalSelector.bits D.run)
abbrev origin (h : D.run.plan.History) := Physical.origin D.block D.axesFit D.machine D.fit D.field
  D.state D.passes D.passesFit h (D.ordinal h)
abbrev bucket := Physical.bucketOrdinal D.machine D.fit D.field D.state

def dest (h : D.run.plan.History) (b : Fin (2^(axes+1))) : Fin (D.roots h) :=
  D.ordinal h (D.run.plan.destination h (0,finFunctionFinEquiv.symm b))

theorem owns (h : D.run.plan.History) (i : Fin S) : D.dest h (D.bucket i) = D.origin h i := by
  change D.ordinal h (D.run.plan.destination h (0,finFunctionFinEquiv.symm (finFunctionFinEquiv _))) = _
  rw [Equiv.symm_apply_apply]
  rfl

include D in
theorem input_extent : S ≤ 2^(axes+1)*(2*2^low) := by
  have grid := D.fit.grid
  rw [show 1+(axes+1+low)=(axes+1)+(1+low) by omega,
    pow_add 2 (axes+1) (1+low),pow_add 2 1 low,pow_one] at grid
  omega

/-- The final six addresses are left as supplied by the resource publisher.
Only the six numerical fields used for resource counts are specialized. -/
def parameters (template : Resources.Parameters ℕ) (h : D.run.plan.History) (m n B : ℕ) :
    Resources.Parameters ℕ :=
  { template with
    lanes := 2^(axes+1)
    roots := D.roots h
    directions := m+1
    pairSpan := 2^low
    band := GridIdleLayout.each m n B
    cap := S }

def costs (template : Resources.Parameters ℕ) (h : D.run.plan.History) (m n B : ℕ)
    (C : D.run.Charges) (unit : ℕ) : Fin (D.roots h) → Fin ((m+1)+2) → ℕ :=
  Resources.cost (D.parameters template h m n B) (D.dest h) (D.work h C unit)

variable {m n B q p scale : ℕ}

/-- Scalar estimates at the chosen scale. The pin bound counts the true
original inputs whose physical ancestor is the indicated terminal site. -/
structure Room (h : D.run.plan.History) (C : D.run.Charges) (unit scale m n B q p : ℕ)
    (header : Cell (m+1) n × Fin q → List Bool) where
  cap : ℕ
  budget : ℕ
  headerLength : ℕ
  copies : 0 < q
  side : 4 ≤ n+1
  pairs : 0 < B
  external : 2*((m+1)*GridIdleLayout.each m n B) ≤ S
  bitwidth : cap ≤ 2^scale
  work_bound : ∀ i, D.work h C unit i ≤ cap
  inputs : ∀ v : (D.run.plan.finish h).Site, Nat.card {j : Fin S //
    D.run.plan.destination h (PairedCursor.owner (layout D.machine D.fit D.field D.state) j)=v} ≤ cap
  avg : 4*S ≤ ((n+1)^(m+1)*q)*budget
  round : 4*((20*(scale+1)+2)^((m+1)+2))*cap ≤ budget
  pin_limit : headerLength+budget ≤ p
  headers : ∀ t, (header t).length ≤ headerLength
  passage : ((20*((scale:ℝ)+1)+2)^((m+1)+2)*cap)*((n+1)*q:ℕ) ≤ B/16

variable (template : Resources.Parameters ℕ) (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ)
variable (header : Cell (m+1) n × Fin q → List Bool) (advice : Fin S → Bool)
variable (R0 : D.Room h C unit scale m n B q p header)

include header R0 in
abbrev tickPos : 0 < (n+1)^(m+1)*q := Nat.mul_pos (pow_pos (Nat.succ_pos _) _) R0.copies

include header R0 in
def rail : GridIdleLayout.Rails m n B ↪ Fin (S/2) where
  toFun e := ⟨e.val,by have := e.isLt; have := R0.external; omega⟩
  inj' _ _ hz := Fin.ext (congrArg (fun y : Fin (S/2) => y.val) hz)

include header R0 in
theorem rail_extent : (m+1)*GridIdleLayout.each m n B ≤ 2^(axes+1)*2^low := by
  have ext := R0.external
  have grid := D.input_extent
  rw [show 2^(axes+1)*(2*2^low)=2*(2^(axes+1)*2^low) by ring] at grid
  omega

include header R0 in
theorem bounded (f : Fin (D.roots h)) (j : Fin ((m+1)+2)) : (D.costs template h m n B C unit) f j ≤ R0.cap := by
  apply Resources.cost_bounded (D.parameters template h m n B) (D.dest h) (D.work h C unit) R0.cap R0.work_bound _ R0.external
  intro i
  let route := fun a : Fin S => D.run.plan.destination h (PairedCursor.owner (layout D.machine D.fit D.field D.state) a)
  have actual := Resources.ranked_inputs (D.parameters template h m n B) (D.dest h) (D.ordinal h) route D.bucket
    (Nat.two_pow_pos _) D.input_extent (TraceDistribution.native_interval_index D.machine D.fit D.field D.state) (D.owns h) i
  exact actual.trans_le (R0.inputs _)

include header R0 in
theorem width (f : Fin (D.roots h)) (j : Fin ((m+1)+2)) : (D.costs template h m n B C unit) f j ≤ 2^scale :=
  (bounded D template h C unit header R0 f j).trans R0.bitwidth

include R0 in
theorem pin_room (tt : Cell (m+1) n × Fin q) : (header tt).length +
    ((FactorAllocation.factors scale (D.costs template h m n B C unit) (List.finRange (D.roots h)) (GridTicks.index tt)).map
      (fun i => (Finset.univ.filter (fun a => D.origin h a=i)).card)).sum ≤ p := by
  let j : Fin ((m+1)+2) := (0 : Fin ((m+1)+1)).succ
  have actual (f : Fin (D.roots h)) := Resources.cost_input_fiber (D.parameters template h m n B) (D.dest h) (D.work h C unit)
    (D.origin h) D.bucket (Nat.two_pow_pos _) D.input_extent
    (TraceDistribution.native_interval_index D.machine D.fit D.field D.state) (D.owns h) f
  have inventory := Resources.cost_inventory (D.parameters template h m n B) (D.dest h) (D.work h C unit) D.input_extent
    (rail_extent D h C unit header R0)
  have inputSum : ((List.finRange (D.roots h)).map
      (fun f => D.costs template h m n B C unit f j)).sum = S := inventory.2.1
  exact allocated_input_room (D.origin h) (D.costs template h m n B C unit) j
    (fun f => (actual f).trans (length_intervalBits _ _))
    (width D template h C unit header R0) (bounded D template h C unit header R0)
    ((congrArg (4 * ·) inputSum).trans_le R0.avg)
    R0.round R0.pin_limit (GridTicks.index tt) (header tt) (R0.headers tt)

abbrev pins : GridThrough.PinAssignment (GridIdleLayout.Rails m n B) (m+1) n q p :=
  Physical.ordinalScheduledPins D.block D.axesFit D.machine D.fit D.field D.state D.passes
  D.passesFit h (D.ordinal h) (tickPos D h C unit header R0) scale (D.costs template h m n B C unit) header advice
  (pin_room D template h C unit header R0) (rail D h C unit header R0) (GridIdleLayout.direction (m:=m) (n:=n) (B:=B))

/-- The recorded per-tick direction counts are read from the exact factor list. -/
def counts (j : Fin (m+1)) (tt : Fin ((n+1)^(m+1)*q)) :=
  ((FactorAllocation.factors scale (D.costs template h m n B C unit) (List.finRange (D.roots h)) tt).map
    (fun f => D.costs template h m n B C unit f j.succ.succ)).sum

theorem conservation (j : Fin (m+1)) (tt : Fin ((n+1)^(m+1)*q)) :
    (GridTicks.pairFiber (GridIdleLayout.direction (m:=m) (n:=n) (B:=B))
      (fun e => GridTicks.index ((pins D template h C unit header advice R0).tick e)) j tt).card =
      (counts (scale:=scale) (q:=q) (m:=m) (n:=n) (B:=B) D template h C unit) j tt := by
  let railMap := rail D h C unit header R0
  have paired := Resources.exterior_account (D.parameters template h m n B) (D.dest h) (D.work h C unit) rfl
    (GridIdleLayout.direction (m:=m) (n:=n) (B:=B))
    GridIdleLayout.direction_val railMap (fun _ => rfl) (D.origin h) D.bucket
    (TraceDistribution.native_interval_index D.machine D.fit D.field D.state) (D.owns h)
    (Nat.two_pow_pos _) (by have := R0.pairs; dsimp [parameters,GridIdleLayout.each]; positivity) (rail_extent D h C unit header R0)
  have owners := FactorAllocation.fiber_conservation (tickPos D h C unit header R0) scale (D.costs template h m n B C unit)
    (fun e => D.origin h (pairPorts railMap (e,false))) (GridIdleLayout.direction (m:=m) (n:=n) (B:=B)) (fun j => j.succ.succ) paired j tt
  have tick_read (e : (GridIdleLayout.Rails m n B)) : GridTicks.index ((pins D template h C unit header advice R0).tick e) =
      FactorAllocation.owner (tickPos D h C unit header R0) scale (D.costs template h m n B C unit)
        (D.origin h (pairPorts railMap (e,false))) :=
    GridTicks.index.apply_symm_apply _
  refine Eq.trans ?_ owners
  apply congrArg Finset.card
  ext e
  simp only [GridTicks.pairFiber,Finset.mem_filter,Finset.mem_univ,true_and,tick_read]
  exact ⟨fun hp => ⟨Finset.mem_univ _,hp⟩,And.right⟩

include header R0 in
theorem enough (X : Catalyst.Approximation F (m+1) (q*p)) (reserved : ∀ j, X.width j ≤ B)
    (c : Cell (m+1) n) (j : Fin (m+1)) : X.width j ≤ ((GridTicks.pairsOn ((counts (scale:=scale) (q:=q) (m:=m) (n:=n) (B:=B) D template h C unit) j) (GridTicks.lineTicks j c)) \
      (GridTicks.pairsOn ((counts (scale:=scale) (q:=q) (m:=m) (n:=n) (B:=B) D template h C unit) j) (GridTicks.cellTicks c))).card := by
  have total := (Resources.cost_inventory (D.parameters template h m n B) (D.dest h) (D.work h C unit) D.input_extent
    (rail_extent D h C unit header R0)).2.2 j
  exact (reserved j).trans (GridTicks.scheduled_line_passages (k:=m+1) (g:=n+1) (q:=q) (B:=B)
    R0.side R0.copies (D.costs template h m n B C unit) (List.finRange _) j.succ.succ
    (fun f _ => width D template h C unit header R0 f) (fun f _ => bounded D template h C unit header R0 f)
    total R0.passage j c).2.2

/-- Both the native geometry writer and the scalar distribution use this same
`ofScheduled` term, with the genuine ordinal allocator as its pin assignment. -/
def scheduled (D : RunData F W pc regs words S base fuel axes low) (template : Resources.Parameters ℕ)
    (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ)
    (header : Cell (m+1) n × Fin q → List Bool) (advice : Fin S → Bool)
    (R0 : D.Room h C unit scale m n B q p header) (X : Catalyst.Approximation F (m+1) (q*p)) (reserved : ∀ j, X.width j ≤ B) :
    GridThrough.Setting X n ((m+1)*GridIdleLayout.each m n B) (GridIdleLayout.direction (m:=m) (n:=n) (B:=B)) :=
  ⟨GridThrough.Program.ofScheduled (pins D template h C unit header advice R0) X.width
    (counts (scale:=scale) (q:=q) (m:=m) (n:=n) (B:=B) D template h C unit)
    (conservation D template h C unit header advice R0)
    (enough D template h C unit header R0 X reserved),rfl⟩

theorem active (X : Catalyst.Approximation F (m+1) (q*p)) (reserved : ∀ j, X.width j ≤ B) (e : (GridIdleLayout.Rails m n B)) :
    (scheduled D template h C unit header advice R0 X reserved).1.touch e = some (((pins D template h C unit header advice R0).tick e).1
      ((GridIdleLayout.direction (m:=m) (n:=n) (B:=B)) e)) := rfl

theorem data (X : Catalyst.Approximation F (m+1) (q*p)) (reserved : ∀ j, X.width j ≤ B) :
    (scheduled D template h C unit header advice R0 X reserved).1.data =
      (pins D template h C unit header advice R0).data := rfl

include header R0 in
/-- A cost bound on each executed tick uses exactly the root charge of this run. -/
theorem tick_work (charge limit : ℕ)
    (avg : 4*charge*(unit*D.run.rootTotal h C
      (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit)) ≤ ((n+1)^(m+1)*q)*limit)
    (err : 4*charge*((20*(scale+1)+2)^((m+1)+2))*R0.cap ≤ limit) (tt : (Cell (m+1) n × Fin q)) :
    charge*((FactorAllocation.factors scale (D.costs template h m n B C unit) (List.finRange (D.roots h)) (GridTicks.index tt)).map
      (D.work h C unit)).sum ≤ limit := by
  have total : ((List.finRange (D.roots h)).map (fun f => (D.costs template h m n B C unit) f 0)).sum =
      unit*D.run.rootTotal h C (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) := by
    change ((List.finRange (D.roots h)).map (D.work h C unit)).sum = _
    simpa only [List.finRange,List.map_ofFn,List.sum_ofFn,Function.comp_def,id_eq] using D.work_sum h C unit
  exact GridScale.resource_fits (D.costs template h m n B C unit) (List.finRange _) 0 (GridTicks.index tt)
    (fun f _ => width D template h C unit header R0 f) (fun f _ => bounded D template h C unit header R0 f)
    (by rw [total]; exact avg) err

section Controller
variable {receiverPC receiverRegs receiverWords : ℕ}
variable (accepts : 0 < receiverPC) (X : Catalyst.Approximation F (m+1) (q*p))
variable (reserved : ∀ j, X.width j ≤ B)
variable (headers : D.trace → Cell (m+1) n × Fin q → List Bool) (literals : D.trace → Fin S → Bool)
variable (rooms : ∀ z : D.trace, D.Room z.1 C unit scale m n B q p (headers z))
/-- A selector branch from the actual history chooses its matching numbered
occurrences. The identity branch installs the accepting native tick. -/
def dispatch (template : Resources.Parameters ℕ) (C : D.run.Charges) (unit : ℕ)
    (accepts : 0 < receiverPC) (X : Catalyst.Approximation F (m+1) (q*p))
    (reserved : ∀ j, X.width j ≤ B)
    (headers : D.trace → Cell (m+1) n × Fin q → List Bool) (literals : D.trace → Fin S → Bool)
    (rooms : ∀ z : D.trace, D.Room z.1 C unit scale m n B q p (headers z)) :
    Option D.trace → GridThrough.Setting X n ((m+1)*GridIdleLayout.each m n B)
      (GridIdleLayout.direction (m:=m) (n:=n) (B:=B))
  | none => ⟨GridIdleLayout.program X.width reserved
      (GridIdleLayout.literal (w:=scale) (r:=receiverRegs) (K:=receiverWords) (S:=p) (q:=q) accepts),rfl⟩
  | some z => scheduled D template z.1 C unit (headers z) (literals z) (rooms z) X reserved

theorem noTouch (e : GridIdleLayout.Rails m n B) : (dispatch (receiverRegs:=receiverRegs) (receiverWords:=receiverWords) D template C unit accepts X reserved
      headers literals rooms none).1.touch e = none := rfl

theorem allTouch (z : D.trace) (e : GridIdleLayout.Rails m n B) : (dispatch (receiverRegs:=receiverRegs) (receiverWords:=receiverWords) D template C unit accepts X reserved
      headers literals rooms (some z)).1.touch e ≠ none := by
  change some _ ≠ none
  simp

theorem unit_eval (fit : NativeTrace.Fits (UniversalTick.accept (64*scale) receiverPC receiverRegs receiverWords accepts)
      p 0 (UniversalTick.depth scale UniversalTick.saving) (UniversalTick.clock scale UniversalTick.saving))
    (hf : Fintype.card F ≤ 2^(64*scale)) (st : Word (64*scale))
    (x : GridDiagonal.Pins (GridIdleLayout.Rails m n B)) (c : Cell (m+1) n) :
    Catalyst.tickProduct (UniversalTick.tick hf fit.width fit.labels 0 st fit.header fit.time receiverRegs receiverWords) q
      ((dispatch (receiverRegs:=receiverRegs) (receiverWords:=receiverWords) D template C unit accepts X reserved
      headers literals rooms none).1.dataBits x c) = 1 := GridIdleLayout.ticks_one accepts fit hf st X.width reserved x c

/-- Both selectors reserve the first rails in their actual geometry, as used
by the native passage and touch-mask sweep. -/
theorem installed (z : Option D.trace) :
    let Q := (dispatch (receiverRegs:=receiverRegs) (receiverWords:=receiverWords) D template C unit accepts X reserved
      headers literals rooms z).1
    ∀ available : ∀ x j, X.width j ≤ (GridLens.untouchedRails Q.direction Q.row Q.touch x j).card,
      Q.pass = GridLens.firstPassage Q.direction Q.row Q.touch X.width available := by
  cases z <;> dsimp only [] <;> intro available <;> rfl

end Controller

end RunData
end Hierarchy.GridRegisteredSetting
end

end OAI
