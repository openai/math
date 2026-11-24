import OAI.Computability.VPVNP.PairRefreshResidentKernel
import OAI.Computability.VPVNP.CompressorRegisterSetupClock
import OAI.Computability.VPVNP.CompressorRegisterSetupTrace

/-! # Exact traces of the refresh diagonal and grid/port dispatcher

The operand setup depends only on the six inputs and external memory. The
comparison and dispatch loops add fixed runs of private ticks, so arbitrary
caller registers have no effect on the chronological external reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentImage.Plan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe OperandInputs PairSimulation NodeArguments MotifConversion NewSlots RefreshMapOperands NetworkKernel
open scoped Fin.CommRing

variable {bits g t hist shared pcs regs : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  (T : Plan B t hist shared)
  (pc : T.Address → Fin pcs) (dfs : Fin 9 ↪ Fin regs) (saved : VertexImage.Saved ↪ Fin regs)
  (common : Fin shared ↪ Fin regs) (own : T.Local ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11) (installed : T.Installed pc dfs saved common own done M)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)

variable (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (start : ℕ) (m : Memory bits)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t (Plan.stride T) start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "inp" => T.inputs dfs saved common
local notation "vout" => ws (v,Prod.snd v)
local notation "vin" => ws (Equiv.symm perm (v,Prod.snd v))

variable (old : X.network.Half (oldSite X v)) (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
local notation "diagonalValue" => portDiagonal perm ws (Prod.fst v) (Prod.snd v) (oldHalf X v old) (segments X v P hD hd internal new)


open MotifEntry MotifDemandPadding MotifSelector LocalHistory
local notation "E₀" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀)
local notation "idx" => (z,Prod.snd v)
local notation "dx" => List.length (RegisterSetup.lines (Plan.diagonal T)) + (7*(vout+vin)+9)
local notation "rx" => List.length (RegisterSetup.lines (Plan.route T)) +
  RefreshResidentDispatch.chainTicks (Fin.val (Equiv.symm (RefreshResidentDispatch.gridOrder B) z)) (Fin.val (Prod.snd v))
local notation "dp" => ∑ i, Expr.loads ((Plan.diagonal T) i)
local notation "rp" => ∑ i, Expr.loads ((Plan.route T) i)

/-- Chronological register-setup events obtained by evaluating the compiled operand expressions
in the supplied external memory. -/
def setupEvents {n : ℕ} (f : Fin n → Expr) (pub : Fin 5 → W bits) (state : W bits)
    (m : Memory bits) : List (Event bits) :=
  (RowRecipe.evaluate pub state m (RegisterSetup.lines f) (fun _ => 0)).1

/-- Trace through diagonal setup, outgoing and incoming bit comparisons, route setup, and
selection of the grid and party handler. -/
noncomputable def frontEvents (pub : Fin 5 → W bits) (state : W bits) : List (Event bits) :=
  (setupEvents T.diagonal pub state m ++ List.replicate (7*(vout+vin)+9) .tick) ++
    (setupEvents T.route pub state m ++ List.replicate
      (RefreshResidentDispatch.chainTicks ((RefreshResidentDispatch.gridOrder B).symm z).val v.2.val) .tick)

private theorem ticks {n : ℕ} :
    choiceBits (List.replicate n (.tick : Event bits)) = [] ∧ countProbes (List.replicate n (.tick : Event bits)) = 0 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ,choiceBits,countProbes] using ih

private theorem tickPrefix {a b : Config bits pcs regs} {n : ℕ}
    (run : PrimedCounter.GuessWord.Prefix M a (List.replicate n .tick) b) :
    ChildScan.Prefix M m a b [] (List.replicate n .tick) := by
  intro fuel more
  simpa only [(ticks (bits := bits) (n := n)).1] using run.execute fuel m more

private theorem setup_exact {n : ℕ} (f : Fin n → Expr) (inputs : Fin 6 → Fin regs)
    (vm : Fin (RegisterSetup.regCount f) ↪ Fin regs) (loc : ℕ → Fin pcs)
    (link : RegisterSetup.Linked vm inputs M loc (RegisterSetup.lines f)) (safe : ∀ i j, vm i ≠ inputs j)
    (c : Config bits pcs regs) (entry : c.pc = loc 0) :
    let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let es := setupEvents f pub state m
    ∃ d, ChildScan.Prefix M m c d [] es ∧ es.length = (RegisterSetup.lines f).length ∧
      countProbes es = ∑ i, (f i).loads ∧ choiceBits es = [] ∧ d.pc = loc (RegisterSetup.lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, d.reg (vm (RegisterSetup.output f i)) = (f i).eval pub state m) ∧
      ∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j := by
  intro pub state es
  have raw := RegisterSetup.execute_setup_raw f inputs vm M m loc link safe c entry
  dsimp only at raw
  rw [RegisterSetup.events_eq] at raw
  obtain ⟨d,len,probes,choices,exit,mem,pers,vals,frame,run⟩ := raw
  exact ⟨d,run,len,probes,choices,exit,mem,pers,vals,frame⟩

include installed in
set_option maxHeartbeats 1600000 in
theorem front_exact {fit : N ≤ 2^bits} (c : Config bits pcs regs) (entry : c.pc = T.diagSetup pc 0)
    (banks : Banks T dfs saved common own)
    (args : Describes T.input (fun i => c.reg (inp i.castSucc)) (c.reg (inp (Fin.last 5))) m
      X v P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice T.ties start T.stride fit m)
    (oldCols : oldDir.ActualColumns X m) (newCols : newDir.ActualColumns Y m)
    (oldData : NodeFields A child X (oldSite X v) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites v) new c.privateMem)
    (wide : D < 2^bits) (wo : vout < 2^bits) (wi : vin < 2^bits) (ok : diagonalValue = (1 : ℤ)) :
    let pub := fun i : Fin 5 => c.reg (inp i.castSucc)
    let state := c.reg (inp (Fin.last 5))
    let es := T.frontEvents X choice v m old new pub state
    ∃ out, ChildScan.Prefix M m c out [] es ∧ es.length = dx + rx ∧ countProbes es = dp + rp ∧
      choiceBits es = [] ∧ out.pc = T.family.target (T.handlerPC pc) idx ∧
      (∀ j, (∀ i, j ≠ own i) → out.reg j = c.reg j) ∧ out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro pub state es
  obtain ⟨a,first,alen,ap,ab,apc,amem,aper,aval,aframe⟩ := setup_exact M m T.diagonal inp (T.diagVM own)
    (T.diagSetup pc) (T.diag_link pc dfs saved common own done M installed) (fun _ j => banks.inputs _ j) c entry
  have val (i) := (aval i).trans (DiagonalFrame.values X v P hD hd internal A child parent oldDir newDir Q src term
    T.input pub state m args oldCols newCols stored.segments wide i)
  simp only [T.outputs own] at val
  obtain ⟨b,scan,bpc,bmem,bper,bframe⟩ := RefreshDiagonal.compare_arguments X v P hD hd internal
    (T.compare_link pc dfs saved common own done M installed) A child parent old new a
    (apc.trans (dite_eq_right (Nat.lt_irrefl _))) (amem ▸ oldData) (amem ▸ newData)
    ⟨⟨val 0,val 1,val 2⟩,⟨val 3,val 4,val 5⟩⟩ wo wi
  rw [ite_eq_left ok] at bpc
  have bReg (j) (hj : ∀ i, j ≠ own i) : b.reg j = c.reg j :=
    (bframe j (fun ⟨i,e⟩ => hj _ e.symm)).trans (aframe j (fun _ => hj _))
  have bInputs (i) : b.reg (inp i) = c.reg (inp i) := bReg _ (fun j => (banks.inputs j i).symm)
  have bPub : (fun i : Fin 5 => b.reg (inp i.castSucc)) = pub := funext fun i => bInputs i.castSucc
  obtain ⟨d,third,dlen,dp',db,dpc,dmem,dper,dvals,dframe⟩ := setup_exact M m T.route inp (T.routeVM own)
    (T.routeSetup pc) (T.route_link pc dfs saved common own done M installed) (fun _ j => banks.inputs _ j) b bpc
  rw [bPub,bInputs (Fin.last 5)] at third dlen dp' db dvals
  have keys := MapRoute.values B X choice v A child parent oldDir newDir T.ties start T.stride m T.input pub state
    args stored wide
  obtain ⟨out,dispatch,exit,frame,mem,pers⟩ := RefreshResidentDispatch.keys_hit B T.input T.stride (T.routeVM own)
    (T.routePC pc) (fun q j => T.family.target (T.handlerPC pc) (q,j)) (T.bad pc) X v M
    (T.dispatch_link pc dfs saved common own done M installed) d (dpc.trans (dite_eq_right (Nat.lt_irrefl _)))
    ((funext dvals).symm ▸ keys) wide
  change (setupEvents T.diagonal pub state m).length = _ at alen
  change (setupEvents T.route pub state m).length = _ at dlen
  change countProbes (setupEvents T.diagonal pub state m) = _ at ap
  change countProbes (setupEvents T.route pub state m) = _ at dp'
  change choiceBits (setupEvents T.diagonal pub state m) = _ at ab
  change choiceBits (setupEvents T.route pub state m) = _ at db
  refine ⟨out,(first.trans (tickPrefix M m scan)).trans (third.trans (tickPrefix M m dispatch)),?_,?_,?_,exit,?_,
    mem.trans (dmem.trans (bmem.trans amem)),pers.trans (dper.trans (bper.trans aper))⟩
  · simp only [es,frontEvents,List.length_append,List.length_replicate,alen,dlen]
  · simp only [es,frontEvents,countProbes_append,ap,dp',ticks.2,Nat.add_zero]
  · simp only [es,frontEvents,PrimedInputRAM.Flow.choiceBits_append,ab,db,ticks.1,List.nil_append]
  · intro j hj
    exact (frame j (fun _ => hj _)).trans ((dframe j (fun _ => hj _)).trans (bReg j hj))

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
