import OAI.ThreeFlat.Diagonal.TickPositiveMatrix
import OAI.ThreeFlat.Diagonal.TraceSeedLocal
import OAI.ThreeFlat.Diagonal.AlignedChunkVisit
import OAI.ThreeFlat.RAM.PhysicalPreparedMatrix
import OAI.ThreeFlat.Diagonal.NavigationCursorPairSpace
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.Diagonal.NavigationSlotSchedule
import OAI.ThreeFlat.Diagonal.TickScheduledInput
import OAI.ThreeFlat.Diagonal.TickInstalledExecution
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.RAM.TickTerminalPrepare

namespace OAI
/-! # The selected cell forests of a physically decoded team entry -/

set_option quotPrecheck false

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets

open HistoryContraction TickChronology TickAuxiliary
open RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM RAM.HistoryFactors
open scoped Classical BigOperators
variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {E : P.Codes}
  {bits : P.History → ℕ} {A : RAM.TickActiveROM.Layout} {c : Clock} {R : GroupRegister P E bits A.bits}
  {lanes span p H J w raw teams : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) w}
  (T : Buckets P bits c A.bits lanes span)

structure Forest (A : RAM.TickActiveROM.Layout) (F : Type*) [Field F] [Fintype F] (p H J w : ℕ) where
  net : BitNetwork F p
  lib : Library net
  hidden : net.internal≤H
  cells : net.cells+(H-net.internal)≤J
  lut : A.lut+8*(lib.count+2)≤2^w

def Forest.input (f : Forest A F p H J w) (v : Plan.Terminal P bits) (t : ℕ) (oa : Aux A.bits)
    (room : 1+A.capacity+2*T.length v (c.group t)≤A.bits) : CellInput A c fit :=
  T.cellInput v t oa room f.net f.lib f.hidden f.cells f.lut

/-- Each processor equation uses the real forest if the native shared-record decoder
admits it. This statement has no opaque AUX, scan, or dynamically chosen layout assumption. -/
theorem scheduled_team (t : ℕ) (pos : 0<teams) (N : BitNetwork F raw)
    (rawPins : Fin teams → Fin raw → Bool) (pin : Fin teams → Fin p → Bool)
    (oa na oc nc : Aux A.bits) (room : ∀ v g, 1+R.capacity+2*T.length v g≤A.bits)
    (weights : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (reserve : A.capacity=R.capacity) (forest : Plan.Terminal P bits → Fin teams → Forest A F p H J w)
    (eval : ∀ v, decode P E bits R.base (if c.phase t=.opening then na else oa)=some v →
      c.phase t=.evaluate → (∏ k, (forest v k).net.eval (pin k)) =
      weights v (c.group t) (before (T.data room weights) v (c.group t) oa)
        (after (T.data room weights) v (c.group t) oa) t) :
    let records := decode P E bits R.base (if c.phase t=.opening then na else oa)
    let input := fun v k => (forest v k).input (fit:=fit) T v t oa (by rw [reserve]; exact room v (c.group t))
    (∀ k, N.eval (rawPins k) =
      if branch R.base (c.phase t) oa na then
        records.elim 0 (fun v => (input v k).weight (c.phase t) oa na oc nc (pin k))
      else if oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc then 1 else 0) →
    (∏ k, N.eval (rawPins k)) = localValue (T.data room weights) t oc nc oa na := by
  intro records input member
  cases known : records with
  | none =>
    have none' : decode P E bits R.base (if c.phase t=.opening then na else oa)=none := known
    simp_rw [member,known,Option.elim_none]
    by_cases idOK : oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc
    · have tag : branch R.base (c.phase t) oa na=false := by
        obtain ⟨o,n,_⟩ := idOK
        simp [branch,o,n]
      simp only [localValue,none',Option.elim_none,tag,Bool.false_eq_true,ite_false,
        ite_eq_left idOK,Finset.prod_const_one,add_zero]
    · simp [localValue,none',idOK,Nat.ne_of_gt pos]
  | some v =>
    have dec : decode P E bits R.base (if c.phase t=.opening then na else oa)=some v := known
    apply installed_team (T.data room weights) t pos N rawPins pin oa na oc nc (input v) (fun _=>True)
    · intro k
      simp [dec]
    · intro k
      rw [member,known]
      simp [branch_layout (R:=R)]
    · intro v' selected
      have eq : v'=v := Option.some.inj (selected.symm.trans dec)
      subst v'
      refine ⟨fun k => ?_,fun _ k => ?_,fun ev => ?_⟩
      · let f := forest v k
        exact T.cellInput_aux v t oa room weights reserve f.net f.lib f.hidden f.cells f.lut
      · let f := forest v k
        exact T.cellInput_guard v t oa room weights reserve f.net f.lib f.hidden f.cells f.lut oc nc
      · calc (∏ k, (input v k).net.eval (pin k)) = ∏ k, (forest v k).net.eval (pin k) := by
              apply Finset.prod_congr rfl
              intro k _
              exact TraceCircuit.addPadding_eval ..
            _ = _ := eval v dec ev


end ThreeFlat.Diagonal.TickPhaseModel.Buckets

namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets
open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM ApproximateImage TraceStartupAtScale
open HistoryContraction TickChronology TickAuxiliary RAM RAM.ContinuationLink RAM.TickMachine
open RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM.TickMountedPins
open scoped Classical BigOperators

private def forestPreparation (F : Type) [Field F] [Fintype F] (w u p H J : ℕ)
    (fit : Fits (TickWeightedBank.shape F p H J) w) (wireStart wirePrefix : ℕ)
    (archive : HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (publicWords : Fin TraceEndpointROM.params → Word w) (families : List HistoryStageBody.Physical.Family)
    (startup : TracePrototypeBoot.Args w) : PhysicalProcedure.Procedure w :=
  TickTerminalRoot.prepare (F:=F) (W:=w) (codec (p:=p) (w:=w) (TickWeightedBank.shape F p H J) fit)
    u p H J wireStart wirePrefix archive shape publicWords families startup

variable {F : Type} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {E : P.Codes}
  {bits : P.History → ℕ} {u e nt ns pk H J teams capacity lanes span : ℕ}
local notation "W" => (16*u^10)
local notation "Q" => (2^(u^3))
local notation "A" => (2^(u^10-u^4))
local notation "PINS" => pinCount Q nt ns pk A
local notation "B" => TickPhysicalABI.mounted u A teams capacity Q nt ns pk

variable (fit : Fits (TickWeightedBank.shape F
    (pinCount (2^(u^3)) nt ns pk (2^(u^10-u^4))) H J) (16*u^10))
  (config : NavigationPass.Parameters) (block : PhysicalStage.Block F) (blocks residualBits : ℕ)
  (wireStart wirePrefix : ℕ) (archive : HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
  (publicWords : Fin TraceEndpointROM.params → Word (16*u^10)) (families : List HistoryStageBody.Physical.Family)
  (startup : TracePrototypeBoot.Args (16*u^10))

local notation "NV" => config.machine («W»:=W) block blocks residualBits
local notation "PR" => forestPreparation F W u PINS H J fit
  wireStart wirePrefix archive shape publicWords families startup

variable (roots : Plan.Terminal P bits → Fin teams → ℕ)
  (arity : ∀ v k, Fin (roots v k) → ℕ)
  (nets : ∀ v k i, BitNetwork F (arity v k i))
  (wires : ∀ v k i, Fin (arity v k i) → Fin (pinCount (2^(u^3)) nt ns pk (2^(u^10-u^4))))
local notation "G" => (fun v k => TickSlotForest.network (HistoryTerminalJoin.projected (nets v k) (wires v k)))

set_option maxHeartbeats 1600000 in
set_option cleanup.letToHave false in
attribute [local irreducible] TickTerminalRoot.prepare NavigationPass.Parameters.machine in
/-- On the actual unshifted pins, the product of the universal trace across a team
is the per-tick scalar of the positive chronological matrix. The two procedure
specifications refer to the canonical parsed history at these exact physical pins. -/
theorem scheduled_team_shifted (hu : cutoff≤u) (hq : Fintype.card F≤u) (he : e≤u)
    (hparams : nt+ns+pk≤u^e) (c : Clock)
    (largeText : textCutoff F (NV).labels (PR).labels (NV).registers (PR).registers (NV).slots (PR).slots≤u)
    (labelRoom : 37+(3400+9*(Fintype.card F*Fintype.card F)+(NV).labels+(PR).labels)≤u)
    (publicRoom : 6+TickPublicData.count (NV).slots (PR).slots≤u)
    (T : Buckets P bits c A lanes span) (R : GroupRegister P E bits A)
    (reserve : capacity=R.capacity) (room : ∀ v g, 1+R.capacity+2*T.length v g≤A)
    (weights : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (hidden : ∀ v k, (G v k).internal≤H) (cells : ∀ v k, (G v k).cells+(H-(G v k).internal)≤J)
    (strideRoom : 52≤TickWorkspace.stride u) (low : cellsBase PINS H≤TickWorkspace.stride u)
    (storage : 4*J≤TickWorkspace.stride u) (tables : 8*(TickTerminalPadding.tables F+2)≤TickWorkspace.stride u)
    (tail : Fin Q → Bool) (par : Fin pk → Bool) (oa na oc nc : Aux A)
    (t C : ℕ) (st : Word W) (pos : 0<teams)
    (ft : teams≤2^nt) (fs : t<2^ns) (wt : teams≤2^W) (ws : t<2^W)
    (dur : c.groupDuration<2^W) (last : c.last<2^W) (begin : c.beginTick<2^W)
    (space : WordBounds B fit) (exponent : e+1+TraceVolume.cm≤u)
    (ageConstant : 8*((max (11161+28*C) (8*68))+124)≤u)
    (identifierCost : nt+ns≤TickTotalBudget.replayBound u e C) :
    let native := linkedProgram B c fit (NV).block (PR).block (NV).publicData (PR).publicData largeText Q nt ns
    let M := shiftedProgram PINS hu native
    let hp : (TickHeaderShift.procedure W PINS).labels+
        Fintype.card (All (n:=(NV).labels) (m:=(PR).labels) (k:=TickPublicData.count (NV).slots (PR).slots) B c fit)≤u := by
      rw [(TickHeaderShift.text W PINS).1]
      exact (Nat.add_le_add_left (text_count B c fit) 37).trans labelRoom
    let hk : (TickHeaderShift.procedure W PINS).slots+TickPublicData.count (NV).slots (PR).slots≤u := by
      rwa [(TickHeaderShift.text W PINS).2.2]
    let D := installProgram (CapacityPadding.pad M hp (Nat.le_refl u) hk) tail
    let ph := c.phase t
    let pin := fun (k : Fin teams) => fields D (digits k.val nt) (digits t ns) par oa na oc nc
    let start := fun k : Fin teams => TickNavigationEntry.input B c k.val t (TickMountedPins.memory (w:=W) (pin k))
    let field : FieldCode F W := codec (p:=PINS) (w:=W) (TickWeightedBank.shape F PINS H J) fit
    let record := decode P E bits R.base (if ph=.opening then na else oa)
    let forest := fun v k => (⟨G v k,HistoryCompiledRows.library (G v k),hidden v k,cells v k,by
      change TickWorkspace.base u 10+8*(TickTerminalPadding.tables F+2)≤2^W
      exact (Nat.add_le_add_left tables _).trans (TickWorkspace.word_space (i:=10)
        (show 1≤u by have := large hu; omega) (by omega)).le⟩ : Forest B F PINS H J W)
    let input := fun v k => (forest v k).input (fit:=fit) T v t oa
      (by change 1+capacity+2*T.length v (c.group t)≤A; rw [reserve]; exact room v (c.group t))
    (∀ v, record=some v → ph=.evaluate → (∏ k, (forest v k).net.eval (pin k)) =
      weights v (c.group t) (before (T.data room weights) v (c.group t) oa)
        (after (T.data room weights) v (c.group t) oa) t) →
    (∀ v, record=some v → ∀ k : Fin teams,
      ∃ (navTime inside finishTime replay selected suffix : ℕ) (pre admitted slotInput : Memory W → Prop)
          (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W),
        2*head.roots≤TickWorkspace.stride u/4 ∧
        TickStageSpec.Admission field (NV).block (NV).publicData pre admitted
            (fun _ out => NavOutput (input v k) ph oa na oc nc slotInput out) navTime ∧
        pre (start k) ∧ admitted (start k) ∧
        ((startup.procedure u).seq (HistoryStageBody.Physical.selected W u archive shape publicWords families)).Spec slotInput
          (fun _ m => TickTerminalRoot.terminalInput (u:=u) (H:=H) (J:=J) (nets v k) (wires v k)
            (pin k) wireStart wirePrefix head own finishTime m) inside ∧
        let charges := TickTotalBudget.charges (input v k) nt ns navTime (inside+finishTime) replay selected suffix
        8*(TickTotalBudget.coefficient charges C+124)≤u ∧
          TickTotalBudget.Bounds charges (TraceVolume.cap u) (TickTotalBudget.replayBound u e C)) →
    (record=none → ∀ k : Fin teams,
      ∃ (navTime : ℕ) (pre admitted : Memory W → Prop) (post : Memory W → Memory W → Prop),
        TickStageSpec.Admission field (NV).block (NV).publicData pre admitted post navTime ∧ pre (start k) ∧
        ¬admitted (start k) ∧ navTime≤TickTotalBudget.replayBound u e C) →
    (∏ k, (TraceStartupAtScale.network hu hq he hparams 0 st).eval
      (fun i => pin k (i.cast (fields_size Q nt ns pk A)))) =
      localValue (T.data room weights) t oc nc oa na := by
  intro native M hp hk D ph pin start field record forest input eval valid invalid
  apply T.scheduled_team (fit:=fit) t pos (TraceStartupAtScale.network hu hq he hparams 0 st)
    (fun k i => pin k (i.cast (fields_size Q nt ns pk A))) pin oa na oc nc room weights reserve forest eval
  intro k
  change _ = (if branch R.base ph oa na then record.elim 0 (fun h => (input h k).weight ph oa na oc nc (pin k))
    else if oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc then 1 else 0)
  cases parsed : record with
  | some v =>
    obtain ⟨navTime,inside,finishTime,replay,selected,suffix,pre,admitted,slotInput,
      head,own,ownerSpace,admission,init,yes,generated,big,bounds⟩ := valid v parsed k
    have prepared : TickStageSpec.Prepare (PR).block (PR).publicData slotInput
        (fun _ out => TickWeightedBank.Ready fit (input v k).net (input v k).lib
          (pin k) (B).metadata (B).lut out) (inside+finishTime) := by
      intro pcs registers slots machine
      exact TickTerminalRoot.prepare_compiled (nets v k) (wires v k) (pin k)
        wireStart wirePrefix fit head own archive shape publicWords families startup slotInput inside finishTime
        generated ((by decide : 1≤128).trans (large hu)) strideRoom ownerSpace (hidden v k) (cells v k)
        low storage tables machine
    have run := eval_installed_shifted hu hq he hparams c fit (NV).block (PR).block (NV).publicData (PR).publicData largeText labelRoom publicRoom
      (input v k) tail par oa na oc nc k.val t navTime (inside+finishTime) replay selected suffix C st
      (k.isLt.trans_le ft) fs (k.isLt.trans_le wt) ws dur last begin space pre admitted slotInput
      admission init prepared big exponent bounds
    change _ = (if branch (input v k).aux ph oa na then (input v k).weight ph oa na oc nc (pin k)
      else if oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc then 1 else 0)
    change _ = (if branch (input v k).aux ph oa na then
      (if admitted (start k) then (input v k).weight ph oa na oc nc (pin k) else 0)
      else if oa=(fun _=>false) ∧ na=(fun _=>false) ∧ oc=nc then 1 else 0) at run
    rw [ite_eq_left yes] at run
    exact run
  | none =>
    obtain ⟨navTime,pre,admitted,post,admission,init,bad,bound⟩ := invalid parsed k
    have run := eval_rejected_shifted hu hq he hparams c fit (NV).block (PR).block (NV).publicData (PR).publicData largeText labelRoom publicRoom
      R.base tail par oa na oc nc k.val t navTime C st (k.isLt.trans_le ft) fs (k.isLt.trans_le wt) ws
      dur last begin space pre admitted post ageConstant exponent identifierCost bound admission init bad
    exact run


set_option maxHeartbeats 600000 in
/-- The selected native row scans and explicit rejection on the actually mounted
record. The per-slot predicate carries clocks, RAM addresses and the cursor predicate
passed between the two emitted instruction tables. -/
def NativeRows (R : GroupRegister P E bits A) (c : Clock)
    (input : Plan.Terminal P bits → Fin teams → CellInput (F:=F) (p:=PINS) (H:=H) (J:=J) (w:=W) B c fit)
    (D : Fin Q→Bool) (par : Fin pk→Bool) (oa na oc nc : Aux A) (t C : ℕ) : Prop :=
    let ph:=c.phase t
    let pin:=fun k : Fin teams=>fields D (digits k.val nt) (digits t ns) par oa na oc nc
    let start:=fun k : Fin teams=>TickNavigationEntry.input B c k.val t (TickMountedPins.memory (w:=W) (pin k))
    let field : FieldCode F W := codec (p:=PINS) (w:=W) (TickWeightedBank.shape F PINS H J) fit
    let record:=decode P E bits R.base (if ph=.opening then na else oa)
    (∀ v, record=some v → ∀ k : Fin teams,
      ∃ (navTime inside finishTime replay selected suffix : ℕ) (pre admitted slotInput : Memory W → Prop)
          (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W),
        2*head.roots≤TickWorkspace.stride u/4 ∧
        TickStageSpec.Admission field (NV).block (NV).publicData pre admitted
            (fun _ out => NavOutput (input v k) ph oa na oc nc slotInput out) navTime ∧
        pre (start k) ∧ admitted (start k) ∧
        ((startup.procedure u).seq (HistoryStageBody.Physical.selected W u archive shape publicWords families)).Spec slotInput
          (fun _ m => TickTerminalRoot.terminalInput (u:=u) (H:=H) (J:=J) (nets v k) (wires v k)
            (pin k) wireStart wirePrefix head own finishTime m) inside ∧
        let charges := TickTotalBudget.charges (input v k) nt ns navTime (inside+finishTime) replay selected suffix
        8*(TickTotalBudget.coefficient charges C+124)≤u ∧
          TickTotalBudget.Bounds charges (TraceVolume.cap u) (TickTotalBudget.replayBound u e C)) ∧
    (record=none → ∀ k : Fin teams,
      ∃ (navTime : ℕ) (pre admitted : Memory W → Prop) (post : Memory W → Memory W → Prop),
        TickStageSpec.Admission field (NV).block (NV).publicData pre admitted post navTime ∧ pre (start k) ∧
        ¬admitted (start k) ∧ navTime≤TickTotalBudget.replayBound u e C)

/-- Uniform age threshold for the finite LUT on every cell of one field. -/
def fieldClock (F : Type*) [Fintype F] (C : ℕ) : ℕ :=
  let entries:=TickTerminalPadding.tables F+2
  let square:=Fintype.card F*Fintype.card F
  8*(max (11161+28*C) (8*(64+(4+8*entries*(6*(8*entries)+10))+square*(6*square+10)))+124)

/-- The accepted navigator's explicit published time and every original scan row
fit the same replay allowance. This uses the two real halves of the cursor height. -/
theorem cursor_replay_bounds {age low lanes e C nt ns : ℕ} (large : 40≤age)
    (exp : 20≤e) (constant : 104000≤C)
    (half : low=age^10/2) (depth : lanes+low≤age^10+2*age^6)
    (publicIDs : nt+ns≤age^e) :
    TickTotalBudget.replayBound age 20 104000≤TickTotalBudget.replayBound age e C ∧
    2^lanes≤TickTotalBudget.replayBound age e C ∧
    ns+nt≤TickTotalBudget.replayBound age e C := by
  let a:=TickTotalBudget.chunk age
  have pa : 0<a:=Nat.two_pow_pos _
  have pc : 0<C:=by omega
  have pu : 0<age^e:=Nat.pow_pos (by omega)
  have base : a≤C*age^e*a:= by exact Nat.le_mul_of_pos_left _ (Nat.mul_pos pc pu)
  have uBound : age^e≤C*age^e*a:=
    (Nat.le_mul_of_pos_left _ pc).trans (Nat.le_mul_of_pos_right _ pa)
  have count:=PhysicalStage.register_exponents (e:=0) (by omega : 16≤age) (Nat.zero_le age) half depth
  have lanesBound : 2^lanes≤a := by
    have hh:=count.1
    simp only [pow_zero,one_mul] at hh
    change 2^lanes≤2^(age^10-age^4)
    omega
  refine ⟨?_,lanesBound.trans base,?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul constant (Nat.pow_le_pow_right (by omega) exp))
  · change ns+nt ≤ C*age^e*a
    rw [Nat.add_comm ns nt]
    exact publicIDs.trans uBound

omit [Fintype F] in
/-- The compact admission grid has exactly one bucket row for each numerical lane. -/
theorem native_scan_count {S : HistoryContraction.Shape} {P : Plan F S} {bits : P.History→ℕ}
    {layout : RAM.TickActiveROM.Layout} {lanes span : ℕ} {c : Clock}
    (T : Buckets P bits c layout.bits lanes span) (v : Plan.Terminal P bits) :
    (finiteRows («A»:=layout) T v).length=lanes := by
  simp only [finiteRows,List.length_map,Plan.bucketRows,BucketRows.pack_length,
    Buckets.rows,ClippedPairBuckets.rows,List.length_ofFn]

set_option maxHeartbeats 600000 in
/-- Assemble the actual typed admission and selected-row subroutines. On phases other
than evaluation the installed phase dispatch never runs the selection program. -/
theorem rows_of_navigation (R : GroupRegister P E bits A) (c : Clock)
    (input : Plan.Terminal P bits→Fin teams→CellInput (F:=F) (p:=PINS) (H:=H) (J:=J) (w:=W) B c fit)
    (D : Fin Q→Bool) (par : Fin pk→Bool) (oa na oc nc : Aux A) (t C : ℕ)
    (smallH : H≤TraceVolume.cap u/40000) (smallJ : J≤2*(TraceVolume.cap u/40000))
    (ids : ns+nt≤TickTotalBudget.replayBound u e C)
    (rows : ∀ v k,(input v k).intervals.length≤TickTotalBudget.replayBound u e C)
    (age : fieldClock F C≤u)
    (lib : ∀ v k,(input v k).lib.count=TickTerminalPadding.tables F+2) :
    let ph:=c.phase t
    let pin:=fun k : Fin teams=>fields D (digits k.val nt) (digits t ns) par oa na oc nc
    let start:=fun k : Fin teams=>TickNavigationEntry.input B c k.val t (TickMountedPins.memory (w:=W) (pin k))
    let field : FieldCode F W := codec (p:=PINS) (w:=W) (TickWeightedBank.shape F PINS H J) fit
    let recd:=decode P E bits R.base (if ph=.opening then na else oa)
    (∀ v,recd=some v→∀ k : Fin teams,
      ∃ (time : ℕ) (slot : Memory W→Prop),
        TickStageSpec.Admission field (NV).block (NV).publicData (·=start k) (fun _=>True)
          (fun _ out=>NavOutput (input v k) ph oa na oc nc slot out) time ∧
        time≤TickTotalBudget.replayBound u e C ∧
        (ph=.evaluate → ∃ (inside finishTime : ℕ) (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W),
          2*head.roots≤TickWorkspace.stride u/4 ∧
          ((startup.procedure u).seq (HistoryStageBody.Physical.selected W u archive shape publicWords families)).Spec slot
            (fun _ m=>TickTerminalRoot.terminalInput (u:=u) (H:=H) (J:=J) (nets v k) (wires v k)
               (pin k) wireStart wirePrefix head own finishTime m) inside ∧ inside+finishTime≤TraceVolume.cap u/4)) →
    (recd=none→∀ k : Fin teams,∃ time,
      TickStageSpec.Admission field (NV).block (NV).publicData (·=start k) (fun _=>False) (fun _ _=>False) time ∧
      time≤TickTotalBudget.replayBound u e C) →
    NativeRows (fit:=fit) (config:=config) (block:=block) (blocks:=blocks) (residualBits:=residualBits)
      (wireStart:=wireStart) (wirePrefix:=wirePrefix) (archive:=archive) (shape:=shape) (publicWords:=publicWords)
      (families:=families) (startup:=startup) (roots:=roots) (arity:=arity)
      (nets:=nets) (wires:=wires) (e:=e) R c input D par oa na oc nc t C := by
  intro ph pin start field recd yes no
  constructor
  · intro v dec k
    obtain ⟨time,slot,nav,timeFit,prep⟩:=yes v dec k
    have bounds (z : ℕ) (hz : z≤TraceVolume.cap u/4) :
        8*(TickTotalBudget.coefficient (TickTotalBudget.charges (input v k) nt ns time z 0 z 0) C+124)≤u ∧
        TickTotalBudget.Bounds (TickTotalBudget.charges (input v k) nt ns time z 0 z 0)
          (TraceVolume.cap u) (TickTotalBudget.replayBound u e C) := by
      constructor
      · simpa only [TickTotalBudget.coefficient,TickTotalBudget.Charges.lookup,TickTotalBudget.Charges.fieldCost,
          TickTotalBudget.charges,fieldClock,lib] using age
      · exact ⟨ids,rows v k,timeFit,Nat.zero_le _,hz,by dsimp [TickTotalBudget.charges];omega,
          Nat.zero_le _,smallH,smallJ⟩
    by_cases ev : ph=.evaluate
    · obtain ⟨inside,finish,head,own,owner,run,cost⟩:=prep ev
      exact ⟨time,inside,finish,0,inside+finish,0,(·=start k),(fun _=>True),slot,head,own,
        owner,nav,rfl,True.intro,run,(bounds _ cost).1,(bounds _ cost).2⟩
    · let head : TickPhysicalABI.NavigationHeader:=⟨0,0,0,0⟩
      let own : TickSlotLookup.Owner W:=fun _=>(0,0)
      refine ⟨time,0,0,0,0,0,(·=start k),(fun _=>True),(fun _=>False),head,own,Nat.zero_le _,?_,rfl,True.intro,?_,
        (bounds 0 (Nat.zero_le _)).1,(bounds 0 (Nat.zero_le _)).2⟩
      · intro labels regs slots M
        refine TickStageSpec.Admission.mono (pre':=(·=start k)) (good':=fun _=>True)
          (post':=fun _ out=>NavOutput (input v k) ph oa na oc nc (fun _=>False) out)
          nav (fun _ h=>h) (fun _ _=>Iff.rfl) ?_ (Nat.le_refl time) M
        intro _ out _ _ ready
        exact {ready with evalInputs:=fun h=>(ev h).elim}
      · intro labels regs words M pc reg data exit installed params st m atPC impossible
        exact impossible.elim
  · intro bad k
    obtain ⟨time,nav,bound⟩:=no bad k
    exact ⟨time,(·=start k),(fun _=>False),(fun _ _=>False),nav,rfl,not_false,bound⟩


set_option maxHeartbeats 1600000 in
set_option cleanup.letToHave false in
attribute [local irreducible] TickTerminalRoot.prepare NavigationPass.Parameters.machine in
/-- The physical instruction-level positive diagonal. All inputs use one padded tick program,
a single self-description carrying both H and X, and the same row-major tick network at
every time. On a matching decoded history the selected native procedures execute its
actual forest. On a malformed history their rejecting computation supplies zero. -/
theorem scheduled_positive (hu : cutoff≤u) (hq : Fintype.card F≤u) (he : e≤u)
    (hparams : nt+ns+pk≤u^e) (c : Clock)
    (largeText : textCutoff F (NV).labels (PR).labels (NV).registers (PR).registers (NV).slots (PR).slots≤u)
    (labelRoom : 37+(3400+9*(Fintype.card F*Fintype.card F)+(NV).labels+(PR).labels)≤u)
    (publicRoom : 6+TickPublicData.count (NV).slots (PR).slots≤u)
    (T : Buckets P bits c A lanes span) (R : GroupRegister P E bits A)
    (reserve : capacity=R.capacity) (room : ∀ v g, 1+R.capacity+2*T.length v g≤A)
    (weights : ∀ v g, Aux (T.length v g)→Aux (T.length v g)→ℕ→F)
    (labels : ∀ h,(Fin (bits h)→Bool)≃(P.finish h).Boundary)
    (rootsAt : ℕ→Plan.Terminal P bits→Fin teams→ℕ)
    (arityAt : ∀ t v k,Fin (rootsAt t v k)→ℕ)
    (netsAt : ∀ t v k i,BitNetwork F (arityAt t v k i))
    (wiresAt : ∀ t v k i,Fin (arityAt t v k i)→Fin PINS)
    (hidden : ∀ t v k,(TickSlotForest.network (HistoryTerminalJoin.projected (netsAt t v k) (wiresAt t v k))).internal≤H)
    (cells : ∀ t v k,let n:=TickSlotForest.network (HistoryTerminalJoin.projected (netsAt t v k) (wiresAt t v k))
      n.cells+(H-n.internal)≤J)
    (strideRoom : 52≤TickWorkspace.stride u) (low : cellsBase PINS H≤TickWorkspace.stride u)
    (storage : 4*J≤TickWorkspace.stride u) (tables : 8*(TickTerminalPadding.tables F+2)≤TickWorkspace.stride u)
    {payload : ℕ} (Hprog Xprog : Machine W u u u) (seed : Fin (FoldSuffixScale.extraSize u)→Bool)
    (fixed : Fin payload→Bool) (par : Fin pk→Bool) (C : ℕ) (st : Word W) (pos : 0<teams)
    (ft : teams≤2^nt) (fs : c.last+1≤2^ns) (wt : teams≤2^W)
    (dur : c.groupDuration<2^W) (last : c.last<2^W) (begin : c.beginTick<2^W)
    (space : WordBounds B fit) (exponent : e+1+TraceVolume.cm≤u)
    (ageConstant : 8*((max (11161+28*C) (8*68))+124)≤u)
    (identifierCost : nt+ns≤TickTotalBudget.replayBound u e C)
    (inside period lastBlock paramBase templateBase : ℕ) [NeZero period]
    (size : c.chunks=2*(period*(inside+1))) (duration : (lastBlock+1)*(inside+1)=c.last+1) :
    let s : PhysicalPinsExpr.Shape := ⟨Q,nt,ns,pk,A,inside,teams,period,lastBlock,paramBase,templateBase⟩
    let order := AlignedChunks.order (period:=s.period) (width:=s.inside+1) c size
    let load := fun (x y : Bool→Fin s.chunks→Aux A) =>
      TraceBitHeader.endpointPin (PhysicalPinsInput.externalBits x) (PhysicalPinsInput.externalBits y)
    let native := linkedProgram B c fit (NV).block (PR).block (NV).publicData (PR).publicData largeText Q nt ns
    let M := shiftedProgram PINS hu native
    let hp : (TickHeaderShift.procedure W PINS).labels+
        Fintype.card (All (n:=(NV).labels) (m:=(PR).labels) (k:=TickPublicData.count (NV).slots (PR).slots) B c fit)≤u := by
      rw [(TickHeaderShift.text W PINS).1]
      exact (Nat.add_le_add_left (text_count B c fit) 37).trans labelRoom
    let hk : (TickHeaderShift.procedure W PINS).slots+TickPublicData.count (NV).slots (PR).slots≤u := by
      rwa [(TickHeaderShift.text W PINS).2.2]
    let tick := CapacityPadding.pad M hp (Nat.le_refl u) hk
    let D := FoldSuffixScale.description tick Hprog Xprog seed fixed Q
    let net := fun t v k => TickSlotForest.network (HistoryTerminalJoin.projected (netsAt t v k) (wiresAt t v k))
    ∀ (X : BitNetwork F (s.area+2*s.halfBits)) (V : Form S (Fin (2*(s.halfBits+s.halfBits))→Bool))
       (assembly : P.Assembly V) (trees : HistoryContraction.Forest F V),
    (∀ v (g : Fin c.groups) x y,((TickRangeChronology.evalTicks c g.val).map
      (weights v g.val (T.read v g x) (T.read v g y))).prod =
      ∏ i : {i // T.group v.1 i=g},(P.assemble v.1 assembly trees).1.values (P.assemble v.1 assembly trees).2
        (load (TickPhysicalOrder.unpack order x) (TickPhysicalOrder.unpack order y)) i.val
        ((P.finish v.1).graph.atVertex (labels v.1 v.2) i.val)) →
    (∀ t, t<c.last+1 → ∀ (oa na oc nc : Aux A),
    let ph := c.phase t
    let pin := fun (k : Fin teams) => fields D (digits k.val nt) (digits t ns) par oa na oc nc
    let _start := fun k : Fin teams => TickNavigationEntry.input B c k.val t (TickMountedPins.memory (w:=W) (pin k))
    let _field : FieldCode F W := codec (p:=PINS) (w:=W) (TickWeightedBank.shape F PINS H J) fit
    let record := decode P E bits R.base (if ph=.opening then na else oa)
    let forest := fun v k => (⟨net t v k,HistoryCompiledRows.library (net t v k),hidden t v k,cells t v k,by
      change TickWorkspace.base u 10+8*(TickTerminalPadding.tables F+2)≤2^W
      exact (Nat.add_le_add_left tables _).trans (TickWorkspace.word_space (i:=10)
        (show 1≤u by have := large hu; omega) (by omega)).le⟩ : Forest B F PINS H J W)
    let input : Plan.Terminal P bits → Fin teams → CellInput (F:=F) (p:=PINS) (H:=H) (J:=J) (w:=W) B c fit :=
      fun v k => (forest v k).input (fit:=fit) T v t oa
        (by change 1+capacity+2*T.length v (c.group t)≤A; rw [reserve]; exact room v (c.group t))
    (∀ v, record=some v → ph=.evaluate → (∏ k, (forest v k).net.eval (pin k)) =
      weights v (c.group t) (before (T.data room weights) v (c.group t) oa)
        (after (T.data room weights) v (c.group t) oa) t) ∧
    NativeRows (fit:=fit) (config:=config) (block:=block) (blocks:=blocks) (residualBits:=residualBits)
      (wireStart:=wireStart) (wirePrefix:=wirePrefix) (archive:=archive) (shape:=shape) (publicWords:=publicWords)
      (families:=families) (startup:=startup) (roots:=rootsAt t) (arity:=arityAt t)
      (nets:=netsAt t) (wires:=wiresAt t) (e:=e) R c input D par oa na oc nc t C) →
    (∀ x y, (∑ h : P.History, ∑ b : (P.finish h).Boundary, ∏ v,
        (P.assemble h assembly trees).1.values (P.assemble h assembly trees).2 (load x y) v
          ((P.finish h).graph.atVertex b v)) = approximatedMatrix X D
          (fun i=>select (nt:=nt) (ns:=ns) (teams:=teams) i.val par)
          (fun i=>s.slots i.val) s.choice s.retained x y) →
    templateRun (cast (congrArg (BitNetwork F) (fields_size Q nt ns pk A)) (network hu hq he hparams 0 st))
      (List.ofFn id) (fun i : Fin (lastBlock+1)=>s.slots i.val) s.choice
      (fun i=>tickPins (nt:=nt) (ns:=ns) (teams:=teams) D i.val par) =
      1 + approximatedMatrix X D (fun i=>select (nt:=nt) (ns:=ns) (teams:=teams) i.val par)
        (fun i=>s.slots i.val) s.choice s.retained := by
  classical
  intro s order load native M hp hk tick D net X V assembly trees groups records cursor
  apply T.positive_forest s room weights labels par tick Hprog Xprog seed fixed
    (network hu hq he hparams 0 st) X V assembly trees size duration groups _ cursor
  intro b j oc nc oa na
  let t:=b.val*(inside+1)+j.val
  have time : t<c.last+1 := by
    rw [←duration]
    have tail:=Nat.mul_le_mul_right (inside+1) (show b.val+1≤lastBlock+1 from b.isLt)
    rw [Nat.succ_mul] at tail
    have slot : j.val < inside+1 := j.isLt
    exact (Nat.add_lt_add_left slot (b.val*(inside+1))).trans_le tail
  obtain ⟨projected,valid,invalid⟩:=records t time oa na oc nc
  exact T.scheduled_team_shifted fit config block blocks residualBits wireStart wirePrefix archive shape
    publicWords families startup (rootsAt t) (arityAt t) (netsAt t) (wiresAt t) hu hq he hparams c largeText
    labelRoom publicRoom R reserve room weights (hidden t) (cells t) strideRoom low storage tables
    (SelfAdvice.suffix (p:=u) (k:=u) Hprog (FoldSuffixScale.extra Xprog seed fixed)) par oa na oc nc t C st
    pos ft (time.trans_le fs) wt (Nat.lt_of_lt_of_le time last) dur last begin space exponent ageConstant
    identifierCost projected valid invalid



end ThreeFlat.Diagonal.TickPhaseModel.Buckets

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open TickChronology TickRangeChronology TickEvaluationProduct HistoryContraction RAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type*} [CommSemiring F] {W p teams : ℕ} (a : RootArchive) (N : Nodes a) (c : Clock)

private theorem prod_rootList {α : Type*} (xs : List α) (cost : α→F) :
    (∏ i : Fin xs.length,cost (xs.get i))=(xs.map cost).prod := by
  calc
    _ = (List.ofFn (cost ∘ xs.get)).prod := (Fin.prod_ofFn _).symm
    _ = ((List.ofFn xs.get).map cost).prod := by rw [List.map_ofFn]
    _ = _ := by rw [List.ofFn_get]

/-- Each tick evaluates the team slots specified by its actual S1 slot words.
A slot with no selected roots contributes the multiplicative identity. -/
def slotWeight (teams group : ℕ) (cost : Fin a.rootCount→F) (t : ℕ) : F :=
  ∏ team : Fin teams, ((a.slotBlock N (c.evaluateTicks*teams) group
    (TickClockWords.values c 0 teams team.val t 3)).map cost).prod

local notation "slots" => c.evaluateTicks*teams
variable (h : ScheduleFacts a W (c.evaluateTicks*teams) N.work N.pairs a.ids) (gf : a.groups<2^W)

private abbrev groupFiber (a : RootArchive) (N : Nodes a) (total : ℕ)
    (facts : ScheduleFacts a W total N.work N.pairs a.ids) (fit : a.groups<2^W)
    (g : Fin a.groups) (s : Fin total) : Type :=
  {i : {j : Fin a.rootCount // a.groupOf N total facts fit j=g} // a.slotOf N total facts i.val=s}

private def slotEnumeration (a : RootArchive) (N : Nodes a) (total : ℕ)
    (h : ScheduleFacts a W total N.work N.pairs a.ids) (gf : a.groups<2^W)
    (g : Fin a.groups) (s : Fin total) :
    Fin (a.slotBlock N total g.val s.val).length ≃ groupFiber a N total h gf g s := by
  let xs:=a.slotBlock N total g.val s.val
  have eqn:=a.slotBlock_filter N total g.val s.val h
  have nodup : xs.Nodup := by
    dsimp only [xs]
    rw [←eqn]
    exact (List.nodup_finRange _).filter _
  have member (i : Fin a.rootCount) : i∈xs ↔ a.groupOf N total h gf i=g ∧ a.slotOf N total h i=s := by
    dsimp only [xs]
    rw [←eqn]
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
    constructor
    · intro atI
      exact ⟨Fin.ext ((a.groupOf_ordinal N total h gf i).trans (congrArg Prod.fst atI)),
        Fin.ext (congrArg Prod.snd atI)⟩
    · rintro ⟨h1,h2⟩
      exact Prod.ext ((a.groupOf_ordinal N total h gf i).symm.trans (congrArg Fin.val h1))
        (congrArg Fin.val h2)
  refine (List.Nodup.getEquiv xs nodup).trans ?_
  exact ⟨fun i=>⟨⟨i.val,((member i.val).mp i.property).1⟩,((member i.val).mp i.property).2⟩,
    fun j=>⟨j.val.val,(member j.val.val).mpr ⟨j.val.property,j.property⟩⟩,fun _=>rfl,fun _=>rfl⟩

/-- Across all evaluation times the native greedy slot decomposition visits
every site assigned to this group exactly once. -/
theorem slotWeight_group (groups : c.groups=a.groups) (g : Fin c.groups) (cost : Fin a.rootCount→F) :
    ((evalTicks c g.val).map (a.slotWeight N c teams g.val cost)).prod =
      ∏ i : {i : Fin a.rootCount // a.groupOf N slots h gf i=g.cast groups},cost i.val := by
  apply eval_product c g (fun i : {i : Fin a.rootCount // a.groupOf N slots h gf i=g.cast groups}=>a.slotOf N slots h i.val)
    (fun i=>cost i.val)
  intro j
  unfold slotWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [clock_slot]
  let s : Fin slots:=finProdFinEquiv (j,k)
  let e:=slotEnumeration a N slots h gf (g.cast groups) s
  rw [←prod_rootList]
  exact e.prod_comp (fun i=>cost i.val.val)

/-- Evaluate the *projected* compiled forests at the mounted pins. The only
local input calculation is the actual Boolean read at each relocated address. -/
theorem slotWeight_tick {S : Shape} {P : Plan F S} {Pins : Type*} {V : Form S Pins}
    (A : P.Assembly V) (trees : HistoryContraction.Forest F V) (hist : P.History)
    (site : Fin a.rootCount→(P.finish hist).Site) (globalPins : Pins) (boundary : (P.finish hist).Boundary)
    (g t : ℕ) (mounted : Fin teams→Fin p→Bool) :
    let result:=P.assemble hist A trees
    let ids:=fun k : Fin teams=>a.slotBlock N slots g (TickClockWords.values c 0 teams k.val t 3)
    let root:=fun k (i : Fin (ids k).length)=>site ((ids k).get i)
    let net:=fun k i=>(result.2 (root k i)).compile
    ∀ (wire : ∀ k (i : Fin (ids k).length), Fin (result.1.width (root k i))→Fin p),
    (∀ k i bit,mounted k (wire k i bit)=result.1.read (root k i) globalPins
      ((P.finish hist).graph.atVertex boundary (root k i)) bit) →
    (∏ k, (TickSlotForest.network (HistoryTerminalJoin.projected (net k) (wire k))).eval (mounted k)) =
      a.slotWeight N c teams g
        (fun i=>P.cells hist (V.values trees globalPins) (site i) ((P.finish hist).graph.atVertex boundary (site i))) t := by
  intro result ids root net wire reads
  unfold slotWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [HistoryTerminalJoin.eval,←prod_rootList]
  apply Finset.prod_congr rfl
  intro i _
  have input : mounted k ∘ wire k i=result.1.read (root k i) globalPins
      ((P.finish hist).graph.atVertex boundary (root k i)) := funext (reads k i)
  rw [input]
  exact congrFun (congrFun (P.assemble_values hist V A trees globalPins) (root k i))
    ((P.finish hist).graph.atVertex boundary (root k i))


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM LinearAlgebra.SpectralBooks.VNP RAM TickGreedyReplay PhysicalStage HistoryContraction TickChronology TickRangeChronology
open private ranked_iff atRank_actual groupWord_eq from OAI.ThreeFlat.Diagonal.NavigationRunBuckets
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {d l W : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (start pairs : A.Site→ℕ) (c : Clock) (teams : ℕ)
local notation "slots" => c.evaluateTicks*teams
local notation "work" => a.rankedWork r h C start
local notation "pay" => a.rankedPairs r h pairs

/-- This version depends only on the history. It can be used in every
local evaluation, before a successful native memory or path is chosen. -/
def runWeightAt (g : ℕ) (f : (r.plan.finish h).Site→F) (t : ℕ) : F :=
  let groups:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  let block:=(groups[g]?).getD []
  let slices:=(Team.handoff work (a.slotBudget/4) slots block).1
  let atRank (i : Fin a.rootCount):=∏ z : (r.plan.finish h).Site,
    if terminalRank r h z=i.val then f z else 1
  ∏ k : Fin teams, (((slices[TickClockWords.values c 0 teams k.val t 3]?).getD []).map atRank).prod

/-- Compute the array extent from the typed terminal state of this history. -/
def runWeight (g : ℕ) (f : (r.plan.finish h).Site→F) (t : ℕ) : F :=
  (a.typedRoot r h).runWeightAt r h C start pairs c teams g f t

variable (O : A.ArchiveSites) (path : r.ArchivePath h C O)
  (card : a.rootCount=(r.finalArchive h C O path).1.count)
  (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O path)
  (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O path).1.first)
  (num : r.FinalNumbered h C O path)
local notation "N" => nodesOfRun a r h C O path m rows zero first card start pairs
local notation "site" => runRootSite a r h C O path card

include num in
theorem runWeight_eq_slotWeight (g : ℕ) (f : (r.plan.finish h).Site→F) (t : ℕ) :
    a.runWeight r h C start pairs c teams g f t = a.slotWeight N c teams g (f ∘ site) t := by
  have wh : work=(N).work := funext fun i=>atRank_actual a r h C O path card num _ i
  have ph : pay=(N).pairs := funext fun i=>atRank_actual a r h C O path card num _ i
  have rank (i : Fin a.rootCount) : (∏ z : (r.plan.finish h).Site,
      if terminalRank r h z=i.val then f z else 1)=f (site i) := by
    simp_rw [ranked_iff a r h C O path card num]
    simp
  have rankFn : (fun i : Fin a.rootCount => ∏ z : (r.plan.finish h).Site,
      if terminalRank r h z=i.val then f z else 1)=f ∘ site := funext rank
  unfold runWeight
  rw [a.typedRoot_eq r h C O path card]
  unfold runWeightAt slotWeight slotBlock slotBlocks groupBlock groupBlocks
  rw [wh,ph,rankFn]

include num in
/-- This is the actual grouped-site product for the same Run buckets used
by the rotating paired-bit scan. It allows the factor to depend on both
external endpoint arrays and the decoded terminal boundary. -/
theorem runBuckets_weight_group
    (bits : r.plan.History→ℕ) (payload span : ℕ) (groupsPos : 0<c.groups)
    (leaf : Fin a.initialLanes→A.Site) (positive : 0<span) (capacity : c.chunks*payload≤a.initialLanes*span)
    (ng : a.groups=c.groups) (gf : a.groups<2^W) (schedule : ScheduleFacts a W slots (N).work (N).pairs a.ids)
    (g : Fin c.groups) (f : (r.plan.finish h).Site→F) :
    let T:=a.runBuckets r C start pairs W slots c bits payload span groupsPos leaf positive capacity
    ((evalTicks c g.val).map (a.runWeight r h C start pairs c teams g.val f)).prod =
      ∏ i : {i // T.group h i=g},f i.val := by
  intro T
  let e : Fin a.rootCount ≃ (r.plan.finish h).Site :=
    (finCongr card).trans (((r.finalArchive h C O path).2.symm).trans (r.finalSite h))
  have wh : work=(N).work := funext fun i=>atRank_actual a r h C O path card num _ i
  have ph : pay=(N).pairs := funext fun i=>atRank_actual a r h C O path card num _ i
  have role (i : Fin a.rootCount) :
      (T.group h (e i)).val=(a.groupOf N slots schedule gf i).val := by
    have k : terminalRank r h (e i)=i.val := (ranked_iff a r h C O path card num _ i).mpr rfl
    change (a.typedRoot r h).groupWord W slots ((a.typedRoot r h).rankedWork r h C start)
      ((a.typedRoot r h).rankedPairs r h pairs) (terminalRank r h (e i))%c.groups=_
    rw [a.typedRoot_eq r h C O path card]
    rw [wh,ph,k,groupWord_eq a N slots schedule gf i]
    exact Nat.mod_eq_of_lt ((a.groupOf N slots schedule gf i).isLt.trans_eq ng)
  let groupEquiv : {i : Fin a.rootCount // a.groupOf N slots schedule gf i=g.cast ng.symm} ≃
      {z : (r.plan.finish h).Site // T.group h z=g} :=
    e.subtypeEquiv (fun i=>by
      constructor
      · intro eqv;exact Fin.ext ((role i).trans (congrArg Fin.val eqv))
      · intro eqv;exact Fin.ext ((role i).symm.trans (congrArg Fin.val eqv)))
  have same := funext (a.runWeight_eq_slotWeight r h C start pairs c teams O path card m rows zero first num g.val f)
  rw [same,a.slotWeight_group N c schedule gf ng.symm g (f ∘ site)]
  exact groupEquiv.prod_comp (fun j=>f j.val)


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets
open TickChronology TickAuxiliary HistoryContraction RAM
open scoped Classical BigOperators
noncomputable section
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
local notation "q" => period*width
local notation "O" => AlignedChunks.order c hc

/-- Natural bit numbers of the two original catalyst halves agree with
the flattened group cursor, including at the first bit of the second half. -/
theorem physicalBit_address (i : Fin (q*a+q*a)) :
    ∃ (k : Fin c.chunks) (j : Fin a), ClippedPairBuckets.address (k,j)=i.val ∧
      ∀ x : Ext c a,PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O x) i=x k j := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) i
  · obtain ⟨⟨k,j⟩,rfl⟩:=finProdFinEquiv.surjective i
    refine ⟨(O).symm (false,k),j,?_,?_⟩
    · change (k.val+q*0)*a+j.val=j.val+a*k.val
      ring
    · intro x
      rw [PhysicalPinsInput.externalBits,Fin.append_left,TraceCircuit.blocks_at]
      rfl
  · obtain ⟨⟨k,j⟩,rfl⟩:=finProdFinEquiv.surjective i
    refine ⟨(O).symm (true,k),j,?_,?_⟩
    · change (k.val+q*1)*a+j.val=q*a+(j.val+a*k.val)
      ring
    · intro x
      rw [PhysicalPinsInput.externalBits,Fin.append_right,TraceCircuit.blocks_at]
      rfl

variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {bits : P.History→ℕ}
    {lanes span : ℕ} (T : Buckets P bits c a lanes span)

/-- Every endpoint bit of a contributing leaf is unchanged by the group's
canonical zero extension. Its lane is selected using the actual pair span. -/
theorem extend_externalBits (v : Plan.Terminal P bits) (g : Fin c.groups) (x : Ext c a)
    (i : Fin (q*a+q*a)) (lane : Fin lanes) (index : i.val/span=lane.val)
    (home : T.group v.1 (P.destination v.1 (T.site lane))=g) :
    PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O (T.extend v g (T.read v g x))) i =
      PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack O x) i := by
  obtain ⟨k,j,atI,point⟩:=physicalBit_address c hc i
  rw [point,point]
  apply T.extend_read
  have atLane : ClippedPairBuckets.lane span T.positive T.fit (k,j)=lane := Fin.ext (by
    change ClippedPairBuckets.address (k,j)/span=lane.val
    rw [atI,index])
  change T.group v.1 (P.destination v.1 (T.site (ClippedPairBuckets.lane _ _ _ (k,j))))=g
  rw [atLane,home]

end
end ThreeFlat.Diagonal.TickPhaseModel.Buckets

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM PhysicalStage HistoryContraction TickChronology TickRangeChronology TickPhaseModel TickAuxiliary
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d l W lanes span payload : ℕ} {A : State d l}
  (a : RootArchive) (r : Run F A) (C : r.Charges) (start pairs : A.Site→ℕ) (c : Clock) (teams : ℕ)
  {bits : r.plan.History→ℕ} (T : Buckets r.plan bits c payload lanes span)
  (factor : ∀ v : Plan.Terminal r.plan bits,Ext c payload→Ext c payload→(r.plan.finish v.1).Site→F)

/-- The local scalar is defined for any packed proposal, before either
complete outside endpoint is given. Only a genuine group contributes. -/
def packedWeight (v : Plan.Terminal r.plan bits) (g : ℕ) (op np : Aux (T.length v g)) (t : ℕ) : F :=
  if hg : g<c.groups then
    a.runWeight r v.1 C start pairs c teams g (factor v (T.extend v ⟨g,hg⟩ op) (T.extend v ⟨g,hg⟩ np)) t
  else 1

variable (v : Plan.Terminal r.plan bits) (O : A.ArchiveSites) (path : r.ArchivePath v.1 C O)
  (card : a.rootCount=(r.finalArchive v.1 C O path).1.count)
  (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) v.1 C O path)
  (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive v.1 C O path).1.first)
  (num : r.FinalNumbered v.1 C O path)
local notation "N" => nodesOfRun a r v.1 C O path m rows zero first card start pairs
local notation "slots" => c.evaluateTicks*teams

include num in
theorem packedWeight_group (groupsPos : 0<c.groups) (leaf : Fin a.initialLanes→A.Site) (positive : 0<span)
    (capacity : c.chunks*payload≤a.initialLanes*span) (ng : a.groups=c.groups)
    (gf : a.groups<2^W) (schedule : ScheduleFacts a W slots (N).work (N).pairs a.ids)
    (g : Fin c.groups) (x y : Ext c payload) :
    let B:=a.runBuckets r C start pairs W slots c bits payload span groupsPos leaf positive capacity
    (∀ j : {j // B.group v.1 j=g},
      factor v (B.extend v g (B.read v g x)) (B.extend v g (B.read v g y)) j.val=factor v x y j.val) →
    ((evalTicks c g.val).map (a.packedWeight r C start pairs c teams B factor v g.val (B.read v g x) (B.read v g y))).prod =
      ∏ j : {j // B.group v.1 j=g},factor v x y j.val := by
  intro B supported
  let localFactor := factor v (B.extend v g (B.read v g x)) (B.extend v g (B.read v g y))
  have weight : a.packedWeight r C start pairs c teams B factor v g.val (B.read v g x) (B.read v g y) =
      a.runWeight r v.1 C start pairs c teams g.val localFactor := by
    funext t
    simp only [packedWeight,dite_eq_left g.isLt,localFactor]
  rw [weight,a.runBuckets_weight_group r v.1 C start pairs c teams O path card m rows zero first num bits payload span
    groupsPos leaf positive capacity ng gf schedule g localFactor]
  exact Finset.prod_congr rfl (fun j _=>supported j)

end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM HistoryContraction LaneCursor TraceSuffix RAM TickPhaseModel TickChronology
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F] {w p r n S base f q low : ℕ}
    (M : Machine w p r n) (t : NativeTrace.Fits M S base ((q+1)+low) f) (hF : Fintype.card F≤2^w)
    (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
variable {period width a : ℕ} (c : Clock) (hc : c.chunks=2*(period*width))
variable (extent : 2*(period*width*a+period*width*a)≤S)
local notation "U" => (seedWordLayout M t hF st B hk extent).ports
variable (P : Plan F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r n ((q+1)+low)).cells).shape)
  {bits : P.History→ℕ} (T : Buckets P bits c a (2^(q+1)) (2^low))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 10000 in
/-- For the original paired-endpoint forest, replacing both outside
groups by zeros preserves every terminal factor in the chosen group. -/
theorem seedForest_extension (leaves : ∀ lane : Lane (q+1), T.site (finFunctionFinEquiv lane)=(0,lane))
    (assembly : P.Assembly (U).form) (N : Forest F (U).form) (v : Plan.Terminal P bits) (g : Fin c.groups)
    (x y : Ext c a) (root : {j // T.group v.1 j=g}) :
    let D:=P.assemble v.1 assembly N
    let readBits : TickPhaseModel.Ext c a → Fin (period*width*a+period*width*a) → Bool :=
      fun e => PhysicalPinsInput.externalBits (TickPhysicalOrder.unpack (AlignedChunks.order c hc) e)
    let pin:=fun (lhs rhs : TickPhaseModel.Ext c a)=>endpointPin (readBits lhs) (readBits rhs)
    D.1.values D.2 (pin (T.extend v g (T.read v g x)) (T.extend v g (T.read v g y))) root.val=
      D.1.values D.2 (pin x y) root.val := by
  intro D readBits pin
  refine seedForest_local M t hF st B hk extent P v.1 root.val assembly N
    (readBits (T.extend v g (T.read v g x))) (readBits (T.extend v g (T.read v g y)))
    (readBits x) (readBits y) ?_
  intro lane dest j address
  have inGroup : T.group v.1 (P.destination v.1 (T.site (finFunctionFinEquiv lane)))=g := by
    have reaches : P.destination v.1 (T.site (finFunctionFinEquiv lane)) = root.val :=
      (congrArg (P.destination v.1) (leaves lane)).trans dest
    exact (congrArg (T.group v.1) reaches).trans root.property
  exact ⟨T.extend_externalBits c hc v g x j (finFunctionFinEquiv lane) address inGroup,
    T.extend_externalBits c hc v g y j (finFunctionFinEquiv lane) address inGroup⟩

end
end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM LinearAlgebra.SpectralBooks.VNP RAM TickGreedyReplay PhysicalStage HistoryContraction TickChronology
open private ranked_iff atRank_actual from OAI.ThreeFlat.Diagonal.NavigationRunBuckets
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {d l W p : ℕ} {A : State d l} (a : RootArchive) (r : Run F A)
    (h : r.plan.History) (C : r.Charges) (start pairs : A.Site→ℕ) (c : Clock) (teams : ℕ)
local notation "slots" => c.evaluateTicks*teams
local notation "work" => a.rankedWork r h C start
local notation "pay" => a.rankedPairs r h pairs

/-- The typed root list uses the actual terminal numbering, before a
concrete archive memory or a proof of successful navigation is supplied. -/
def rankSite? (i : ℕ) : Option (r.plan.finish h).Site :=
  if e : ∃ v, terminalRank r h v=i then some e.choose else none

def teamRootsAt (g s : ℕ) : List (r.plan.finish h).Site :=
  let gs:=schedule a.groups (Team.ticks work a.ids) a.totalPairs work pay a.ids
  let ss:=(Team.handoff work (a.slotBudget/4) slots ((gs[g]?).getD [])).1
  ((ss[s]?).getD []).filterMap (fun i=>rankSite? r h i.val)

def teamRoots (g s : ℕ) : List (r.plan.finish h).Site :=
  (a.typedRoot r h).teamRootsAt r h C start pairs c teams g s

variable (O : A.ArchiveSites) (path : r.ArchivePath h C O)
  (card : a.rootCount=(r.finalArchive h C O path).1.count)
  (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O path)
  (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O path).1.first)
  (num : r.FinalNumbered h C O path)
local notation "N" => nodesOfRun a r h C O path m rows zero first card start pairs
local notation "site" => runRootSite a r h C O path card

include num in
theorem rankSite?_of_numbered (i : Fin a.rootCount) : rankSite? r h i.val=some (site i) := by
  have e : ∃ v, terminalRank r h v=i.val := ⟨site i,(ranked_iff a r h C O path card num _ i).mpr rfl⟩
  rw [rankSite?,dite_eq_left e]
  exact congrArg some ((ranked_iff a r h C O path card num e.choose i).mp e.choose_spec)

include num in
theorem teamRoots_block (g s : ℕ) :
    a.teamRoots r h C start pairs c teams g s=(a.slotBlock N slots g s).map site := by
  have wh : work=(N).work := funext fun i=>atRank_actual a r h C O path card num _ i
  have ph : pay=(N).pairs := funext fun i=>atRank_actual a r h C O path card num _ i
  unfold teamRoots
  rw [a.typedRoot_eq r h C O path card]
  unfold teamRootsAt slotBlock slotBlocks groupBlock groupBlocks
  rw [wh,ph]
  exact List.filterMap_eq_map_iff_forall_eq_some.mpr (fun i _=>rankSite?_of_numbered a r h C O path card num i)

include num in
/-- Transfer the native S17 root array to typed terminal trees in exactly
the order seen by the installed preparation program. -/
theorem teamRoots_numbers (hs : ScheduleFacts a W slots (N).work (N).pairs a.ids)
    (gf : a.groups≤2^W) (sf : slots≤2^W) (g : Fin a.groups) (s : Fin slots)
    (prepared : Memory W) (cg : prepared (TickWorkspace.base a.age 1)=(g.val:Word W))
    (cs : prepared (TickWorkspace.base a.age 1+3)=(s.val:Word W)) :
    (a.teamRoots r h C start pairs c teams g.val s.val).map (terminalRank r h)=
      TickTerminalRoot.rootIds a.age (a.summaryHeader N) (a.scheduledOwner N slots) prepared := by
  rw [a.teamRoots_block r h C start pairs c teams O path card m rows zero first num,
    a.selected_block N slots hs gf sf g s prepared cg cs,List.map_map]
  exact List.map_congr_left (fun i _ => (ranked_iff a r h C O path card num _ i).mpr rfl)

include num in
/-- Adding the directory first-final word to a real selected root number yields
the exact address indexed by the chronological typed-tree and origin ledger. -/
theorem teamRoots_archiveIds (hs : ScheduleFacts a W slots (N).work (N).pairs a.ids)
    (gf : a.groups≤2^W) (sf : slots≤2^W) (g : Fin a.groups) (s : Fin slots)
    (prepared : Memory W) (cg : prepared (TickWorkspace.base a.age 1)=(g.val:Word W))
    (cs : prepared (TickWorkspace.base a.age 1+3)=(s.val:Word W)) :
    (a.teamRoots r h C start pairs c teams g.val s.val).map (fun v=>(r.archivePlanIndex h C O path v).val)=
      (TickTerminalRoot.rootIds a.age (a.summaryHeader N) (a.scheduledOwner N slots) prepared).map (a.firstFinal+·) := by
  rw [←a.teamRoots_numbers r h C start pairs c teams O path card m rows zero first num hs gf sf g s prepared cg cs,List.map_map]
  apply List.map_congr_left
  intro v _
  change (r.finalArchive h C O path).1.first+((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val =
    a.firstFinal+terminalRank r h v
  have number : ((r.finalArchive h C O path).2 ((r.finalSite h).symm v)).val = terminalRank r h v :=
    num ((r.finalSite h).symm v)
  exact congrArg₂ Nat.add first.symm number

include O path card m rows zero first num in
/-- The complete team scalar for the real typed root arrays equals the
history-only weight. The physical premise is a bit read for each selected
wire of each mounted root, and is independent of its field evaluation. -/
theorem teamRoots_tick {Pins : Type*} {V : Form A.shape Pins} (asm : r.plan.Assembly V)
    (trees : HistoryContraction.Forest F V) (globalPins : Pins) (boundary : (r.plan.finish h).Boundary)
    (g t : ℕ) (mounted : Fin teams→Fin p→Bool) :
    let D:=r.plan.assemble h asm trees
    let roots:=fun k : Fin teams=>a.teamRoots r h C start pairs c teams g (TickClockWords.values c 0 teams k.val t 3)
    let net:=fun k (i : Fin (roots k).length)=>(D.2 ((roots k).get i)).compile
    ∀ wire : ∀ k (i : Fin (roots k).length),Fin (D.1.width ((roots k).get i))→Fin p,
    (∀ k i bit,mounted k (wire k i bit)=D.1.read ((roots k).get i) globalPins
      ((r.plan.finish h).graph.atVertex boundary ((roots k).get i)) bit) →
    (∏ k, (TickSlotForest.network (HistoryTerminalJoin.projected (net k) (wire k))).eval (mounted k)) =
      a.runWeight r h C start pairs c teams g
        (fun z=>D.1.values D.2 globalPins z ((r.plan.finish h).graph.atVertex boundary z)) t := by
  intro D roots net wire reads
  let f:=fun z=>D.1.values D.2 globalPins z ((r.plan.finish h).graph.atVertex boundary z)
  rw [a.runWeight_eq_slotWeight r h C start pairs c teams O path card m rows zero first num]
  unfold slotWeight
  apply Finset.prod_congr rfl
  intro k _
  rw [HistoryTerminalJoin.eval]
  calc
    _ = ∏ i : Fin (roots k).length,f ((roots k).get i) := by
      apply Finset.prod_congr rfl
      intro i _
      have atI : mounted k ∘ wire k i=D.1.read ((roots k).get i) globalPins
        ((r.plan.finish h).graph.atVertex boundary ((roots k).get i)) := funext (reads k i)
      rw [atI]
      rfl
    _ = ((roots k).map f).prod := prod_rootList _ f
    _ = _ := by
      dsimp only [roots]
      rw [a.teamRoots_block r h C start pairs c teams O path card m rows zero first num,List.map_map]


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM LinearAlgebra.SpectralBooks.VNP PhysicalStage HistoryContraction TickChronology TickRangeChronology TickPhaseModel TickAuxiliary
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d l W span payload : ℕ} {A : State d l}
    (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges) (start pairs : A.Site→ℕ)
    (c : Clock) (teams : ℕ) (bits : r.plan.History→ℕ)
    (groupsPos : 0<c.groups) (leaf : Fin a.initialLanes→A.Site) (positive : 0<span)
    (capacity : c.chunks*payload≤a.initialLanes*span)
local notation "T" => a.runBuckets r C start pairs W (c.evaluateTicks*teams) c bits payload span
  groupsPos leaf positive capacity
local notation "b" => a.typedRoot r h
local notation "slots" => c.evaluateTicks*teams
local notation "work" => rankedWork (typedRoot a r h) r h C start
local notation "pay" => rankedPairs (typedRoot a r h) r h pairs

/-- The ordered native slot products of a typed history exhaust precisely the
terminal cells assigned to the group, before any memory image is chosen. -/
theorem runBuckets_intrinsic_group (ng : a.groups=c.groups) (wg : a.groups<2^W)
    (facts : ScheduleFacts b W slots work pay (b).ids) (g : Fin c.groups) (f : (r.plan.finish h).Site→F) :
    ((evalTicks c g.val).map (a.runWeight r h C start pairs c teams g.val f)).prod =
      ∏ j : {j // (T).group h j=g},f j.val := by
  let e : Fin (b).rootCount ≃ (r.plan.finish h).Site := (r.terminalOrderEquiv h).symm
  let label (i : Fin (b).rootCount):=(b).groupWord W slots work pay i.val
  have ord (i : Fin (b).rootCount) : terminalRank r h (e i)=i.val :=
    (r.terminalOrderEquiv_val h (e i)).symm.trans (congrArg Fin.val ((r.terminalOrderEquiv h).apply_symm_apply i))
  have rank (i : Fin (b).rootCount) : (∏ z : (r.plan.finish h).Site,if terminalRank r h z=i.val then f z else 1)=f (e i) := by
    have hit (z : (r.plan.finish h).Site) : terminalRank r h z=i.val ↔ z=e i := by
      rw [show terminalRank r h z=((r.terminalOrderEquiv h) z).val from (r.terminalOrderEquiv_val h z).symm]
      exact Fin.ext_iff.symm.trans (r.terminalOrderEquiv h).eq_symm_apply.symm
    simp_rw [hit];simp
  have byTime : a.runWeight r h C start pairs c teams g.val f=(b).arrayWeight work pay c teams g.val (f ∘ e) := by
    funext t
    simp only [runWeight,runWeightAt,arrayWeight,rank,Function.comp_def]
  have bound := groupWord_bounds b slots work pay facts wg
  have role (i : Fin (b).rootCount) : ((T).group h (e i)).val=label i := by
    change (b).groupWord W slots work pay (terminalRank r h (e i))%c.groups=_
    rw [ord];exact Nat.mod_eq_of_lt ((bound.1 i).trans_eq ng)
  let subset : {i : Fin (b).rootCount // label i=g.val} ≃ {z // (T).group h z=g} :=
    e.subtypeEquiv (fun i=>⟨fun yes=>Fin.ext ((role i).trans yes),fun yes=>(role i).symm.trans (congrArg Fin.val yes)⟩)
  rw [byTime,(b).arrayWeight_group work pay c teams facts wg g (f ∘ e)]
  exact subset.prod_comp (fun j=>f j.val)

/-- Every grouped phase satisfies its product identity for every typed record,
using only its ranked work/pair bounds and the local endpoint extension law. -/
theorem packedWeight_intrinsic_group
    (factor : ∀ v : Plan.Terminal r.plan bits,Ext c payload→Ext c payload→(r.plan.finish v.1).Site→F)
    (v : Plan.Terminal r.plan bits) (ng : a.groups=c.groups) (wg : a.groups<2^W)
    (facts : ScheduleFacts (a.typedRoot r v.1) W slots ((a.typedRoot r v.1).rankedWork r v.1 C start)
      ((a.typedRoot r v.1).rankedPairs r v.1 pairs) (a.typedRoot r v.1).ids)
    (g : Fin c.groups) (x y : Ext c payload)
    (supported : ∀ j : {j // (T).group v.1 j=g},
      factor v ((T).extend v g ((T).read v g x)) ((T).extend v g ((T).read v g y)) j.val=factor v x y j.val) :
    ((evalTicks c g.val).map (a.packedWeight r C start pairs c teams T factor v g.val ((T).read v g x) ((T).read v g y))).prod =
      ∏ j : {j // (T).group v.1 j=g},factor v x y j.val := by
  let localFactor := factor v ((T).extend v g ((T).read v g x)) ((T).extend v g ((T).read v g y))
  have weight : a.packedWeight r C start pairs c teams T factor v g.val ((T).read v g x) ((T).read v g y) =
      a.runWeight r v.1 C start pairs c teams g.val localFactor := by
    funext t
    simp only [packedWeight, dite_eq_left g.isLt, localFactor]
  rw [weight, a.runBuckets_intrinsic_group r v.1 C start pairs c teams bits groupsPos leaf positive capacity ng wg facts]
  exact Finset.prod_congr rfl (fun j _=>supported j)


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM LinearAlgebra.SpectralBooks.VNP RAM TickGreedyReplay PhysicalStage HistoryContraction TickChronology
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d l p : ℕ} {A : State d l} (a : RootArchive) (r : Run F A)
    (h : r.plan.History) (C : r.Charges) (start pairs : A.Site→ℕ) (c : Clock) (teams : ℕ)
local notation "b" => a.typedRoot r h
local notation "E" => r.terminalOrderEquiv h
local notation "work" => rankedWork (typedRoot a r h) r h C start
local notation "pay" => rankedPairs (typedRoot a r h) r h pairs

theorem rankSite?_intrinsic (i : Fin (Fintype.card (r.plan.finish h).Site)) :
    rankSite? r h i.val=some ((E).symm i) := by
  have hit (z : (r.plan.finish h).Site) : terminalRank r h z=i.val ↔ z=(E).symm i := by
    rw [show terminalRank r h z=(E z).val from (r.terminalOrderEquiv_val h z).symm]
    exact Fin.ext_iff.symm.trans (E).eq_symm_apply.symm
  have existsRank : ∃ z,terminalRank r h z=i.val:=⟨(E).symm i,(hit _).mpr rfl⟩
  rw [rankSite?,dite_eq_left existsRank,(hit _).mp existsRank.choose_spec]

/-- The native slice's ordered list and the semantic history trees have the same
physical ranks, even before a clock tick presents a decoded journal. -/
def intrinsicTeamIds (g s : ℕ) : List (Fin (b).rootCount) :=
  let gs:=schedule (b).groups (Team.ticks work (b).ids) (b).totalPairs work pay (b).ids
  let ss:=(Team.handoff work ((b).slotBudget/4) (c.evaluateTicks*teams) ((gs[g]?).getD [])).1
  (ss[s]?).getD []

theorem teamRoots_intrinsic (g s : ℕ) : a.teamRoots r h C start pairs c teams g s=
    (a.intrinsicTeamIds r h C start pairs c teams g s).map (E).symm := by
  unfold teamRoots teamRootsAt intrinsicTeamIds
  exact List.filterMap_eq_map_iff_forall_eq_some.mpr (fun i _=>rankSite?_intrinsic r h i)

private theorem map_root_values {α β γ : Type*} (xs : List α) (site : α → β)
    (f : β → γ) (ranked : α → γ) (value : ∀ i, f (site i) = ranked i) :
    (xs.map site).map f = xs.map ranked :=
  List.map_map.trans (congrArg (fun g => xs.map g) (funext value))

/-- The exact team root array at every history and every slot fits its share of
the native work budget, including every site passed to terminal compilation. -/
theorem teamRoots_budget (g s : ℕ) :
    Team.ticks (fun v=>a.nodeBank.unitWork*r.chargeAt h C start v) (a.teamRoots r h C start pairs c teams g s)
      ≤a.slotBudget/4 := by
  rw [teamRoots_intrinsic]
  let ids:=a.intrinsicTeamIds r h C start pairs c teams g s
  have item (i : Fin (b).rootCount) : work i=a.nodeBank.unitWork*r.chargeAt h C start ((E).symm i) :=
    intrinsicAt a r h (fun v => a.nodeBank.unitWork*r.chargeAt h C start v) i
  let site : Fin (b).rootCount → (r.plan.finish h).Site := (E).symm
  have charges := map_root_values ids site (fun v => a.nodeBank.unitWork*r.chargeAt h C start v)
    work (fun i => (item i).symm)
  exact (congrArg (fun xs : List ℕ => xs.sum) charges).le.trans (arrayBlock_budget b work pay c teams g s)

/-- Each root of the chosen true slot belongs to that slot's clock group,
for every typed history that satisfies the intrinsic scheduler bounds. -/
theorem teamRoots_group {W payload span : ℕ} (bits : r.plan.History→ℕ)
    (groupsPos : 0<c.groups) (leaf : Fin a.initialLanes→A.Site) (positive : 0<span)
    (capacity : c.chunks*payload≤a.initialLanes*span) (wg : a.groups<2^W)
    (facts : ScheduleFacts b W (c.evaluateTicks*teams) work pay (b).ids)
    (g : Fin c.groups) (s : ℕ) (root : (r.plan.finish h).Site)
    (mem : root∈a.teamRoots r h C start pairs c teams g.val s) :
    (a.runBuckets r C start pairs W (c.evaluateTicks*teams) c bits payload span
        groupsPos leaf positive capacity).group h root=g := by
  rw [a.teamRoots_intrinsic r h C start pairs c teams] at mem
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp mem
  have word:=(b).arrayBlock_group work pay (c.evaluateTicks*teams) g.val s facts wg i hi
  have ord : terminalRank r h ((E).symm i)=i.val := (r.terminalOrderEquiv_val h ((E).symm i)).symm.trans
    (congrArg Fin.val ((E).apply_symm_apply i))
  apply Fin.ext
  change (b).groupWord W (c.evaluateTicks*teams) work pay (terminalRank r h ((E).symm i))%c.groups=g.val
  rw [ord,show (b).groupWord W (c.evaluateTicks*teams) work pay i.val=g.val from word,Nat.mod_eq_of_lt g.isLt]

/-- A mounted team computation evaluates the history's planned local weight
for every per-pin assignment satisfying the actual assembled forest read. -/
theorem teamRoots_intrinsic_tick {Pins : Type*} {V : Form A.shape Pins} (asm : r.plan.Assembly V)
    (trees : HistoryContraction.Forest F V) (globalPins : Pins) (boundary : (r.plan.finish h).Boundary)
    (g t : ℕ) (mounted : Fin teams→Fin p→Bool) :
    let D:=r.plan.assemble h asm trees
    let roots:=fun k : Fin teams=>a.teamRoots r h C start pairs c teams g (TickClockWords.values c 0 teams k.val t 3)
    let net:=fun k (i : Fin (roots k).length)=>(D.2 ((roots k).get i)).compile
    ∀ wire : ∀ k (i : Fin (roots k).length),Fin (D.1.width ((roots k).get i))→Fin p,
    (∀ k i bit,mounted k (wire k i bit)=D.1.read ((roots k).get i) globalPins
      ((r.plan.finish h).graph.atVertex boundary ((roots k).get i)) bit) →
    (∏ k,(TickSlotForest.network (HistoryTerminalJoin.projected (net k) (wire k))).eval (mounted k)) =
      a.runWeight r h C start pairs c teams g
        (fun z=>D.1.values D.2 globalPins z ((r.plan.finish h).graph.atVertex boundary z)) t := by
  intro D roots net wire reads
  let f:=fun z=>D.1.values D.2 globalPins z ((r.plan.finish h).graph.atVertex boundary z)
  let ranked (i : Fin (b).rootCount):=∏ z : (r.plan.finish h).Site,if terminalRank r h z=i.val then f z else 1
  have value (i : Fin (b).rootCount) : ranked i=f ((E).symm i) := by
    have hit (z : (r.plan.finish h).Site) : terminalRank r h z=i.val ↔ z=(E).symm i := by
      rw [show terminalRank r h z=(E z).val from (r.terminalOrderEquiv_val h z).symm]
      exact Fin.ext_iff.symm.trans (E).eq_symm_apply.symm
    dsimp only [ranked];simp_rw [hit];simp
  unfold runWeight runWeightAt
  apply Finset.prod_congr rfl
  intro k _
  rw [HistoryTerminalJoin.eval]
  calc
    _ = ∏ i : Fin (roots k).length,f ((roots k).get i) := by
      apply Finset.prod_congr rfl
      intro i _
      have atI : mounted k ∘ wire k i=D.1.read ((roots k).get i) globalPins
        ((r.plan.finish h).graph.atVertex boundary ((roots k).get i)) := funext (reads k i)
      rw [atI];rfl
    _ = ((roots k).map f).prod := prod_rootList _ f
    _ = _ := by
      let s:=TickClockWords.values c 0 teams k.val t 3
      change ((a.teamRoots r h C start pairs c teams g s).map f).prod=
        ((a.intrinsicTeamIds r h C start pairs c teams g s).map ranked).prod
      rw [teamRoots_intrinsic]
      let site : Fin (b).rootCount → (r.plan.finish h).Site := (E).symm
      exact congrArg (fun xs : List F => xs.prod)
        (map_root_values (a.intrinsicTeamIds r h C start pairs c teams g s) site f ranked
          (fun i => (value i).symm))


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

end
end OAI
