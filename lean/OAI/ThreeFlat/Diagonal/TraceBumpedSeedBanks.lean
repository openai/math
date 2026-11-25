import OAI.ThreeFlat.Diagonal.FoldPhysicalClock
import OAI.ThreeFlat.Diagonal.TraceSelectedArenas
import OAI.ThreeFlat.Diagonal.TraceMountedTemplate
import OAI.ThreeFlat.RAM.TracePrototypeBoot
import OAI.ThreeFlat.RAM.HistorySelectedFamily
import OAI.ThreeFlat.RAM.TraceMountedParameters
import OAI.ThreeFlat.RAM.TickLedgerTerminal
import OAI.ThreeFlat.RAM.TraceSuffixAperture

namespace OAI
/-! # The H suffix read from physical pins at an advanced S12 seed -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM PhysicalPrelude ApproximateImage TickWorkspace HistoryStageBody.Physical
open HistoryNodeDirectory HistoryNodeDirectory.Selected HistoryInitialSeed
open scoped Fin.CommRing
noncomputable section

variable {F : Type} [Fintype F] [Field F] {u w n W nt ns aux : ℕ}

theorem bumped_public_span {advice nt ns params aux hidden : ℕ}
    (room : BitLayout.cellsBase (ApproximateImage.pinCount advice nt ns params aux) hidden ≤ stride u) :
    2+advice+nt+ns+params ≤ stride u := by
  dsimp only [BitLayout.cellsBase,BitLayout.hiddenBase,ApproximateImage.pinCount] at room
  omega

omit [Fintype F] [Field F] in
/-- The selected walk changes its cursor at S18 before entering the local body.
Every true public input survives both the cursor write and the preceding ledger. -/
theorem bumped_seed_low {dir : Directory W n} {label : ((Fin 3→Bool)→F)→ℕ} {val : Fin n→NodeValue F}
    {warm before : Memory W} {i : ℕ}
    (live : Ledger u dir label val (TickTerminalRoot.slotKeep u) warm i before)
    (word : base u 18<2^W) (prepared : Memory W)
    (startup : ∀ j,j<base u 53→warm j=prepared j) {j : ℕ} (low : j<base u 12) :
    bump (ownerData W u) before j=prepared j := by
  have s:=apart (u:=u) (by decide : 12<18)
  have t:=apart (u:=u) (by decide : 12<53)
  exact (bumped_outside u before word (by omega)).trans ((live.durable j (Or.inl low)).trans (startup j (by omega)))

/-- Read the description, H parameter bits and compact coefficient-table bits
at their original addresses after the actual S18 cursor increment. -/
theorem bumped_suffix (im : Image F w) (desc : Fin im.advice→Bool)
    (team : Fin nt→Bool) (step : Fin ns→Bool) (initialBits : Fin im.parameters→Bool)
    (oa na oc nc : Fin aux→Bool) (off len code textStart textLength : ℕ) (wordAt : ℕ→Word W)
    (par : Fin im.parameters→Bool) (isPar : TraceMountedParameters.parameters im off len wordAt initialBits=par)
    (wordPositive : 0<W) (fits : off+W*len+w*FixedTraceImage.count im.G≤ im.parameters)
    (size : 2+im.advice+nt+ns+im.parameters ≤ stride u)
    (prepared warm before : Memory W) {dir : Directory W n} {label : ((Fin 3→Bool)→F)→ℕ} {val : Fin n→NodeValue F}
    {i : ℕ} (live : Ledger u dir label val (TickTerminalRoot.slotKeep u) warm i before)
    (ctrl : base u 18<2^W) (startup : ∀ j,j<base u 53→warm j=prepared j)
    (pins : ∀j,j<stride u→prepared j=TickMountedPins.memory (fields desc team step par oa na oc nc) j) :
    let src:=bump (ownerData W u) before
    let pb:=2+im.advice+nt+ns
    let loc : TraceSuffixOracle.Locations:=⟨2,pb,pb+(off+W*len),code,textStart,textLength⟩
    TraceSuffixOracle.Mounted im loc (fun j=>(src j).val) desc par ∧ (src 0).val=0 ∧ (src 1).val=1 := by
  subst par
  let par:=TraceMountedParameters.parameters im off len wordAt initialBits
  let bus:=fields desc team step par oa na oc nc
  let src:=bump (ownerData W u) before
  have low12:=lower u 12
  have mem (j : ℕ) (hj : j<stride u) : src j=TickMountedPins.memory (w:=W) bus j :=
    (bumped_seed_low live ctrl prepared startup (hj.trans_le low12)).trans (pins j hj)
  have H:=(TraceMountedParameters.physical im desc team step initialBits oa na oc nc off len code
    textStart textLength wordAt wordPositive fits).1
  have literals:=TickMountedPins.memory_constants (w:=W) bus
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro j
    exact (congrArg Fin.val (mem (2+j.val) (by have:=j.isLt;omega))).trans (H.description j)
  · intro j
    exact (congrArg Fin.val (mem (2+im.advice+nt+ns+j.val) (by have:=j.isLt;omega))).trans (H.parameters j)
  · intro j
    exact (congrArg Fin.val (mem (2+im.advice+nt+ns+(off+W*len)+j.val) (by have:=j.isLt;omega))).trans (H.table j)
  · exact congrArg Fin.val ((mem 0 (by omega)).trans literals.1)
  · have one : (1:ℕ)<2^W:=Nat.one_lt_two_pow wordPositive.ne'
    calc
      (src 1).val=((1:Word W)).val:=congrArg Fin.val ((mem 1 (by omega)).trans literals.2)
      _=1:=Fin.val_cast_of_lt one

/-- The table operand in the installed virtual reader starts directly after the
navigation, local template and sparse seed records in the original H parameter stream. -/
theorem bumped_cursor_suffix {q : ℕ} (im : Image F W) (D : Fin im.advice→Bool)
    (team : Fin nt→Bool) (step : Fin ns→Bool) (oa na oc nc : Fin aux→Bool)
    (nav : List ℕ) (G : BitNetwork F q) (codec : FieldCode F W) (keys : Fin q→TraceAddressRecord.Record)
    (es : List (EffectStream.Record W)) (tmp seedPins shared code tp tk hp hk : ℕ) (par : Fin im.parameters→Bool)
    (mounted :
      let ws:=nav++NavigationPass.templateWords G codec keys
      TraceMountedParameters.parameters im 0 (ws.length+2*es.length)
        (TraceMountedParameters.seedWords ws.length tmp (fun j=>(ws[j]?.getD 0 : Word W)) es) (fun _=>false)=par)
    (fit :
      let ws:=nav++NavigationPass.templateWords G codec keys
      W*(ws.length+2*es.length)+W*FixedTraceImage.count im.G≤ im.parameters)
    (size : 2+im.advice+nt+ns+im.parameters ≤ stride u) (wordPositive : 0<W)
    (prepared warm before : Memory W) {dir : Directory W n} {label : ((Fin 3→Bool)→F)→ℕ} {val : Fin n→NodeValue F}
    {i : ℕ} (live : Ledger u dir label val (TickTerminalRoot.slotKeep u) warm i before)
    (ctrl : base u 18<2^W) (startup : ∀ j,j<base u 53→warm j=prepared j)
    (pins : ∀j,j<stride u→prepared j=TickMountedPins.memory (fields D team step par oa na oc nc) j) :
    let pb:=2+im.advice+nt+ns
    let boot:=TracePrototypeBoot.cursor u pb nav.length seedPins shared es.length G codec
    let tb:=boot.seedSource+W*(2*es.length)
    let src:=bump (ownerData W u) before
    TraceSuffixOracle.Mounted im (TraceSuffixOracle.locations W tp tk hp hk 2 pb tb code)
        (fun j=>(src j).val) D par ∧ (src 0).val=0 ∧ (src 1).val=1 := by
  let ws:=nav++NavigationPass.templateWords G codec keys
  let pb:=2+im.advice+nt+ns
  let boot:=TracePrototypeBoot.cursor u pb nav.length seedPins shared es.length G codec
  let wordAt:=TraceMountedParameters.seedWords ws.length tmp (fun j=>(ws[j]?.getD 0 : Word W)) es
  have table : boot.seedSource+W*(2*es.length)=pb+(0+W*(ws.length+2*es.length)) := by
    simp only [boot,TracePrototypeBoot.Args.seedSource,TracePrototypeBoot.cursor,ws,List.length_append,
      NavigationPass.templateWords_length,Nat.zero_add,Nat.mul_add,Nat.add_assoc]
  change TraceSuffixOracle.Mounted im (TraceSuffixOracle.locations W tp tk hp hk 2 pb
    (boot.seedSource+W*(2*es.length)) code) _ D par ∧ _
  rw [table]
  exact bumped_suffix im D team step (fun _=>false) oa na oc nc 0 (ws.length+2*es.length) code
    (SelfAdvice.textSize W tp tk) (SelfAdvice.textSize W hp hk) wordAt par mounted wordPositive (by simpa only [ws, Nat.zero_add] using fit)
    size prepared warm before live ctrl startup pins

/-- Exactly the three sections of the low parameter vector and the three
sparse S54–56 banks used by the virtual seed reader are protected. -/
theorem bumped_seed_regions (im : Image F w) (B : TraceBucketAtom.Layout) (z : HistoryInitialSeed.Site)
    (cells slots rows masks nt ns offset len code textStart textLength : ℕ)
    (separated : Separated (initial u B) z) (room : volume u+42 ≤ stride u)
    (ids : B.tableIds=base u 54) (dict : B.dictionary=base u 56) (mask : B.masks=base u 55)
    (cellsFit : 11*cells ≤ stride u) (size : 2+im.advice+nt+ns+im.parameters ≤ stride u)
    (fit : offset+W*len+w*FixedTraceImage.count im.G≤ im.parameters) :
    let pb:=2+im.advice+nt+ns
    let loc : TraceSuffixOracle.Locations:=⟨2,pb,pb+(offset+W*len),code,textStart,textLength⟩
    Immutable (initial u B) z B cells rows masks im loc ∧
      Visible (base u 52) cells (base u 54) slots (base u 56) rows (base u 55) masks im loc := by
  have low:=lower u 12
  have high:=lower u 52
  refine ⟨immutable_regions u cells rows masks B z im _ separated room ids dict mask ?_ ?_ ?_ ?_,
    visible_regions u cells slots rows masks im _ cellsFit ?_ ?_ ?_ ?_⟩
  all_goals try dsimp only
  all_goals omega


/-- The eager public-word reader at an H leaf fits in the native address type
even when it computes addresses for the unused branch of its conditional. -/
theorem suffix_page_extent {depth fuel : ℕ} (I : Image F (16*u^10))
    (M : PrivateRAM.Machine (16*u^10) u u u)
    (trace : NativeTrace.Fits M (FoldTrace.hHeader u I.sizes.rawCount) I.sizes.rawCount depth fuel)
    (age : 40≤u) (gridSize : depth≤u^10+2*u^6) (pb tb : ℕ) (order : pb≤tb)
    (mounted : tb≤TickWorkspace.stride u) :
    TraceSuffixOracle.suffixExtent (TraceSuffixOracle.layout I
      (TraceSuffixOracle.locations (16*u^10) u u u u 2 pb tb I.sizes.rawCount))
      (FoldTrace.hHeader u I.sizes.rawCount)≤2^(16*u^10) := by
  let V:=u^10
  let cap:=2^(8*V)
  let size:=FoldTrace.hHeader u I.sizes.rawCount
  let txt:=SelfAdvice.textSize (16*u^10) u u
  have sixth : u^6≤V:=Nat.pow_le_pow_right (by omega : 0<u) (by decide : 6≤10)
  have unit : u≤V:=Nat.le_self_pow (by decide : 10≠0) _
  have grid : size≤2^(1+depth):=(Nat.le_add_right size fuel).trans trace.grid
  have gap : 2*2^(1+depth)≤cap:=by
    change 2*2^(1+depth)≤2^(8*V)
    rw [Nat.mul_comm,←Nat.pow_succ]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have two : 2≤2^(1+depth):=Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤1+depth)
  have extra : size+2≤cap:=by omega
  have txtEq : size=I.sizes.rawCount+txt:=rfl
  have width : 16*u^10≤txt:=Nat.le_mul_of_pos_left _ (by omega)
  have P : I.sizes.rawParams=2*I.endpointBits+I.advice:=rfl
  have T : I.sizes.rawTable=I.sizes.rawParams+I.parameters:=rfl
  have C : I.sizes.rawCount=I.sizes.rawTable+(16*u^10)*FixedTraceImage.count I.G:=rfl
  have memory : TickWorkspace.stride u≤cap:=by
    change (2^V)^4≤2^(8*V)
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)
  have extent:=TraceSuffixOracle.extent_le
    (s:=TraceSuffixOracle.layout I (TraceSuffixOracle.locations (16*u^10) u u u u 2 pb tb I.sizes.rawCount))
    (S:=size) (cap:=cap) (by change u≤u^10 at unit;omega) (by omega)
    (by change 16*u^10<cap;omega) (by change 2*I.endpointBits<cap;omega)
    (by change I.sizes.rawParams<cap;omega) (by change I.sizes.rawTable<cap;omega)
    (by change I.sizes.rawCount<cap;omega) (by change I.sizes.rawCount+txt<cap;omega)
    (by change 2+txt≤cap;omega) (by change pb≤cap;omega) (by change tb≤cap;omega)
  apply extent.trans
  change 2*2^(8*V)≤2^(16*V)
  rw [Nat.mul_comm,←Nat.pow_succ]
  exact Nat.pow_le_pow_right (by decide : 0<2) (by omega)

end
end ThreeFlat.Diagonal.TraceBitHeader

end OAI
