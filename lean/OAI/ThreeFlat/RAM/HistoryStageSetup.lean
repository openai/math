import OAI.ThreeFlat.RAM.HistoryNodeDirectoryRow
import OAI.ThreeFlat.Diagonal.ShrinkLayerData
import OAI.ThreeFlat.RAM.HistoryStageFormulaChecks
import OAI.ThreeFlat.RAM.HistorySelectedInterior
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchivePath
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # The selected chronological node's native stage header and descriptor banks -/
namespace ThreeFlat.RAM.HistoryStageSetup
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryPartyBatchExec HistoryStageRoot HistoryStageBody
open scoped BigOperators Fin.CommRing
noncomputable section
variable {W : ℕ} (A : HistoryGatherBody.Layout) (cap : ℕ) (m : Memory W)

/-- The selected stage takes its chronological node ID from the real cursor word. -/
def run : StageRun W := ⟨A,cap,numInput A cap (numeric m),m⟩

local notation "X" => run A cap m
local notation "Q" => numInput A cap (numeric m)
local notation "N₀" => childCount Q (numeric m)
local notation "Base" => args A

/-- The exact initial addresses and lengths consumed by all six native descriptor scans. -/
def controls (S : Input) (count : ℕ) : Fin 26 → ℕ :=
  ![S.id,S.nodeBase,S.resultBase,S.kernel,S.stream,S.maps,S.operand,S.ext,S.links,S.copyArguments,
    S.extArguments,loc A 12,HistoryStageBody.hub A,6,links A,4*(count+1),mapArgs A cap,5*(count+1),
    extArgs A cap,3*count,extCommands A cap,7*count,extCommands A cap,extCommands A cap+7*count,
    S.resultBase+8*S.id,6]

theorem id_word (addr : Word W) (cursor : A.nodePorts.cursor<2^W) (wide : 1<2^W) :
    (nodeId A).eval Fin.elim0 m (fun _=>addr)=((Q).id:Word W) := by
  let v : Fin 1→ℕ := fun _=>addr.val
  have fit : (HistoryNodePorts.id A.nodePorts).Fits W (fun _=>0) (numeric m) v :=
    ⟨⟨trivial,cursor⟩,trivial,(m A.nodePorts.cursor).isLt,wide⟩
  have h := closed_eval (HistoryNodePorts.id A.nodePorts) (numeric m) v fit
  change ((HeaderScan.closed (HistoryNodePorts.id A.nodePorts)).eval Fin.elim0 m (fun _=>addr)) =
    ((Formula.natural W (fun _=>0) (numeric m) v (HistoryNodePorts.id A.nodePorts)) : Word W)
  simpa only [word_numeric,v,Fin.cast_val_eq_self] using h

private theorem count_word (addr : Word W) (cursor : A.nodePorts.cursor<2^W)
    (node : HistoryStageRoot.node Q+4<2^W) (wide : 1<2^W) :
    (cn A).eval Fin.elim0 m (fun _=>addr)=(N₀:Word W) := by
  let v : Fin 1→ℕ := fun _=>addr.val
  have fi : (HistoryNodePorts.id A.nodePorts).Fits W (fun _=>0) (numeric m) v :=
    ⟨⟨trivial,cursor⟩,trivial,(m A.nodePorts.cursor).isLt,wide⟩
  have fit : (HistoryNodePorts.childCount A.nodePorts).Fits W (fun _=>0) (numeric m) v :=
    ⟨⟨⟨trivial,⟨trivial,fi,trivial⟩,trivial⟩,trivial,trivial⟩,node⟩
  have h := closed_eval (HistoryNodePorts.childCount A.nodePorts) (numeric m) v fit
  change ((HeaderScan.closed (HistoryNodePorts.childCount A.nodePorts)).eval Fin.elim0 m (fun _=>addr)) =
    ((Formula.natural W (fun _=>0) (numeric m) v (HistoryNodePorts.childCount A.nodePorts)) : Word W)
  simpa only [word_numeric,v,Fin.cast_val_eq_self] using h

private theorem scratch_word (addr : Word W) (k : HistoryScratch.Local) (cursor : A.nodePorts.cursor<2^W)
    (wide : 1<2^W) : (HistoryStageBody.ptr A k).eval Fin.elim0 m (fun _=>addr)=
      (HistoryScratch.atWord A.party.arena A.party.V A.party.motifs A.party.parties (Q).id k 0:Word W) := by
  simp only [HistoryStageBody.ptr,a,times,l,Term.eval_binary,Term.eval_literal,
    id_word A cap m addr cursor wide,BinaryOp.eval,HistoryScratch.atWord,Nat.add_zero,Nat.cast_add,Nat.cast_mul]

private theorem selected_word (addr : Word W) (idx : ℕ) (key : Term W 0 1)
    (xs : List (Term W 0 1)) (pos : idx<xs.length) (room : idx<2^W)
    (index : key.eval Fin.elim0 m (fun _=>addr)=(idx:Word W)) :
    (HistoryStageBody.select key 0 xs).eval Fin.elim0 m (fun _=>addr)=(xs[idx]).eval Fin.elim0 m (fun _=>addr) := by
  have same (start : ℕ) (ys : List (Term W 0 1)) :
      HistoryStageBody.select key start ys=HistoryMotifJoin.select key start ys := by
    induction ys generalizing start with
    | nil=>rfl
    | cons h t ih=>
      simp only [HistoryStageBody.select,HistoryMotifJoin.select,ih]
      rfl
  rw [same]
  exact HistoryMotifJoin.select_at m addr key 0 idx xs pos (by omega) (by simpa using index)

private theorem controls_list (S : Input) (count : ℕ) :
    List.ofFn (controls A cap S count) =
      [S.id,S.nodeBase,S.resultBase,S.kernel,S.stream,S.maps,S.operand,S.ext,S.links,S.copyArguments,
       S.extArguments,loc A 12,HistoryStageBody.hub A,6,links A,4*(count+1),mapArgs A cap,5*(count+1),
       extArgs A cap,3*count,extCommands A cap,7*count,extCommands A cap,extCommands A cap+7*count,
       S.resultBase+8*S.id,6] := rfl

private theorem fields_to_controls (p : Word W) (cursor : A.nodePorts.cursor<2^W)
    (node : HistoryStageRoot.node Q+4<2^W) (wide : 1<2^W) :
    (fields (W:=W) A cap).map (fun t => t.eval Fin.elim0 m (fun _=>p)) =
      (List.ofFn (controls A cap Q N₀)).map (fun v : ℕ => (v : Word W)) := by
  have nid := id_word A cap m p cursor wide
  have size := count_word A cap m p cursor node wide
  have address (k : HistoryScratch.Local) := scratch_word A cap m p k cursor wide
  rw [controls_list]
  cases mode : A.mode <;>
    simp only [fields, input, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, cache, HistoryStageBody.a, times, l,
      Term.eval_binary, Term.eval_literal, nid, size, address, BinaryOp.eval,
      numInput, mode, Nat.cast_add, Nat.cast_mul, Nat.cast_one]

open private equalEntry difference from OAI.ThreeFlat.RAM.HistoryGatherBody

private theorem selected_header_word (xs : List (Term W 0 1)) (start : ℕ) (j : Fin 26)
    (values : Fin 26 → ℕ) (space : start+26 < 2^W) (len : xs.length=26)
    (semantic : xs.map (fun t => t.eval Fin.elim0 m (fun _ => ((start+j.val : ℕ) : Word W))) =
      (List.ofFn values).map (fun v : ℕ => (v : Word W))) :
    HistoryMotifJoin.headerImage (HistoryStageBody.select (cut (.result 0) (l start)) 0 xs)
      start xs.length m (start+j.val) = (values j : Word W) := by
  let p : Word W := ((start+j.val:ℕ):Word W)
  have small : start+j.val < 2^W := by have := j.isLt; omega
  have pos : j.val < xs.length := by rw [len]; exact j.isLt
  have inside : start ≤ start+j.val ∧ start+j.val < start+xs.length := by omega
  rw [HistoryMotifJoin.headerImage,fillSegment,ite_eq_left inside]
  have key : (cut (.result 0) (l start) : Term W 0 1).eval Fin.elim0 m (fun _=>p)=(j.val:Word W) := by
    have a : p.val=start+j.val := Fin.val_cast_of_lt small
    have b : (start:Word W).val=start := Fin.val_cast_of_lt (by omega)
    simpa only [cut,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval,Comparison.test,
      BinaryOp.eval,HistoryGatherBody.cutWord,decide_eq_true_eq,Nat.cast_zero] using
      difference p (start:Word W) start j.val b a
  refine (selected_word m p j.val _ xs pos (by omega) key).trans ?_
  have entry := equalEntry semantic j.val (by simpa only [List.length_map] using pos)
    (by simpa only [List.length_map,List.length_ofFn] using j.isLt)
  simpa only [List.getElem_map,List.getElem_ofFn] using entry

theorem initialized_words (cursor : A.nodePorts.cursor<2^W) (node : HistoryStageRoot.node Q+4<2^W)
    (space : Base+26<2^W) (j : Fin 26) :
    (X).initialized (Base+j.val)=(controls A cap Q N₀ j:Word W) :=
  selected_header_word m (fields (W:=W) A cap) (args A) j (controls A cap Q N₀) space rfl
    (fields_to_controls A cap m ((args A+j.val:ℕ):Word W) cursor node (by omega))


/-- Physical observation of the retained 26-word control area. -/
def ControlsAt (S : Input) (count : ℕ) (mem : Memory W) := ∀ j : Fin 26,
  mem (Base+j.val)=(controls A cap S count j:Word W)

theorem ControlsAt.fill {S : Input} {count : ℕ} {mem : Memory W}
    (old : ControlsAt A cap S count mem) {start len : ℕ} (data : ℕ→Word W)
    (above : Base+26 ≤ start) : ControlsAt A cap S count (fillSegment start len data mem) := by
  intro j
  have outside : ¬(start≤Base+j.val ∧ Base+j.val<start+len) := by have:=j.isLt;omega
  simpa only [fillSegment,ite_eq_right outside] using old j

def off : Bank→ℕ
  | .hub=>0 | .link=>2 | .mapArgs=>4 | .extArgs=>6 | .extCommand=>8 | .result=>12

private theorem select_input (S : Input) (count : ℕ) (f : Fin 11) :
    controls A cap S count ⟨f.val,by have:=f.isLt;omega⟩=S.words f := by
  fin_cases f <;> rfl

theorem ControlsAt.input {S : Input} {count : ℕ} {mem : Memory W}
    (resident : ControlsAt A cap S count mem) (room : ∀ f,S.words f<2^W) (f : Fin 11) :
    numeric mem (Base+f.val)=S.words f := by
  have h:=resident ⟨f.val,by have:=f.isLt;omega⟩
  rw [select_input] at h
  exact (congrArg Fin.val h).trans (Fin.val_cast_of_lt (room f))

private theorem scan_read {S : Input} {count : ℕ} {mem : Memory W}
    (resident : ControlsAt A cap S count mem) (space : Base+26<2^W) (k : ℕ) (bound : k<14) :
    HeaderScan.headerWord mem ((loc A 11:ℕ):Word W) k=
      (controls A cap S count ⟨12+k,by omega⟩:Word W) := by
  have ptr:=resident (11:Fin 26)
  change mem (Base+11)=(loc A 12:Word W) at ptr
  have eq11 : loc A 11=Base+11 := by simp [args,loc]
  have eq12 : loc A 12=Base+12 := by simp [args,loc]
  unfold HeaderScan.headerWord
  rw [Fin.val_cast_of_lt (by omega : loc A 11<2^W),eq11,ptr,←Nat.cast_add,
    Fin.val_cast_of_lt (by omega : loc A 12+k<2^W),eq12,Nat.add_assoc]
  exact resident ⟨12+k,by omega⟩

theorem ControlsAt.scan {S : Input} {count : ℕ} {mem : Memory W}
    (resident : ControlsAt A cap S count mem) (space : Base+26<2^W)
    (eqCount : childCount S (numeric mem)=count) (b : Bank) :
    HeaderScan.headerWord mem ((loc A 11:ℕ):Word W) (off b)=(bankBase A cap S b:Word W) ∧
    HeaderScan.headerWord mem ((loc A 11:ℕ):Word W) (off b+1)=(bankSize S (numeric mem) b:Word W) := by
  unfold bankSize
  rw [eqCount,scan_read A cap resident space (off b) (by cases b <;> decide),
    scan_read A cap resident space (off b+1) (by cases b <;> decide)]
  cases b <;> simp [controls,off,bankBase,Bank.width,rowCount]

/-- Every pre-join scan operates above the fixed control words, including when the child list is empty. -/
theorem phase_controls (cursor : A.nodePorts.cursor<2^W) (node : HistoryStageRoot.node Q+4<2^W)
    (space : Base+26<2^W) :
    ControlsAt A cap Q N₀ (X).initialized ∧ ControlsAt A cap Q N₀ (X).withHub ∧
    ControlsAt A cap Q N₀ (X).withLinks ∧ ControlsAt A cap Q N₀ (X).withMap ∧
    ControlsAt A cap Q N₀ (X).withSources ∧ ControlsAt A cap Q N₀ (X).withCommands ∧
    ControlsAt A cap Q N₀ (X).mounted := by
  have init := initialized_words A cap m cursor node space
  have h : ControlsAt A cap Q N₀ (X).withHub := ControlsAt.fill A cap init _ (by
    change Base+26≤HistoryStageBody.hub A;simp [args,HistoryStageBody.hub,loc])
  have li : ControlsAt A cap Q N₀ (X).withLinks := ControlsAt.fill A cap h _ (by
    change Base+26≤links A;simp [args,links,loc])
  have maps : ControlsAt A cap Q N₀ (X).withMap := ControlsAt.fill A cap li _ (by
    change Base+26≤ mapArgs A cap;unfold mapArgs links args loc;omega)
  have tuples : ControlsAt A cap Q N₀ (X).withSources := ControlsAt.fill A cap maps _ (by
    change Base+26≤extArgs A cap;unfold extArgs mapArgs links args loc;omega)
  have cmd : ControlsAt A cap Q N₀ (X).withCommands := ControlsAt.fill A cap tuples _ (by
    change Base+26≤extCommands A cap;unfold extCommands extArgs mapArgs links args loc;omega)
  exact ⟨init,h,li,maps,tuples,cmd,ControlsAt.fill A cap cmd _ (by
    change Base+26≤HistoryStageBody.hub A+6;unfold HistoryStageBody.hub args loc;omega)⟩


/-- The temporary region begins at the 26-word input and ends after the largest endpoint scan. -/
def limit := extCommands A cap+7*cap

def External (a : ℕ) := a<Base ∨ limit A cap≤a

/-- The external numerical observations are unchanged in every preparation phase. -/
def Retains (start now : Memory W) := ∀ a,External A cap a→now a=start a

private theorem retains_fill {initial now : Memory W} (keep : Retains A cap initial now)
    {lo len : ℕ} (lower : Base≤lo) (upper : lo+len≤limit A cap) (value : ℕ→Word W) :
    Retains A cap initial (fillSegment lo len value now) := by
  intro x out
  have h : ¬(lo≤x ∧ x<lo+len) := by unfold External at out;omega
  simpa [fillSegment,h] using keep x out

theorem phase_frames (capCount : N₀≤cap) (outside : External A cap (HistoryStageRoot.node Q+4)) :
    Retains A cap m (X).initialized ∧ Retains A cap m (X).withHub ∧ Retains A cap m (X).withLinks ∧
    Retains A cap m (X).withMap ∧ Retains A cap m (X).withSources ∧ Retains A cap m (X).withCommands ∧
    Retains A cap m (X).mounted := by
  have refl : Retains A cap m m := fun _ _=>rfl
  have init : Retains A cap m (X).initialized := retains_fill A cap refl (le_refl _) (by
    change Base+26≤limit A cap;unfold limit extCommands extArgs mapArgs links args loc;omega) _
  have step (mem : Memory W) (kept : Retains A cap m mem) (b : Bank) (ordinary : b≠.result) :
      Retains A cap m (adjust A cap Q b mem) := by
    have eq : childCount Q (numeric mem)=N₀ := congrArg Fin.val (kept _ outside)
    apply retains_fill A cap kept
    · cases b <;> simp_all [bankBase,HistoryStageBody.hub,links,mapArgs,extArgs,extCommands,args,loc] <;> omega
    · unfold bankSize;rw [eq]
      cases b
      case result => exact (ordinary rfl).elim
      all_goals simp only [bankBase,Bank.width,rowCount,limit,extCommands,extArgs,mapArgs,links,
        HistoryStageBody.hub,loc]; omega
  have h := step _ init .hub (by decide)
  have li := step _ h .link (by decide)
  have mp := step _ li .mapArgs (by decide)
  have tu := step _ mp .extArgs (by decide)
  have co := step _ tu .extCommand (by decide)
  have mounted : Retains A cap m (X).mounted := retains_fill A cap co (by
    change Base≤HistoryStageBody.hub A+6;unfold args HistoryStageBody.hub loc;omega) (by
    change HistoryStageBody.hub A+6+1≤limit A cap;unfold limit extCommands extArgs mapArgs links HistoryStageBody.hub loc;omega) _
  exact ⟨init,h,li,mp,tu,co,mounted⟩

/-- All lookups behind the two endpoint descriptor banks. Each extent and pointer is
read from a real chronological child record. -/
structure ChildAddresses (S : Input) (raw : ℕ→ℕ) : Prop where
  nodeList : External A cap (HistoryStageRoot.node S+3)
  childList : ∀ i,i<childCount S raw→External A cap (raw (HistoryStageRoot.node S+3)+i)
  ext : ∀ i,i<childCount S raw→External A cap (childPtr S raw i+4)
  width : ∀ i,i<childCount S raw→External A cap (childPtr S raw i+5)

private theorem endpoint_eq {S : Input} {old now : Memory W} (keep : Retains A cap old now)
    (geom : ChildAddresses A cap S (numeric old)) {i : ℕ} (hi : i<childCount S (numeric old)) :
    endpointWords S (numeric now) i=endpointWords S (numeric old) i ∧
    endpointCommand S (numeric now) i=endpointCommand S (numeric old) i := by
  have same (a : ℕ) (out : External A cap a) : numeric now a=numeric old a := congrArg Fin.val (keep a out)
  have child (k : ℕ) (hk : k<childCount S (numeric old)) :
      childPtr S (numeric now) k=childPtr S (numeric old) k := by
    simp only [childPtr,same _ geom.nodeList,same _ (geom.childList k hk)]
  have width (k : ℕ) (hk : k<childCount S (numeric old)) :
      (atResult (numeric now) (childPtr S (numeric now) k)).extCount=
      (atResult (numeric old) (childPtr S (numeric old) k)).extCount := by
    rw [child k hk];exact same _ (geom.width k hk)
  have pre : «prefix» S (numeric now) i Result.extCount=«prefix» S (numeric old) i Result.extCount := by
    unfold «prefix»
    exact Finset.sum_congr rfl fun k hk=>width k (lt_trans (Finset.mem_range.mp hk) hi)
  have ext : (atResult (numeric now) (childPtr S (numeric now) i)).ext=
      (atResult (numeric old) (childPtr S (numeric old) i)).ext := by
    rw [child i hi];exact same _ (geom.ext i hi)
  have args : endpointWords S (numeric now) i=endpointWords S (numeric old) i := by
    simp only [endpointWords,pre,width i hi,ext]
  exact ⟨args,by simp only [endpointCommand,args]⟩

theorem adjust_at (S : Input) (mem : Memory W) (b : Bank) (i : ℕ)
    (h : i<rowCount (childCount S (numeric mem)) b) (j : Fin b.width) :
    adjust A cap S b mem (bankBase A cap S b+(b.width*i+j.val))=(b.word S (numeric mem) i j:Word W) := by
  let start := bankBase A cap S b
  have wid : 0<b.width := by cases b <;> decide
  have lo : start ≤ start+(b.width*i+j.val) := Nat.le_add_right _ _
  have stop : start+(b.width*i+j.val) < start+bankSize S (numeric mem) b := by
    have mul:=Nat.mul_le_mul_left b.width (Nat.succ_le_of_lt h)
    have col:=j.isLt
    change _ < start+b.width*rowCount (childCount S (numeric mem)) b
    rw [Nat.mul_succ] at mul
    omega
  change fillSegment start _ _ mem (start+(b.width*i+j.val))=_
  rw [fillSegment,ite_eq_left ⟨lo,stop⟩]
  simp only [bankWord,start,Nat.add_sub_cancel_left,Nat.mul_add_div wid,Nat.div_eq_of_lt j.isLt,
    Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]

set_option maxHeartbeats 1000000 in
/-- The mounted operand and command rows retain their common physical child readback. -/
theorem mounted_endpoints (capCount : N₀≤cap) (outside : External A cap (HistoryStageRoot.node Q+4))
    (children : ChildAddresses A cap Q (numeric m)) (i : ℕ) (hi : i<N₀) :
    (∀j : Fin 3,(X).mounted (extArgs A cap+(3*i+j.val))=(endpointWords Q (numeric m) i j:Word W)) ∧
    (∀j : Fin 7,(X).mounted (extCommands A cap+7*i+j.val)=(endpointCommand Q (numeric m) i j:Word W)) := by
  obtain ⟨_,_,_,maps,sources,_,_⟩:=phase_frames A cap m capCount outside
  have countM : childCount Q (numeric (X).withMap)=N₀ := congrArg Fin.val (maps _ outside)
  have countS : childCount Q (numeric (X).withSources)=N₀ := congrArg Fin.val (sources _ outside)
  have sameM:=(endpoint_eq A cap maps children hi).1
  have sameS:=(endpoint_eq A cap sources children hi).2
  have layoutAt : (X).layout=A := rfl
  have mounted (a : ℕ) (h : HistoryStageBody.hub A+7≤a) : (X).mounted a=(X).withCommands a := by
    have miss : ¬(HistoryStageBody.hub A+6≤a ∧ a<HistoryStageBody.hub A+6+1) := by omega
    simp only [StageRun.mounted,layoutAt,HistoryMotifJoin.headerImage,fillSegment,ite_eq_right miss]
  constructor
  · intro j
    have jl:=j.isLt
    have lo : HistoryStageBody.hub A+7≤extArgs A cap+(3*i+j.val) := by
      unfold extArgs mapArgs links HistoryStageBody.hub loc;omega
    have endArg : extArgs A cap+(3*i+j.val)<extCommands A cap := by unfold extCommands;omega
    rw [mounted _ lo]
    have miss : ¬(extCommands A cap≤extArgs A cap+(3*i+j.val) ∧
        extArgs A cap+(3*i+j.val)<extCommands A cap+bankSize Q (numeric (X).withSources) .extCommand) :=
      fun h=>Nat.not_le_of_gt endArg h.1
    simp only [StageRun.withCommands,adjust,layoutAt,show (X).cap=cap from rfl,
      show (X).inputs=Q from rfl,bankBase,fillSegment,ite_eq_right miss]
    have eq:=adjust_at A cap Q (X).withMap .extArgs i
      (by change i<childCount Q (numeric (X).withMap);rwa [countM]) j
    exact eq.trans (congrArg (fun v : Fin 3→ℕ=>(v j:Word W)) sameM)
  · intro j
    have lo : HistoryStageBody.hub A+7≤extCommands A cap+7*i+j.val := by
      unfold extCommands extArgs mapArgs links HistoryStageBody.hub loc;omega
    rw [mounted _ lo,Nat.add_assoc (extCommands A cap) (7*i) j.val]
    have eq:=adjust_at A cap Q (X).withSources .extCommand i
      (by change i<childCount Q (numeric (X).withSources);rwa [countS]) j
    exact eq.trans (congrArg (fun v : Fin 7→ℕ=>(v j:Word W)) sameS)

private theorem id_reads (mem : Memory W) (p : Word W) (cursor : A.nodePorts.cursor<2^W) :
    ∀ x∈(nodeId A).reads Fin.elim0 mem (fun _=>p),x=A.nodePorts.cursor := by
  intro x hx
  let addr : Term W 0 1 := l A.nodePorts.cursor
  change x∈(cut addr.load (l 1)).reads Fin.elim0 mem (fun _=>p) at hx
  simpa [cut,addr,l,Term.reads_select,Term.reads_binary,Term.reads_load,Fin.val_cast_of_lt cursor] using hx

private theorem count_reads (p : Word W) (cursor : A.nodePorts.cursor<2^W)
    (node : HistoryStageRoot.node Q+4<2^W) (wide : 1<2^W) :
    ∀ x∈(cn A).reads Fin.elim0 m (fun _=>p),x=A.nodePorts.cursor ∨ x=HistoryStageRoot.node Q+4 := by
  let addr : Term W 0 1 := a (a (l A.nodePorts.nodes) (times (l 8) (nodeId A))) (l 4)
  have value : addr.eval Fin.elim0 m (fun _=>p)=((HistoryStageRoot.node Q+4:ℕ):Word W) := by
    simp only [addr,a,times,l,Term.eval_binary,Term.eval_literal,id_word A cap m p cursor wide,
      BinaryOp.eval,HistoryStageRoot.node,numInput,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  intro x hx
  change x∈addr.load.reads Fin.elim0 m (fun _=>p) at hx
  simp only [Term.reads_load,value,Fin.val_cast_of_lt node,List.mem_append,List.mem_singleton] at hx
  rcases hx with hx|hx
  · left;apply id_reads A m p cursor
    simpa [addr,a,times,l] using hx
  · exact Or.inr hx

private theorem selector_reads (p : Word W) (R : ℕ→Prop) (key : Term W 0 1)
    (safeKey : ∀ x∈key.reads Fin.elim0 m (fun _=>p),R x)
    (xs : List (Term W 0 1)) (safe : ∀ q∈xs,∀ x∈q.reads Fin.elim0 m (fun _=>p),R x) (start : ℕ) :
    ∀ x∈(HistoryStageBody.select key start xs).reads Fin.elim0 m (fun _=>p),R x := by
  induction xs generalizing start with
  | nil=>simp [HistoryStageBody.select,l]
  | cons h t ih=>
    intro x hx
    simp only [HistoryStageBody.select,Term.reads_select,l,Term.reads_literal,List.nil_append,List.mem_append] at hx
    rcases hx with key|head|tail
    · exact safeKey x key
    · exact safe h (List.mem_cons_self ..) x head
    · exact ih (fun q hq=>safe q (List.mem_cons_of_mem _ hq)) (start+1) x tail

open private Tracked tracked_op tracked_lit from
  OAI.ThreeFlat.RAM.HistoryMotifJoin

private theorem field_reads (p : Word W) (safe : ℕ→Prop)
    (hid : Tracked m p safe (nodeId A)) (hcount : Tracked m p safe (cn A)) :
    ∀ q∈fields A cap,Tracked m p safe q := by
  have empty : ∀ x∈([] : List (Term W 0 1)),Tracked m p safe x := by
    intro x hx
    cases hx
  simp only [fields,List.forall_mem_append]
  constructor
  · cases mode : A.mode <;>
      simp only [input,mode,List.forall_mem_cons,HistoryStageBody.ptr,
        a,times,l,tracked_op,tracked_lit,hid,true_and] <;> exact empty
  · simp only [List.forall_mem_cons,cache,a,times,l,
      tracked_op,tracked_lit,hid,hcount,true_and]; exact empty

/-- The fixed 26 words read only the chronological cursor and the current S44 child count. -/
theorem fixed_frame (cursor : A.nodePorts.cursor<2^W) (node : HistoryStageRoot.node Q+4<2^W)
    (wide : 1<2^W) (cursorOut : External A cap A.nodePorts.cursor)
    (nodeOut : External A cap (HistoryStageRoot.node Q+4)) :
    Protected (joinHeader A cap W) m Base (fields (W:=W) A cap).length := by
  intro p _ _ x hx
  have protect (z : ℕ) (out : External A cap z) : z<Base ∨ Base+(fields (W:=W) A cap).length≤z := by
    have len : (fields (W:=W) A cap).length=26 := rfl
    dsimp only [External] at out
    have under : Base+26≤limit A cap := by unfold limit extCommands extArgs mapArgs links args loc;omega
    omega
  apply protect
  have hid : Tracked m p (External A cap) (nodeId A) := by
    intro y hy;rw [id_reads A m p cursor y hy];exact cursorOut
  have hcount : Tracked m p (External A cap) (cn A) := by
    intro y hy
    rcases count_reads A cap m p cursor node wide y hy with hc|hc
    · rw [hc];exact cursorOut
    · rw [hc];exact nodeOut
  exact selector_reads m p (External A cap) (cut (.result 0) (l Base)) (by
    simp [cut,l,Term.reads]) (fields A cap) (field_reads A cap m p _ hid hcount) 0 x hx

theorem cache_frame (mem : Memory W) (cursor : A.nodePorts.cursor<2^W)
    (outside : External A cap A.nodePorts.cursor) :
    Protected (cache A : Term W 0 1) mem (HistoryStageBody.hub A+6) 1 := by
  intro p _ _ x hx
  have eq:=id_reads A mem p cursor x (by simpa [cache,a,times,l] using hx)
  have lo : Base≤HistoryStageBody.hub A+6 := by unfold HistoryStageBody.hub args loc;omega
  have hi : HistoryStageBody.hub A+6+1≤limit A cap := by
    unfold limit extCommands extArgs mapArgs links HistoryStageBody.hub loc;omega
  unfold External at outside
  omega

/-- All reads from the retained native node lie outside the full preparation interval.
The command and operand rows are generated in that interval. -/
structure SourceCells (S : Input) (raw : ℕ→ℕ) (W : ℕ) : Prop where
  cursor : A.nodePorts.cursor<2^W ∧ External A cap A.nodePorts.cursor
  node : ∀ j : Fin 8,HistoryStageRoot.node S+j.val<2^W ∧ External A cap (HistoryStageRoot.node S+j.val)
  child : ∀ i,i<childCount S raw→ raw (HistoryStageRoot.node S+3)+i<2^W ∧
    External A cap (raw (HistoryStageRoot.node S+3)+i)
  kernel : ∀ j : Fin 6,S.kernel+j.val<2^W ∧ External A cap (S.kernel+j.val)
  old : ∀ i,i<childCount S raw→∀ j : Fin 6,childPtr S raw i+j.val<2^W ∧ External A cap (childPtr S raw i+j.val)
  incident : ∀ j : Fin 2,raw (HistoryStageRoot.node S+6)+j.val<2^W ∧
    External A cap (raw (HistoryStageRoot.node S+6)+j.val)
  last : 0<raw (raw (HistoryStageRoot.node S+6))→∀ j,2≤j→j≤3→
    HistoryStageBounds.lastIncident S raw+j<2^W ∧ External A cap (HistoryStageBounds.lastIncident S raw+j)

private theorem scan_interval (S : Input) (mem : Memory W) (b : Bank) (ordinary : b≠.result)
    (h : childCount S (numeric mem)≤cap) :
    Base+26≤bankBase A cap S b ∧ bankBase A cap S b+bankSize S (numeric mem) b≤limit A cap := by
  cases b <;> simp_all [bankBase,bankSize,Bank.width,rowCount,limit,extCommands,extArgs,mapArgs,
    links,HistoryStageBody.hub,args,loc] <;> omega

private theorem SourceCells.bank (S : Input) (old mem : Memory W) (resident : Retains A cap old mem)
    (cells : SourceCells A cap S (numeric old) W) (b : Bank) (ordinary : b≠.result)
    (children : childCount S (numeric mem)≤cap) (room : limit A cap<2^W) :
    HistoryStageBounds.BankCells A cap S mem b := by
  have ⟨lo,hi⟩:=scan_interval A cap S mem b ordinary children
  have ext (x : ℕ) (h : x<2^W ∧ External A cap x) :
      HistoryStageBounds.Cell W (HistoryStageBounds.BankOutside A cap S mem b) x := by
    refine ⟨h.1,?_⟩;rcases h.2 with h|h <;> unfold HistoryStageBounds.BankOutside <;> omega
  have same (x : ℕ) (h : x<2^W ∧ External A cap x) : numeric mem x=numeric old x :=
    congrArg Fin.val (resident x h.2)
  have node (j : Fin 8) := same _ (cells.node j)
  have index : childCount S (numeric mem)=childCount S (numeric old) := node 4
  have cs : numeric mem (HistoryStageRoot.node S+3)=numeric old (HistoryStageRoot.node S+3) := node 3
  have hp : numeric mem (HistoryStageRoot.node S+6)=numeric old (HistoryStageRoot.node S+6) := node 6
  have cc (i : ℕ) (h : i<childCount S (numeric old)) :
      childPtr S (numeric mem) i=childPtr S (numeric old) i := by
    simp only [childPtr,cs,same _ (cells.child i h)]
  have ha : numeric mem (numeric old (HistoryStageRoot.node S+6))=numeric old (numeric old (HistoryStageRoot.node S+6)) := by
    simpa only [Fin.val_zero,Nat.add_zero] using same _ (cells.incident 0)
  have hb : numeric mem (numeric old (HistoryStageRoot.node S+6)+1)=numeric old (numeric old (HistoryStageRoot.node S+6)+1) :=
    same _ (cells.incident 1)
  constructor
  · intro result;exact (ordinary result).elim
  · intro j
    refine ⟨by have:=j.isLt;omega,Or.inl (by have:=j.isLt;omega)⟩
  · intro j;exact ext _ (cells.node j)
  · intro i h;rw [cs];exact ext _ (cells.child i (index ▸ h))
  · intro j;exact ext _ (cells.kernel j)
  · intro i h j;rw [cc i (index ▸ h)];exact ext _ (cells.old i (index ▸ h) j)
  · intro j;rw [hp];exact ext _ (cells.incident j)
  · intro h j lo hi
    rw [hp,ha] at h
    simpa only [HistoryStageBounds.lastIncident,hp,ha,hb] using ext _ (cells.last h j lo hi)

private theorem ordinary_destination (S : Input) (mem : Memory W) (b : Bank) (ordinary : b≠.result)
    (addr : Word W) : (destination A cap b).eval Fin.elim0 mem (fun _=>addr)=(bankBase A cap S b:Word W) := by
  cases b with
  | result => exact (ordinary rfl).elim
  | hub | link | mapArgs | extArgs | extCommand => rfl

/-- One of the five real stage source banks, with all formula bounds and memory footprints
deduced from the original retained physical node and the actual generated controls. -/
theorem make_bank (mem : Memory W) (b : Bank) (ordinary : b≠.result)
    (control : ControlsAt A cap Q N₀ mem) (retains : Retains A cap m mem)
    (cells : SourceCells A cap Q (numeric m) W) (inputRoom : ∀ f,(Q).words f<2^W)
    (children : N₀≤cap) (space : limit A cap<2^W) :
    BankInput A cap Q b (off b) mem := by
  have i : childCount Q (numeric mem)=N₀ := congrArg Fin.val (retains _ (cells.node 4).2)
  have small : childCount Q (numeric mem)≤cap := by rw [i];exact children
  have ⟨lo,hi⟩:=scan_interval A cap Q mem b ordinary small
  have br : Base+26<2^W := by omega
  have cp : cap<2^W := by dsimp only [limit,extCommands,extArgs,mapArgs,links,loc] at space;omega
  have wide : 11<2^W := by omega
  have scan:=ControlsAt.scan A cap control br i b
  have header:=ControlsAt.input A cap control inputRoom
  have atDest := ordinary_destination A cap Q mem b ordinary
  have checks:=HistoryStageBounds.formula_checks A cap Q mem b header atDest (lt_of_le_of_lt hi space) small cp wide
    (SourceCells.bank A cap Q m mem retains cells b ordinary small space)
  exact ⟨scan.1,scan.2,header,atDest,lt_of_le_of_lt hi space,small,checks.1,checks.2⟩

/-- Natural source / destination allocation for copying the old external pins. -/
structure CopyRanges (S : Input) (raw : ℕ→ℕ) (W : ℕ) : Prop where
  source : ∀ i,i<childCount S raw→Endpoints.srcAddr S raw i+Endpoints.width S raw i<2^W
  dest : ∀ i,i<childCount S raw→Endpoints.toAddr S raw i+Endpoints.width S raw i<2^W
  sourceExternal : ∀ i,i<childCount S raw→∀ j : Fin (Endpoints.width S raw i),
    External A cap (Endpoints.srcAddr S raw i+j.val)
  destExternal : ∀ i,i<childCount S raw→
    Endpoints.toAddr S raw i+Endpoints.width S raw i≤Base ∨ limit A cap≤Endpoints.toAddr S raw i
  sourceSeparate : ∀ i,i<childCount S raw→∀ j : Fin (Endpoints.width S raw i),
    Endpoints.survives S raw (Endpoints.srcAddr S raw i+j.val)

/-- The native chronological setup, including the five descriptor scans, mounted cache pointer
and the actual endpoint copy input. Its hypotheses refer solely to original source addresses. -/
theorem header (cells : SourceCells A cap Q (numeric m) W) (inputRoom : ∀ f,(Q).words f<2^W)
    (children : N₀≤cap) (space : limit A cap<2^W) (ranges : CopyRanges A cap Q (numeric m) W) :
    (X).Header := by
  have geom : ChildAddresses A cap Q (numeric m) :=
    ⟨(cells.node 3).2,fun i h=>(cells.child i h).2,fun i h=>(cells.old i h 4).2,fun i h=>(cells.old i h 5).2⟩
  have span : Base+26≤limit A cap := by unfold limit extCommands extArgs mapArgs links args loc;omega
  have hr : Base+26<2^W := by omega
  have cmdRange : extCommands A cap+7*N₀≤limit A cap := by unfold limit;omega
  have ar : extArgs A cap+3*N₀≤extCommands A cap := by unfold extCommands;omega
  have first : loc A 22+2≤extArgs A cap := by unfold extArgs mapArgs links loc;omega
  have ac : extArgs A cap≤extCommands A cap := by unfold extCommands;omega
  have pc : Base≤loc A 22 := by unfold args loc;omega
  obtain ⟨ci,ch,cl,cm,cs,_,mounted⟩:=phase_controls A cap m cells.cursor.1 (cells.node 4).1 hr
  obtain ⟨fi,fh,fl,fm,fs,_,_⟩:=phase_frames A cap m children (cells.node 4).2
  refine ⟨hr,fixed_frame A cap m cells.cursor.1 (cells.node 4).1 (by omega) cells.cursor.2 (cells.node 4).2,
    make_bank A cap m _ .hub (by decide) ci fi cells inputRoom children space,
    make_bank A cap m _ .link (by decide) ch fh cells inputRoom children space,
    make_bank A cap m _ .mapArgs (by decide) cl fl cells inputRoom children space,
    make_bank A cap m _ .extArgs (by decide) cm fm cells inputRoom children space,
    make_bank A cap m _ .extCommand (by decide) cs fs cells inputRoom children space,
    ?_,cache_frame A cap (X).withCommands cells.cursor.1 cells.cursor.2,?_⟩
  · have upper : HistoryStageBody.hub A+7≤limit A cap := by
      unfold HistoryStageBody.hub limit extCommands extArgs mapArgs links loc;omega
    exact upper.trans_lt space
  · change Endpoints.Banks Q (numeric m) (extCommands A cap) (loc A 22) (X).mounted
    have scalar (k : Fin 26) := mounted k
    have p : loc A 22=Base+22 := by simp [loc,args]
    have ep := mounted_endpoints A cap m children (cells.node 4).2 geom
    refine ⟨by omega,by change extArgs A cap+3*N₀<2^W;omega,ranges.source,ranges.dest,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro i hi j
      change extArgs A cap+(3*i+j.val)≠loc A 22 ∧ _
      have hj:=j.isLt
      constructor
      · omega
      · intro k hk
        change extArgs A cap+(3*i+j.val)<Endpoints.toAddr Q (numeric m) k ∨
          Endpoints.toAddr Q (numeric m) k+Endpoints.width Q (numeric m) k≤extArgs A cap+(3*i+j.val)
        rcases ranges.destExternal k hk with below|above <;> omega
    · intro i hi j
      refine ⟨?_,ranges.sourceSeparate i hi j⟩
      rcases ranges.sourceExternal i hi j with h|h <;> omega
    · intro i hi;rcases ranges.destExternal i hi with h|h <;> omega
    · intro i hi;rcases ranges.destExternal i hi with h|h <;> omega
    · rw [p];exact scalar 22
    · rw [p,Nat.add_assoc];exact scalar 23
    · intro i hi j;exact (ep i hi).2 j
    · intro i hi j;exact (ep i hi).1 j

section Chronological
open Diagonal.NavigationPass Diagonal.NavigationPass.NodePublication NavigationNodeRows

/-- Evaluating the tail of the true four-field half rows in any later journal
memory that retained the original incident header and selected tail row. -/
theorem retained_half {s : Layer} (data : LayerData s) (j : Fin s.count) (stage now : Memory W)
    (head : (stage (s.incident+j.val*2)).val=(data.halfWidth j).length)
    (tail : 0<(data.halfWidth j).length →
      let last := (stage (s.incident+j.val*2+1)).val+4*((data.halfWidth j).length-1)
      (stage (last+3)).val+(stage (last+2)).val=(data.halfWidth j).sum)
    (headerFrame : ∀ k : Fin 2,now (s.incident+j.val*2+k.val)=stage (s.incident+j.val*2+k.val))
    (tailFrame : 0<(data.halfWidth j).length →
      let last := (stage (s.incident+j.val*2+1)).val+4*((data.halfWidth j).length-1)
      now (last+2)=stage (last+2) ∧ now (last+3)=stage (last+3))
    (S : Input) (s44 : numeric now (HistoryStageRoot.node S+6)=s.incident+j.val*2) :
    halfWidth S (numeric now)=(data.halfWidth j).sum := by
  have count : numeric now (s.incident+j.val*2)=(data.halfWidth j).length :=
    (congrArg Fin.val (headerFrame 0)).trans head
  have ptr : numeric now (s.incident+j.val*2+1)=(stage (s.incident+j.val*2+1)).val :=
    congrArg Fin.val (headerFrame 1)
  unfold halfWidth
  rw [s44]
  dsimp only
  rw [count,ptr]
  by_cases zero : (data.halfWidth j).length=0
  · rw [ite_eq_left zero]
    simp [List.length_eq_zero_iff.mp zero]
  · rw [ite_eq_right zero]
    obtain ⟨width,offset⟩:=tailFrame (Nat.pos_of_ne_zero zero)
    simpa only [numeric,width,offset] using tail (Nat.pos_of_ne_zero zero)

section Ports
open Diagonal.HistoryContraction BitLayout
variable {F Pins : Type*} [CommSemiring F] {S : Diagonal.HistoryContraction.Shape} {R : Rewrite S F} {t : Fin R.count}
    (L : PortLayout S Pins) (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
    (order : ∀ v,Fin (count v)≃{j // R.owner t j=v}) (v : (R.target t).Site)

/-- Native stage ports from the published S44/S43 words, actual chronological child
IDs and the two indicated S13 cache fields for each already-computed child. -/
theorem ports {b : Banks} {s : Layer} (data : LayerData s) (j : Fin s.count)
    (Q₀ : Input) (mem : Memory W) (id : Q₀.id=s.first+j.val) (base : Q₀.nodeBase=b.nodes)
    (row : DirectoryRow b s j mem) (read : data.Reads (numeric mem))
    (degree : s.childCount=count v) (small : s.childCount<2^W)
    (listRoom : s.children+j.val*s.childCount<2^W)
    (outerRoom : 2*numeric mem (b.charges+2*(s.first+j.val)+1)<2^W)
    (external : 2*numeric mem (b.charges+2*(s.first+j.val)+1)=(L.inherit V count order).ext v)
    (fresh : halfWidth Q₀ (numeric mem)=V.halfBits v)
    (cache : ∀ i : Fin (count v),let k:=data.child j (Fin.cast degree.symm i)
      numeric mem (Q₀.resultBase+8*k+1)=L.form.width (order v i).val ∧
      numeric mem (Q₀.resultBase+8*k+5)=L.ext (order v i).val) :
    HistoryStageRoot.Ports L V count order v Q₀ (numeric mem) := by
  have nd : HistoryStageRoot.node Q₀=b.nodes+8*(s.first+j.val) := by simp only [HistoryStageRoot.node,id,base]
  have ptr:= (congrArg Fin.val row.childPtr).trans (Fin.val_cast_of_lt listRoom)
  have child (i : Fin (count v)) : childPtr Q₀ (numeric mem) i.val=
      Q₀.resultBase+8*data.child j (Fin.cast degree.symm i) := by
    unfold childPtr
    rw [nd,show numeric mem (b.nodes+8*(s.first+j.val)+3)=_ from ptr]
    rw [show numeric mem (s.children+j.val*s.childCount+i.val)=_ from read.child j (Fin.cast degree.symm i)]
  refine ⟨?_,fresh,?_,?_,?_⟩
  · unfold childCount;rw [nd]
    exact (congrArg Fin.val row.childCount).trans ((Fin.val_cast_of_lt small).trans degree)
  · unfold outer;rw [nd]
    have w : mem (b.nodes+8*(s.first+j.val)+7)=((2*numeric mem (b.charges+2*(s.first+j.val)+1):ℕ):Word W) := by
      simpa only [numeric,Nat.cast_mul,Nat.cast_ofNat,Fin.cast_val_eq_self] using row.external
    exact (congrArg Fin.val w).trans ((Fin.val_cast_of_lt outerRoom).trans external)
  · intro i;rw [child];exact (cache i).1
  · intro i;rw [child];exact (cache i).2

/-- The numerical prefix produced by the actual child scan has the typed
assembler's old half-width order, including its final total at offset count. -/
theorem child_prefix_value (A₀ : HistoryNodePorts.Layout) (T : Input) (raw : ℕ→ℕ)
    (seen : HistoryStageRoot.Ports L V count order v T raw)
    (current : raw A₀.cursor-1=T.id) (nodes : A₀.nodes=T.nodeBase) (cache : A₀.cache=T.resultBase)
    (k : ℕ) (bound : k≤count v) :
    HistoryMotifJoin.childWidth A₀ (count v) raw (A₀.starts+k)=
      ∑ i : Fin k,L.halfBits (order v (i.castLE bound)).val := by
  have deg : raw (A₀.nodes+8*(raw A₀.cursor-1)+4)=count v:=by
    rw [nodes,current];exact seen.degree
  rw [HistoryMotifJoin.childWidth,Nat.add_sub_cancel_left,deg,min_eq_left bound]
  have same : HistoryNodePorts.sum A₀ raw k=HistoryStageRoot.prefix T raw k oldHalf := by
    unfold HistoryNodePorts.sum HistoryStageRoot.prefix
    rw [current,nodes,cache]
    rfl
  rw [same]
  exact HistoryStageRoot.prefix_value oldHalf (L.oldWidths count order v)
    (fun i=>oldWidth_read L count order v T raw i (seen.childArity i) (seen.childExt i)) k bound

theorem child_prefix_word (A₀ : HistoryNodePorts.Layout) (T : Input) (input : Memory W)
    (seen : HistoryStageRoot.Ports L V count order v T (numeric input))
    (current : numeric input A₀.cursor-1=T.id) (nodes : A₀.nodes=T.nodeBase) (cache : A₀.cache=T.resultBase)
    (k : ℕ) (bound : k≤count v) :
    fillSegment A₀.starts (count v+1)
      (fun a=>(HistoryMotifJoin.childWidth A₀ (count v) (numeric input) a:Word W)) input (A₀.starts+k)=
      ((∑ i : Fin k,L.halfBits (order v (i.castLE bound)).val:ℕ):Word W) := by
  rw [fillSegment,ite_eq_left (by constructor <;> omega),child_prefix_value L V count order v A₀ T _ seen current nodes cache k bound]

end Ports
section SelectedChild
open HistoryStageBody.Physical HistoryNodeDirectory HistoryNodeDirectory.Selected
open Diagonal.PhysicalStage Diagonal.HistoryContraction Diagonal.TickWorkspace
variable {nn : ℕ}

private theorem picked_parent (directory : Directory W nn) (nodes : Chronology nn)
    (root : ∀ i,directory.root i=(nodes.root i:Word W)) (child parent : Fin nn)
    (before : child.val<nodes.firstFinal) (owner : nodes.parent child=parent)
    (live : picked directory parent.val=true) : picked directory child.val=true := by
  have equal : directory.root child=directory.root parent := by
    rw [root child,root parent,Chronology.root]
    simp only [dite_eq_left before,owner]
  simpa only [picked,dite_eq_left child.isLt,dite_eq_left parent.isLt,equal] using live

variable {F Pins E : Type} [Field F] {d l D lanes : ℕ} {S : State d l}
  (R : Move F S D lanes) (next : ∀ t,Run F (R.next t))
  (hist : (Run.step R next).plan.History) (steps : Run.WordSteps Pins (Run.step R next))
  (L : S.Words Pins) (N : Forest F L.ports.form) (charges : (Run.step R next).Charges)
  (O : S.ArchiveSites) (path : (Run.step R next).ArchivePath hist charges O)
  (orig : ∀u,Fin (L.ext u)→E)
set_option quotPrecheck false in
local notation "S₁" => path.1
set_option quotPrecheck false in
local notation "last" => ((Run.step R next).finalArchive hist charges O path).1

/-- Looking up a selected child in the actual chronological ledger yields its typed stream,
pin count, inherited endpoint count, and all endpoint values in the current stage input. -/
theorem selected_child_cache_at (v : (R.next hist.1).Site) (u : ℕ) (D₀ : Directory W nn)
    (nodes : Chronology nn) (roots : ∀ i,D₀.root i=(nodes.root i:Word W))
    (id : ((Fin 3→Bool)→F)→ℕ) (vals : Fin nn→NodeValue F) (pointer : E→ℕ)
    (keep : ℕ→Prop) (input previous mem : Memory W)
    (ledger : Ledger u D₀ id vals keep input ((S₁).sites.id v) previous)
    (inside : (S₁).sites.id v<nn) (terminal : (S₁).sites.layer.first≤nodes.firstFinal)
    (ids : nn=(last).first+(last).count)
    (owner : ∀ i : Fin (S₁).sites.layer.childCount,∀ h,
      nodes.parent ⟨(S₁).data.child ((S₁).sites.ord v) i,h⟩=⟨(S₁).sites.id v,inside⟩)
    (selected : picked D₀ ((S₁).sites.id v)=true)
    (values : ∀ (k : Fin nn) (lo : O.layer.first≤k.val),
      vals k=NodeValue.ofSite ((Run.step R next).selectedAt hist steps L N charges O path orig k.val lo
        (by rw [←ids];exact k.isLt)) pointer (vals k).stream (vals k).ext)
    (frame : ∀ (k : Fin nn),k.val<(S₁).sites.id v→∀ a,(vals k).uses u k.val a→mem a=previous a)
    (i : Fin (S₁).sites.layer.childCount) :
    let k:=(S₁).data.child ((S₁).sites.ord v) i
    ∃ bound : k<nn,(NodeValue.ofSite (Run.nodeOfSite L N orig (((S₁).row.children v i).val)) pointer
      (vals ⟨k,bound⟩).stream (vals ⟨k,bound⟩).ext).Cached id u k mem := by
  let k:=(S₁).data.child ((S₁).sites.ord v) i
  have eq : k=O.id (((S₁).row.children v i).val) := (S₁).row.childId v i
  have less : k<(S₁).sites.layer.first := by
    have limit:=(O.ord (((S₁).row.children v i).val)).isLt
    rw [(S₁).row.contiguous,eq]
    exact Nat.add_lt_add_left limit _
  have prior : k<(S₁).sites.id v := lt_of_lt_of_le less (Nat.le_add_right ..)
  let j : Fin nn := ⟨k,prior.trans inside⟩
  have live:=picked_parent D₀ nodes roots j ⟨_,inside⟩ (lt_of_lt_of_le less terminal) (owner i j.isLt) selected
  have record := NodeValue.Cached.retain (vals j) id (ledger.published j prior live) (frame j prior)
  have lo : O.layer.first≤k := by rw [eq];exact Nat.le_add_right ..
  have vv:=values j lo
  have trueChild := Run.selectedChild L N O R next hist steps charges path orig v i lo (by rw [←ids];exact j.isLt)
  change (Run.step R next).selectedAt hist steps L N charges O path orig j.val _ _=_ at trueChild
  rw [trueChild] at vv
  refine ⟨j.isLt,?_⟩
  exact (congrArg (fun val : NodeValue F=>val.Cached id u k mem) vv).mp record

theorem selected_child_cache (v : (R.next hist.1).Site) (u : ℕ) (D₀ : Directory W nn)
    (nodes : Chronology nn) (roots : ∀ i,D₀.root i=(nodes.root i:Word W))
    (id : ((Fin 3→Bool)→F)→ℕ) (vals : Fin nn→NodeValue F) (pointer : E→ℕ)
    (keep : ℕ→Prop) (input previous mem : Memory W)
    (ledger : Ledger u D₀ id vals keep input ((S₁).sites.id v) previous)
    (inside : (S₁).sites.id v<nn) (terminal : (S₁).sites.layer.first≤nodes.firstFinal)
    (ids : nn=(last).first+(last).count)
    (owner : ∀ i : Fin (S₁).sites.layer.childCount,∀ h,
      nodes.parent ⟨(S₁).data.child ((S₁).sites.ord v) i,h⟩=⟨(S₁).sites.id v,inside⟩)
    (selected : picked D₀ ((S₁).sites.id v)=true)
    (values : ∀ (k : Fin nn) (lo : O.layer.first≤k.val),
      vals k=NodeValue.ofSite ((Run.step R next).selectedAt hist steps L N charges O path orig k.val lo
        (by rw [←ids];exact k.isLt)) pointer (vals k).stream (vals k).ext)
    (frame : ∀ (k : Fin nn),k.val<(S₁).sites.id v→∀ a,(vals k).uses u k.val a→mem a=previous a)
    (i : Fin (S₁).sites.layer.childCount) :
    let k:=(S₁).data.child ((S₁).sites.ord v) i
    ∃ stream ext,(NodeValue.ofSite (Run.nodeOfSite L N orig (((S₁).row.children v i).val)) pointer stream ext).Cached id u k mem := by
  obtain ⟨bound,actual⟩:=selected_child_cache_at R next hist steps L N charges O path orig v u D₀
    nodes roots id vals pointer keep input previous mem ledger inside terminal ids owner selected values frame i
  exact ⟨_,_,actual⟩

/-- The previous semantic node's two port values are the actual words observed by
the stage, independent of the concrete S12 stream and endpoint addresses. -/
theorem cache_port_words {z : Run.SelectedNode F Pins E} {u k : ℕ} (pointer : E→ℕ)
    (id : ((Fin 3→Bool)→F)→ℕ) (mem : Memory W)
    (written : ∃ stream ext,(NodeValue.ofSite z pointer stream ext).Cached id u k mem) :
    numeric mem (Diagonal.TickWorkspace.base u 13+8*k+1)=z.arity ∧
    numeric mem (Diagonal.TickWorkspace.base u 13+8*k+5)=z.external := by
  obtain ⟨stream,ext,h⟩:=written
  exact ⟨congrArg HistoryStageRoot.Result.pins h.header,congrArg HistoryStageRoot.Result.extCount h.header⟩

end SelectedChild
section PreparedPorts
open scoped Classical
open Diagonal.PhysicalStage Diagonal.HistoryContraction HistoryStageBody.Physical Diagonal.TickWorkspace
variable {F Pins E : Type} [Field F] {d l D lanes : ℕ} {S : State d l}
variable {R : Move F S D lanes} {branch : Fin R.rules.count}
    (L : S.Words Pins) (step : R.WordStep Pins L branch)
    {old : S.ArchiveSites} {ch : (R.next branch).Site→ℕ} (row : R.ArchiveStep branch old ch)

private theorem half_bits {d₁ l₁ : ℕ} (B : State d₁ l₁) (words : B.Words Pins)
    (order : B.OrderedHalves words) (v : B.Site) : words.ports.halfBits v=B.incidentWidth v := by
  let f := fun i : Fin (2*d₁)=>B.width (Diagonal.CompressorPacking.Native.ShrinkStage.Halves.sourceHalf B.graph (B.chart.symm v) i)
  calc
    _ = ∑ j : Fin (words.count v),f (j.cast (order.count v)) :=
      Finset.sum_congr rfl fun j _=>congrArg B.width (order.edge v j)
    _ = ∑ j : Fin (2*d₁),f j := (finCongr (order.count v)).sum_comp f
    _ = _ := half_total B.graph B.width (B.chart.symm v)

private theorem cast_half {sourceShape targetShape : Diagonal.HistoryContraction.Shape}
    (eq : sourceShape=targetShape) (w : PortLayout targetShape Pins) (y : targetShape.Site) :
    ((eq.symm ▸ w : PortLayout sourceShape Pins).halfBits
      ((Equiv.cast (congrArg Diagonal.HistoryContraction.Shape.Site eq)).symm y))=w.halfBits y := by
  cases eq;rfl

/-- Reading at the end of the padded child-prefix bank saturates at this node's
true count. Its successor bits are precisely the public halves of the same word step. -/
theorem complete_port_width (v : (R.next branch).Site) (input : Input) (raw : ℕ→ℕ)
    (C : HistoryNodePorts.Layout) (cap : ℕ)
    (seen : HistoryStageRoot.Ports L.ports
      ((R.target_eq branch).symm ▸ step.words.ports : PortLayout (R.rules.target branch) Pins)
      step.stage.count step.stage.child (Move.WordStep.targetSite (R:=R) (i:=branch) v) input raw)
    (current : raw C.cursor-1=input.id) (nodes : C.nodes=input.nodeBase) (cache : C.cache=input.resultBase)
    (bounded : step.stage.count (Move.WordStep.targetSite (R:=R) (i:=branch) v)≤cap)
    (arity : let target:=Move.WordStep.targetSite (R:=R) (i:=branch) v
      let fresh:=((R.target_eq branch).symm ▸ step.words.ports : PortLayout (R.rules.target branch) Pins)
      step.stage.rootWidth target=(∑ i,L.ports.halfBits (step.stage.child target i).val)+fresh.halfBits target) :
    HistoryMotifJoin.childWidth C cap raw (C.starts+cap)+(R.next branch).incidentWidth v=
      step.stage.rootWidth (Move.WordStep.targetSite (R:=R) (i:=branch) v) := by
  let z:=Move.WordStep.targetSite (R:=R) (i:=branch) v
  let n:=step.stage.count z
  have count : raw (C.nodes+8*(raw C.cursor-1)+4)=n := by rw [nodes,current];exact seen.degree
  have old:=child_prefix_value L.ports _ step.stage.count step.stage.child z C input raw seen current nodes cache n le_rfl
  have same : HistoryMotifJoin.childWidth C cap raw (C.starts+cap)=
      HistoryMotifJoin.childWidth C n raw (C.starts+n) := by
    have room : n≤cap := bounded
    simp only [HistoryMotifJoin.childWidth,Nat.add_sub_cancel_left,count,min_eq_right room,min_self]
  have newBits:= (cast_half (R.target_eq branch) step.words.ports v).trans
    (half_bits _ step.words step.halves v)
  rw [same,old,arity,←newBits]
  rfl

/-- S44 field six addresses the same incident directory as the ordered native publisher. -/
theorem stage_half {d₁ l₁ : ℕ} {X₀ : State d₁ l₁} (sites : X₀.ArchiveSites)
    {safe : ℕ→Prop} {raw : ℕ→ℕ} (H : State.HalfRows sites safe raw)
    (Q₀ : Input) (v : X₀.Site) (header : raw (HistoryStageRoot.node Q₀+6)=sites.layer.incident+(sites.ord v).val*2) :
    halfWidth Q₀ raw=X₀.incidentWidth v := by
  rw [halfWidth,header,H.count]
  by_cases none : 2*d₁=0
  · have deg : d₁=0 := by omega
    subst d₁;simp [State.incidentWidth]
  · rw [ite_eq_right none]
    let i : Fin (2*d₁):=⟨2*d₁-1,by omega⟩
    have hw:=H.width v i
    have hp:=H.start v i
    change raw (raw (sites.layer.incident+(sites.ord v).val*2+1)+4*i.val+3)+
      raw (raw (sites.layer.incident+(sites.ord v).val*2+1)+4*i.val+2)=_
    rw [hw,hp]
    let f:=fun j : Fin (2*d₁)=>X₀.width (Diagonal.CompressorPacking.Native.ShrinkStage.Halves.sourceHalf
      X₀.graph (X₀.chart.symm v) j)
    exact (half_tail_total (Nat.pos_of_ne_zero none) f).trans (half_total X₀.graph X₀.width (X₀.chart.symm v))

/-- All five stage port observations in the actual assembler's order. Earlier semantic cache
rows come from `selected_child_cache`; the successor pair mass is its own S43 value.
The retained tail is the publisher's last response width and prefix, observed after the journal. -/
theorem stage_ports_of_outer (order : step.ChildOrder row) (v : (R.next branch).Site)
    (Q₀ : Input) (mem : Memory W) (b : Banks) (u : ℕ)
    (directory : DirectoryRow b row.sites.layer (row.sites.ord v) mem)
    (data : row.data.Reads (numeric mem)) (id : Q₀.id=row.sites.id v)
    (baseNodes : Q₀.nodeBase=b.nodes) (cacheBase : Q₀.resultBase=base u 13)
    (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(row.sites.ord v).val*row.sites.layer.childCount<2^W)
    (outerRoom : 2*numeric mem (b.charges+2*row.sites.id v+1)<2^W)
    (mass : 2*numeric mem (b.charges+2*row.sites.id v+1)=step.words.ext v)
    {safe : ℕ→Prop} (halves : State.HalfRows row.sites safe (numeric mem))
    (headFits : row.sites.layer.incident+(row.sites.ord v).val*2<2^W)
    (N : Forest F L.ports.form) (origin : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ)
    (encode : ((Fin 3→Bool)→F)→ℕ)
    (child : ∀ i : Fin row.sites.layer.childCount,∃ stream ext,
      (NodeValue.ofSite (Run.nodeOfSite L N origin (row.row.children v i).val) pointer stream ext).Cached
        encode u (row.data.child (row.sites.ord v) i) mem) :
    let V := ((R.target_eq branch).symm ▸ step.words.ports : PortLayout (R.rules.target branch) Pins)
    HistoryStageRoot.Ports L.ports V step.stage.count step.stage.child
      (Move.WordStep.targetSite (R:=R) (i:=branch) v) Q₀ (numeric mem) := by
  intro V
  let z:=Move.WordStep.targetSite (R:=R) (i:=branch) v
  have eq := step.count_eq row v
  have atNode : numeric mem (HistoryStageRoot.node Q₀+6)=row.sites.layer.incident+(row.sites.ord v).val*2 := by
    rw [HistoryStageRoot.node,id,baseNodes]
    exact (congrArg Fin.val directory.incident).trans (Fin.val_cast_of_lt headFits)
  have fresh : halfWidth Q₀ (numeric mem)=V.halfBits z :=
    (stage_half row.sites halves Q₀ v atNode).trans ((half_bits _ step.words step.halves v).symm.trans
      (cast_half (R.target_eq branch) step.words.ports v).symm)
  refine ports L.ports V step.stage.count step.stage.child z row.data (row.sites.ord v) Q₀ mem id baseNodes
    directory data eq countRoom listRoom outerRoom ?_ fresh ?_
  · change 2*numeric mem (b.charges+2*row.sites.id v+1)=_
    rw [mass]
    exact (step.originOrder v).choose
  · intro i
    let k:=Fin.cast eq.symm i
    have source := cache_port_words pointer encode mem (child k)
    have same : (row.row.children v k).val=(step.stage.child z i).val := order v k
    change numeric mem (base u 13+8*row.data.child (row.sites.ord v) k+1)=
      L.ports.form.width (row.row.children v k).val ∧
      numeric mem (base u 13+8*row.data.child (row.sites.ord v) k+5)=L.ext (row.row.children v k).val at source
    rw [same] at source
    rw [cacheBase]
    exact source

theorem stage_ports (order : step.ChildOrder row) (v : (R.next branch).Site)
    (Q₀ : Input) (mem : Memory W) (b : Banks) (u : ℕ)
    (directory : DirectoryRow b row.sites.layer (row.sites.ord v) mem)
    (data : row.data.Reads (numeric mem)) (id : Q₀.id=row.sites.id v)
    (baseNodes : Q₀.nodeBase=b.nodes) (cacheBase : Q₀.resultBase=base u 13)
    (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(row.sites.ord v).val*row.sites.layer.childCount<2^W)
    (outerRoom : 2*numeric mem (b.charges+2*row.sites.id v+1)<2^W)
    (pay : S.Site→ℕ) (oldExt : ∀ x,L.ext x=2*pay x)
    (mass : numeric mem (b.charges+2*row.sites.id v+1)=∑ x : {x // R.parent branch x=v},pay x.val)
    {safe : ℕ→Prop} (halves : State.HalfRows row.sites safe (numeric mem))
    (headFits : row.sites.layer.incident+(row.sites.ord v).val*2<2^W)
    (N : Forest F L.ports.form) (origin : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ)
    (encode : ((Fin 3→Bool)→F)→ℕ)
    (child : ∀ i : Fin row.sites.layer.childCount,∃ stream ext,
      (NodeValue.ofSite (Run.nodeOfSite L N origin (row.row.children v i).val) pointer stream ext).Cached
        encode u (row.data.child (row.sites.ord v) i) mem) :
    let V := ((R.target_eq branch).symm ▸ step.words.ports : PortLayout (R.rules.target branch) Pins)
    HistoryStageRoot.Ports L.ports V step.stage.count step.stage.child
      (Move.WordStep.targetSite (R:=R) (i:=branch) v) Q₀ (numeric mem) := by
  refine stage_ports_of_outer L step row order v Q₀ mem b u directory data id baseNodes cacheBase
    countRoom listRoom outerRoom ?_ halves headFits N origin pointer encode child
  rw [mass,Finset.mul_sum]
  calc
    _ = ∑ i : Fin (step.stage.count (Move.WordStep.targetSite (R:=R) (i:=branch) v)),2*pay (step.children v i).val :=
      ((step.children v).sum_comp (fun x=>2*pay x.val)).symm
    _ = _ := (Finset.sum_congr rfl fun i _=>(oldExt (step.children v i).val).symm).trans
      (step.originOrder v).choose.symm


end PreparedPorts

end Chronological

section ArbitraryWidth
open HistoryStageBody.Physical Diagonal.TickWorkspace
variable (u : ℕ) (archive : Archive) (family : Family) (mem : Memory W)
local notation "A₀" => layout u archive family
local notation "C₀" => family.childBound
local notation "V₀" => volume u
local notation "T₀" => numInput A₀ C₀ (numeric mem)
local notation "n₀" => childCount T₀ (numeric mem)

/-- The retained descriptor cells occur in the actual navigation heap and
initial metadata banks (S22 and S49). -/
def NavigationCell (u a : ℕ) := base u 20≤a ∧ a<base u 60

/-- A navigation word lies above the stage scratch and is representable by the machine. -/
def ReadableNavigation (W u a : ℕ) := base u 20≤a ∧ a<2^W

private theorem sector_interval (start node width index : ℕ) (inside : index < width) :
    start + node * width^2 ≤ start + (node * width + index) * width + 0 ∧
      start + (node * width + index) * width + 0 + width ≤ start + (node + 1) * width^2 := by
  have fits := Nat.mul_le_mul_right width (Nat.succ_le_of_lt inside)
  rw [Nat.succ_mul] at fits
  simp only [Nat.add_zero, Nat.add_mul, pow_two, Nat.mul_assoc, Nat.one_mul]
  omega

private theorem input_words_fit (s : Input) (top : ℕ)
    (idFit : s.id<top) (nodeFit : s.nodeBase<top) (resultFit : s.resultBase<top)
    (kernelFit : s.kernel<top) (streamFit : s.stream<top) (mapsFit : s.maps<top)
    (operandFit : s.operand<top) (extFit : s.ext<top) (linksFit : s.links<top)
    (copyFit : s.copyArguments<top) (argumentsFit : s.extArguments<top)
    (i : Fin 11) : s.words i<top := by
  fin_cases i <;> first
    | exact idFit | exact nodeFit | exact resultFit | exact kernelFit | exact streamFit
    | exact mapsFit | exact operandFit | exact extFit | exact linksFit | exact copyFit
    | exact argumentsFit

/-- Build the mounted header and all preparation bounds at an independent word width.
The source addresses may be anywhere from S20 up to the machine word limit. -/
theorem header_above (far : base u 60+Diagonal.TickWorkspace.stride u<2^W)
    (age : 40≤u) (smallCap : C₀≤V₀) (childCap : n₀≤C₀)
    (nodeSize : (T₀).id<V₀^2)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V₀)
    (childId : ∀ i,i<n₀→numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)<(T₀).id)
    (childList : ∀ i,i<n₀→ReadableNavigation W u (numeric mem (HistoryStageRoot.node T₀+3)+i))
    (incident : ∀ j : Fin 2,ReadableNavigation W u (numeric mem (HistoryStageRoot.node T₀+6)+j.val))
    (last : 0<numeric mem (numeric mem (HistoryStageRoot.node T₀+6))→∀ j,2≤j→j≤3→
      ReadableNavigation W u (HistoryStageBounds.lastIncident T₀ (numeric mem)+j))
    (oldStops : ∀ i,i<n₀→Endpoints.srcAddr T₀ (numeric mem) i+Endpoints.width T₀ (numeric mem) i≤
      base u 12+(T₀).id*V₀^2)
    (total : HistoryStageRoot.prefix T₀ (numeric mem) n₀ Result.extCount≤V₀) :
    (run A₀ C₀ mem).Header ∧ SourceCells A₀ C₀ T₀ (numeric mem) W ∧
      (∀ j,(T₀).words j<2^W) ∧ CopyRanges A₀ C₀ T₀ (numeric mem) W := by
  let nodeId:=(T₀).id
  let slab:=base u 12+nodeId*V₀^2
  let slabEnd:=base u 12+(nodeId+1)*V₀^2
  have large : 64≤V₀ := by
    change 2^6≤2^(u^10)
    exact Nat.pow_le_pow_right (by decide) ((by omega : 6≤u).trans (Nat.le_self_pow (by decide : 10≠0) _))
  have square : 64*V₀≤V₀^2 := by rw [pow_two];exact Nat.mul_le_mul_right _ large
  have fourth : 8*V₀^2≤Diagonal.TickWorkspace.stride u := by
    change 8*V₀^2≤V₀^4
    calc
      _ ≤ V₀^2*V₀^2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have early (i : ℕ) (h : i<60) : base u i+Diagonal.TickWorkspace.stride u≤base u 60 := apart h
  have space : limit A₀ C₀≤base u 14+Diagonal.TickWorkspace.stride u := by
    change base u 14+V₀+64+55+4*(C₀+1)+5*(C₀+1)+3*C₀+7*C₀≤base u 14+Diagonal.TickWorkspace.stride u
    omega
  have start : base u 14≤args A₀ := by change base u 14≤base u 14+V₀+64+0;omega
  have end14:=early 14 (by decide)
  have end12 : base u 12+Diagonal.TickWorkspace.stride u≤base u 14 := apart (by decide)
  have end13 : base u 13+Diagonal.TickWorkspace.stride u≤base u 14 := apart (by decide)
  have begin18 : base u 14+Diagonal.TickWorkspace.stride u≤base u 18 := apart (by decide)
  have begin20 : base u 14+Diagonal.TickWorkspace.stride u≤base u 20 := apart (by decide)
  have begin44 : base u 14+Diagonal.TickWorkspace.stride u≤base u 44 := apart (by decide)
  have end44:=early 44 (by decide)
  have end18:=early 18 (by decide)
  have slabRoom : slabEnd≤base u 12+Diagonal.TickWorkspace.stride u := by
    change base u 12 + (nodeId + 1) * V₀^2 ≤ base u 12 + V₀^4
    apply Nat.add_le_add_left
    calc
      (nodeId + 1) * V₀^2 ≤ V₀^2 * V₀^2 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt nodeSize)
      _ = V₀^4 := by ring
  have slabLe : slab≤ slabEnd := by dsimp [slab,slabEnd];rw [Nat.add_mul];omega
  let localPtr := fun (k : HistoryScratch.Local)=>HistoryScratch.atWord (base u 12) V₀ family.motifs family.parties nodeId k 0
  have localBound (k : HistoryScratch.Local) (sz : HistoryScratch.sector family.motifs family.parties k<V₀) :
      slab≤localPtr k ∧ localPtr k+V₀≤ slabEnd :=
    sector_interval (base u 12) nodeId V₀ (HistoryScratch.sector family.motifs family.parties k) sz
  have kk : slab≤(T₀).kernel ∧ (T₀).kernel+V₀≤ slabEnd := by
    let kernel := match family.mode with
      | .shrink _ => localPtr ⟨0,0,4,1⟩
      | .refresh .. => localPtr ⟨2,0,3,1⟩
    change slab≤kernel ∧ kernel+V₀≤ slabEnd
    unfold kernel;cases family.mode <;>
      first | exact localBound ⟨0,0,4,1⟩ (by unfold HistoryScratch.sector;dsimp;omega)
            | exact localBound ⟨2,0,3,1⟩ (by unfold HistoryScratch.sector;dsimp;omega)
  have stream : slab≤(T₀).stream ∧ (T₀).stream+V₀≤ slabEnd :=
    localBound ⟨0,0,5,0⟩ (by unfold HistoryScratch.sector;dsimp;omega)
  have ex : slab≤(T₀).ext ∧ (T₀).ext+V₀≤ slabEnd :=
    localBound ⟨0,0,5,1⟩ (by unfold HistoryScratch.sector;dsimp;omega)
  have ext (x : ℕ) (h : ReadableNavigation W u x) : x<2^W ∧ External A₀ C₀ x := by
    obtain ⟨a,b⟩:=h;exact ⟨b,Or.inr (by omega)⟩
  have geom : SourceCells A₀ C₀ T₀ (numeric mem) W := by
    constructor
    · change base u 18<2^W ∧ External A₀ C₀ (base u 18)
      exact ⟨by omega,Or.inr (by omega)⟩
    · intro j
      have hj:=j.isLt
      change base u 44+8*(T₀).id+j.val<_ ∧ External A₀ C₀ (base u 44+8*(T₀).id+j.val)
      exact ⟨by omega,Or.inr (by omega)⟩
    · exact fun i hi=>ext _ (childList i hi)
    · intro j;have hj:=j.isLt;exact ⟨by omega,Or.inl (by omega)⟩
    · intro i hi j
      have old:=childId i hi
      have hj:=j.isLt
      change base u 13+8*numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)+j.val<_ ∧
        External A₀ C₀ (base u 13+8*numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)+j.val)
      exact ⟨by omega,Or.inl (by omega)⟩
    · exact fun j=>ext _ (incident j)
    · exact fun nz j hl hh=>ext _ (last nz j hl hh)
  have inWords : ∀ f,(T₀).words f<2^W := by
    have end16:=early 16 (by decide)
    have map : (T₀).maps=base u 18+5*V₀ := rfl
    have argsEnd : (T₀).extArguments≤limit A₀ C₀ := by change extArgs A₀ C₀≤limit A₀ C₀;unfold limit extCommands;omega
    have operands : (T₀).operand≤(T₀).extArguments := by change mapArgs A₀ C₀≤extArgs A₀ C₀;unfold extArgs;omega
    have links : (T₀).links≤(T₀).operand := by change HistoryStageBody.links A₀≤ mapArgs A₀ C₀;unfold mapArgs;omega
    have nbase : (T₀).nodeBase=base u 44 := rfl
    have rbase : (T₀).resultBase=base u 13 := rfl
    have argsBase : (T₀).copyArguments=base u 16 := rfl
    intro f
    apply input_words_fit T₀ (2^W) (i:=f) <;> omega
  have pre (i : ℕ) (hi : i<n₀) :
      HistoryStageRoot.prefix T₀ (numeric mem) i Result.extCount+Endpoints.width T₀ (numeric mem) i≤V₀ := by
    apply le_trans _ total
    let width := Endpoints.width T₀ (numeric mem)
    change (∑ j ∈ Finset.range i, width j) + width i ≤ ∑ j ∈ Finset.range n₀, width j
    rw [←Finset.sum_range_succ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
      (fun _ _ _=>Nat.zero_le _)
  have ranges : CopyRanges A₀ C₀ T₀ (numeric mem) W := by
    have dst (i : ℕ) (h : i<n₀) : slab≤Endpoints.toAddr T₀ (numeric mem) i ∧
        Endpoints.toAddr T₀ (numeric mem) i+Endpoints.width T₀ (numeric mem) i≤ slabEnd := by
      have p:=pre i h;unfold Endpoints.toAddr;constructor <;> omega
    constructor
    · intro i hi;have old:=oldStops i hi;change _≤ slab at old;omega
    · intro i hi;have e:=(dst i hi).2;omega
    · intro i hi j;have old:=oldStops i hi;change _≤ slab at old
      exact Or.inl (by have:=j.isLt;omega)
    · intro i hi;left; have e:=(dst i hi).2;omega
    · intro i hi j k hk
      have old:=oldStops i hi;change _≤ slab at old
      have d:=(dst k hk).1
      exact Or.inl (by have:=j.isLt;omega)
  exact ⟨header A₀ C₀ mem geom inWords childCap (by omega) ranges,geom,inWords,ranges⟩

end ArbitraryWidth

section Scaled
open HistoryStageBody.Physical Diagonal.TickWorkspace
variable (u : ℕ) (archive : Archive) (family : Family) (mem : Memory (16*u^10))
local notation "A₀" => layout u archive family
local notation "C₀" => family.childBound
local notation "V₀" => volume u
local notation "T₀" => numInput A₀ C₀ (numeric mem)
local notation "n₀" => childCount T₀ (numeric mem)

/-- The original S44 pointers, cumulative inherited extents, and old S12
source stops suffice for all native pre-join scans at the real workspace layout. -/
theorem header_at_scale_geometry (age : 40≤u) (smallCap : C₀≤V₀) (childCap : n₀≤C₀)
    (nodeSize : (T₀).id<V₀^2)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V₀)
    (childId : ∀ i,i<n₀→numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)<(T₀).id)
    (childList : ∀ i,i<n₀→NavigationCell u (numeric mem (HistoryStageRoot.node T₀+3)+i))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric mem (HistoryStageRoot.node T₀+6)+j.val))
    (last : 0<numeric mem (numeric mem (HistoryStageRoot.node T₀+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T₀ (numeric mem)+j))
    (oldStops : ∀ i,i<n₀→Endpoints.srcAddr T₀ (numeric mem) i+Endpoints.width T₀ (numeric mem) i≤
      base u 12+(T₀).id*V₀^2)
    (total : HistoryStageRoot.prefix T₀ (numeric mem) n₀ Result.extCount≤V₀) :
    (run A₀ C₀ mem).Header ∧ SourceCells A₀ C₀ T₀ (numeric mem) (16*u^10) ∧
      (∀ j,(T₀).words j<2^(16*u^10)) ∧ CopyRanges A₀ C₀ T₀ (numeric mem) (16*u^10) := by
  have large : 64≤V₀ := by
    change 2^6≤2^(u^10)
    exact Nat.pow_le_pow_right (by decide) ((by omega : 6≤u).trans (Nat.le_self_pow (by decide : 10≠0) _))
  have vstride : V₀≤Diagonal.TickWorkspace.stride u := Nat.le_self_pow (by decide : 4≠0) V₀
  have far : base u 60+Diagonal.TickWorkspace.stride u<2^(16*u^10) := word_space (by omega) (by omega)
  have read {x : ℕ} (h : NavigationCell u x) : ReadableNavigation (16*u^10) u x :=
    ⟨h.1,h.2.trans_le (by omega)⟩
  exact header_above u archive family mem far age smallCap childCap nodeSize sector childId
    (fun i hi=>read (childList i hi)) (fun j=>read (incident j))
    (fun h j lo hi=>read (last h j lo hi)) oldStops total

theorem header_at_scale_inputs (age : 40≤u) (smallCap : C₀≤V₀) (childCap : n₀≤C₀)
    (nodeSize : (T₀).id<V₀^2)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V₀)
    (childId : ∀ i,i<n₀→numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)<(T₀).id)
    (childList : ∀ i,i<n₀→NavigationCell u (numeric mem (HistoryStageRoot.node T₀+3)+i))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric mem (HistoryStageRoot.node T₀+6)+j.val))
    (last : 0<numeric mem (numeric mem (HistoryStageRoot.node T₀+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T₀ (numeric mem)+j))
    (oldStops : ∀ i,i<n₀→Endpoints.srcAddr T₀ (numeric mem) i+Endpoints.width T₀ (numeric mem) i≤
      base u 12+(T₀).id*V₀^2)
    (total : HistoryStageRoot.prefix T₀ (numeric mem) n₀ Result.extCount≤V₀) :
    (run A₀ C₀ mem).Header ∧ SourceCells A₀ C₀ T₀ (numeric mem) (16*u^10) ∧
      ∀ j,(T₀).words j<2^(16*u^10) := by
  obtain ⟨head,cells,inputs,_⟩:=header_at_scale_geometry u archive family mem age smallCap childCap nodeSize
    sector childId childList incident last oldStops total
  exact ⟨head,cells,inputs⟩

theorem header_at_scale (age : 40≤u) (smallCap : C₀≤V₀) (childCap : n₀≤C₀)
    (nodeSize : (T₀).id<V₀^2)
    (sector : (2*(family.parties+2)*8+5)*32+8≤V₀)
    (childId : ∀ i,i<n₀→numeric mem (numeric mem (HistoryStageRoot.node T₀+3)+i)<(T₀).id)
    (childList : ∀ i,i<n₀→NavigationCell u (numeric mem (HistoryStageRoot.node T₀+3)+i))
    (incident : ∀ j : Fin 2,NavigationCell u (numeric mem (HistoryStageRoot.node T₀+6)+j.val))
    (last : 0<numeric mem (numeric mem (HistoryStageRoot.node T₀+6))→∀ j,2≤j→j≤3→
      NavigationCell u (HistoryStageBounds.lastIncident T₀ (numeric mem)+j))
    (oldStops : ∀ i,i<n₀→Endpoints.srcAddr T₀ (numeric mem) i+Endpoints.width T₀ (numeric mem) i≤
      base u 12+(T₀).id*V₀^2)
    (total : HistoryStageRoot.prefix T₀ (numeric mem) n₀ Result.extCount≤V₀) :
    (run A₀ C₀ mem).Header :=
  (header_at_scale_inputs u archive family mem age smallCap childCap nodeSize sector childId childList
    incident last oldStops total).1

end Scaled
end

end ThreeFlat.RAM.HistoryStageSetup

end OAI
