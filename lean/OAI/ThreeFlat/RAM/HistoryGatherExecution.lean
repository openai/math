import OAI.ThreeFlat.Diagonal.RefreshPartyNumbering
import OAI.ThreeFlat.Diagonal.FixedMotifMaxWidth
import OAI.ThreeFlat.RAM.HistoryPhysicalFamilies
import OAI.ThreeFlat.Diagonal.RefreshSiteTree
import OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
import OAI.ThreeFlat.RAM.HistoryGatherBody
import OAI.ThreeFlat.RAM.HistoryScopeMeaning
import OAI.ThreeFlat.RAM.ExpressionReads
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Exact memory and runtime of the physical party gather -/

namespace ThreeFlat.RAM.HistoryGatherExecution

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure DescriptorExpr DescriptorScan HistoryGatherBody
open scoped BigOperators Fin.CommRing

variable {w : ℕ}

/-- Each source row and gathered word is indexed by its absolute write address. -/
structure Plan (w : ℕ) where
  headerWord : ℕ → Word w
  width : Bool → ℕ → ℕ
  sourceWord : Bool → ℕ → ℕ → Word w
  gatherBase : ℕ
  gatherCount : ℕ
  gatherWord : ℕ → Word w

def cap (A : Layout) (side : Bool) := if side then A.supplyCap else A.demandCap

def headerImage (A : Layout) (P : Plan w) (input : Memory w) : Memory w :=
  fillSegment A.temp (fields (W:=w) A).length P.headerWord input

def portPrefix (A : Layout) (P : Plan w) (side : Bool) (initial : Memory w) (n : ℕ) : Memory w :=
  (List.range n).foldl (fun m j => fillSegment (srcBase A side j) (P.width side j) (P.sourceWord side j) m) initial

def beforePort (A : Layout) (P : Plan w) (input : Memory w) (side : Bool) (j : ℕ) : Memory w :=
  let h := headerImage A P input
  portPrefix A P side (if side then portPrefix A P false h A.demandCap else h) j

def beforeGather (A : Layout) (P : Plan w) (input : Memory w) : Memory w :=
  beforePort A P input true A.supplyCap

def output (A : Layout) (P : Plan w) (input : Memory w) : Memory w :=
  fillSegment P.gatherBase P.gatherCount P.gatherWord (beforeGather A P input)

theorem portPrefix_succ (A : Layout) (P : Plan w) (side : Bool) (m : Memory w) (n : ℕ) :
    portPrefix A P side m (n+1) =
      fillSegment (srcBase A side n) (P.width side n) (P.sourceWord side n) (portPrefix A P side m n) := by
  simp [portPrefix,List.range_succ,List.foldl_append]

private theorem fill_away (lo n x : ℕ) (word : ℕ→Word w) (m : Memory w) (h : x<lo ∨ lo+n≤x) :
    fillSegment lo n word m x=m x := by
  have : ¬(lo≤x ∧ x<lo+n) := by omega
  simp [fillSegment,this]

theorem portPrefix_away (A : Layout) (P : Plan w) (side : Bool) (m : Memory w) (n x : ℕ)
    (away : ∀ j<n, x<srcBase A side j ∨ srcBase A side j+P.width side j≤x) :
    portPrefix A P side m n x=m x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [portPrefix_succ,fill_away _ _ x _ _ (away n (Nat.lt_succ_self n))]
    exact ih (fun j hj => away j (Nat.lt_succ_of_lt hj))

theorem beforePort_away (A : Layout) (P : Plan w) (input : Memory w) (side : Bool) (j x : ℕ)
    (hj : j≤cap A side)
    (away : ∀ q i, i<cap A q → x<srcBase A q i ∨ srcBase A q i + P.width q i≤x) :
    beforePort A P input side j x=headerImage A P input x := by
  cases side with
  | false => exact portPrefix_away A P false _ j x (fun i hi => away false i (hi.trans_le hj))
  | true =>
    exact (portPrefix_away A P true _ j x (fun i hi => away true i (hi.trans_le hj))).trans
      (portPrefix_away A P false _ A.demandCap x (fun i hi => away false i hi))

theorem output_away (A : Layout) (P : Plan w) (input : Memory w) (x : ℕ)
    (header : x<A.temp ∨ A.temp+(fields (W:=w) A).length≤x)
    (ports : ∀ q i, i<cap A q → x<srcBase A q i ∨ srcBase A q i+P.width q i≤x)
    (gather : x<P.gatherBase ∨ P.gatherBase+P.gatherCount≤x) : output A P input x=input x := by
  exact (fill_away _ _ _ _ _ gather).trans ((beforePort_away A P input true _ x le_rfl ports).trans
    (fill_away _ _ _ _ _ header))

/-- All descriptor start/count lanes and the indirect control pointer lie below this endpoint. -/
def headerEnd (A : Layout) := A.temp + 3+2*(A.demandCap+A.supplyCap)

def offset (A : Layout) (side : Bool) (j : ℕ) := 2*slot A side j

def gatherOffset (A : Layout) := 2*(A.demandCap+A.supplyCap)

private theorem offset_le (A : Layout) (q : Bool) (j : ℕ) (hj : j<cap A q) :
    offset A q j ≤ gatherOffset A := by
  cases q <;> dsimp [offset,slot,gatherOffset,cap] at * <;> omega

/-- The emitted affine header contains natural base/length pairs and its own pointer. -/
structure Header (A : Layout) (P : Plan w) (input : Memory w) : Prop where
  room : headerEnd A ≤ 2^w
  pointer : headerImage A P input A.temp = ((A.temp+1 : ℕ) : Word w)
  portStart : ∀ q j, j<cap A q → headerImage A P input (A.temp+1+offset A q j) = (srcBase A q j : Word w)
  portLength : ∀ q j, j<cap A q → headerImage A P input (A.temp+1+(offset A q j+1)) = (P.width q j : Word w)
  gatherStart : headerImage A P input (A.temp+1+gatherOffset A) = (P.gatherBase : Word w)
  gatherLength : headerImage A P input (A.temp+1+(gatherOffset A+1)) = (P.gatherCount : Word w)
  portClear : ∀ q j, j<cap A q → P.width q j=0 ∨ headerEnd A≤ srcBase A q j

/-- A scan may overwrite its output aperture. Its selected value in each such memory
still equals the word written at that absolute address. -/
structure ScanRows (e : Term w 0 1) (input : Memory w) (lo n : ℕ) (word : ℕ→Word w) : Prop where
  room : lo+n<2^w
  value : ∀ (a : Word w) (scratch : Memory w), lo≤a.val → a.val<lo+n →
    agreesOutside lo (lo+n) scratch input → e.eval Fin.elim0 scratch (fun _ => a)=word a.val

theorem ScanRows.of_protected {e : Term w 0 1} {input : Memory w} {lo n : ℕ} {word : ℕ→Word w}
    (room : lo+n<2^w)
    (protect : ∀ a : Word w, lo≤a.val → a.val<lo+n →
      ∀ x ∈ e.reads Fin.elim0 input (fun _=>a), x<lo ∨ lo+n≤x)
    (value : ∀ (a : Word w), lo≤a.val → a.val<lo+n → e.eval Fin.elim0 input (fun _ => a)=word a.val) :
    ScanRows e input lo n word := by
  refine ⟨room,fun a scratch low high frame => ?_⟩
  exact (e.eval_eq_of_agrees_reads Fin.elim0 input scratch (fun _=>a)
    (fun x hx => frame x (protect a low high x hx))).trans (value a low high)

private theorem ScanRows.run {e : Term w 0 1} {input : Memory w} {lo n : ℕ} {word : ℕ→Word w}
    (rows : ScanRows e input lo n word) (control : Word w) (start length : ℕ)
    (h0 : HeaderScan.headerWord input control start=(lo:Word w))
    (h1 : HeaderScan.headerWord input control length=(n:Word w)) :
    (HeaderScan.procedure control start length e).Exec input (fillSegment lo n word input)
      (13+n*(2*e.binds+4)) := by
  exact HistoryPartyBatchExec.scan_dynamic e control start length lo n input word rows.room h0 h1 rows.value

private theorem descriptor (A : Layout) (P : Plan w) (input : Memory w) (hdr : Header A P input)
    (side : Bool) (j off : ℕ) (hj : j≤cap A side) (ho : off≤gatherOffset A+1) :
    HeaderScan.headerWord (beforePort A P input side j) (A.temp : Word w) off =
      headerImage A P input (A.temp+1+off) := by
  have keep (x : ℕ) (hx : x<headerEnd A) := beforePort_away A P input side j x hj
    (fun q i hi => by rcases hdr.portClear q i hi with hz|hle <;> omega)
  have p : A.temp<headerEnd A := by dsimp [headerEnd]; omega
  have bound : A.temp+1+off<headerEnd A := by dsimp [headerEnd,gatherOffset] at *; omega
  change (beforePort A P input side j)
    (((beforePort A P input side j) (A.temp:Word w).val+(off:Word w)).val)=_
  rw [Fin.val_cast_of_lt (p.trans_le hdr.room),keep A.temp p,hdr.pointer,←Nat.cast_add,
    Fin.val_cast_of_lt (bound.trans_le hdr.room)]
  exact keep _ bound

def widthSum (P : Plan w) (side : Bool) (n : ℕ) := ∑ j ∈ Finset.range n,P.width side j

noncomputable def portCharge (A : Layout) (P : Plan w) (side : Bool) (n : ℕ) :=
  13*n + widthSum P side n*(2*sourceCost A.mode side+4)

def headerCharge (w : ℕ) (A : Layout) := 4+(fields (W:=w) A).length*(2*(headerTerm w A).binds+4)

noncomputable def tariff (w : ℕ) (A : Layout) (P : Plan w) := headerCharge w A+
  portCharge A P false A.demandCap+portCharge A P true A.supplyCap+
  (13+P.gatherCount*(2*(gatherTerm w A).binds+4))

private theorem portCharge_succ (A : Layout) (P : Plan w) (q : Bool) (n : ℕ) :
    portCharge A P q (n+1) = portCharge A P q n+(13+P.width q n*(2*sourceCost A.mode q+4)) := by
  simp only [portCharge,widthSum,Finset.sum_range_succ]
  ring

private noncomputable def portCode (w : ℕ) (A : Layout) (q : Bool) (init : Procedure w) (n : ℕ) : Procedure w :=
  (List.range n).foldl (fun u j =>
    u.seq (HeaderScan.procedure (A.temp:Word w) (offset A q j) (offset A q j+1) (sourceTerm w A q j))) init

private theorem portCode_succ (A : Layout) (q : Bool) (init : Procedure w) (n : ℕ) :
    portCode w A q init (n+1) = (portCode w A q init n).seq
      (HeaderScan.procedure (A.temp : Word w) (offset A q n) (offset A q n+1) (sourceTerm w A q n)) := by
  simp [portCode,List.range_succ,List.foldl_append]

private theorem port_exec (A : Layout) (P : Plan w) (input : Memory w) (hdr : Header A P input)
    (q : Bool) (j : ℕ) (hj : j<cap A q)
    (read : ScanRows (sourceTerm w A q j) (beforePort A P input q j)
      (srcBase A q j) (P.width q j) (P.sourceWord q j)) :
    (HeaderScan.procedure (A.temp:Word w) (offset A q j) (offset A q j+1) (sourceTerm w A q j)).Exec
      (beforePort A P input q j) (beforePort A P input q (j+1))
      (13+P.width q j*(2*sourceCost A.mode q+4)) := by
  have ho := offset_le A q j hj
  have h₀ := (descriptor A P input hdr q j (offset A q j) hj.le (by omega)).trans (hdr.portStart q j hj)
  have h₁ := (descriptor A P input hdr q j (offset A q j+1) hj.le (by omega)).trans (hdr.portLength q j hj)
  have cheaper : 2*(sourceTerm w A q j).binds+4 ≤ 2*sourceCost A.mode q+4 := by
    have := source_bound w A q j
    omega
  have eq : beforePort A P input q (j+1) =
      fillSegment (srcBase A q j) (P.width q j) (P.sourceWord q j) (beforePort A P input q j) :=
    portPrefix_succ A P q _ j
  rw [eq]
  intro labels registers slots machine pc reg pub exit installed params cfg mem entry initial
  exact Procedure.Spec.mono (read.run (A.temp:Word w) (offset A q j) (offset A q j+1) h₀ h₁)
    (fun _ h => h) (fun _ _ h => h) (Nat.add_le_add_left (Nat.mul_le_mul_left _ cheaper) _)
    machine pc reg pub exit installed params cfg mem entry initial

private theorem runPorts (A : Layout) (P : Plan w) (input : Memory w) (hdr : Header A P input)
    (side : Bool) (init : Procedure w) (cost : ℕ) (start : init.Exec input (beforePort A P input side 0) cost)
    (reads : ∀ j, j<cap A side → ScanRows (sourceTerm w A side j) (beforePort A P input side j)
      (srcBase A side j) (P.width side j) (P.sourceWord side j)) (n : ℕ) (hn : n≤cap A side) :
    (portCode w A side init n).Exec input (beforePort A P input side n) (cost+portCharge A P side n) := by
  induction n with
  | zero =>
    rw [show portCharge A P side 0 = 0 by simp [portCharge, widthSum], Nat.add_zero]
    exact start
  | succ n ih =>
    have h : n<cap A side := hn
    rw [portCode_succ,portCharge_succ,← Nat.add_assoc]
    intro labels registers slots machine pc reg pub exit installed params cfg mem entry initial
    exact Procedure.Exec.then (ih h.le) (port_exec A P input hdr side n h (reads n h))
      machine pc reg pub exit installed params cfg mem entry initial

/-- The header is written once. The native scans then cover every demand port, every
supply port, and the final gather, each with its own live width and actual row expression. -/
theorem execute (A : Layout) (P : Plan w) (input : Memory w) (hdr : Header A P input)
    (initRows : ScanRows (headerTerm w A) input A.temp (fields (W:=w) A).length P.headerWord)
    (portRows : ∀ q j, j<cap A q → ScanRows (sourceTerm w A q j) (beforePort A P input q j)
      (srcBase A q j) (P.width q j) (P.sourceWord q j))
    (gatherRows : ScanRows (gatherTerm w A) (beforeGather A P input) P.gatherBase P.gatherCount P.gatherWord) :
    (procedure w A).Exec input (output A P input) (tariff w A P) := by
  let init := PhysicalInputPhases.writing (headerTerm w A) Fin.elim0 A.temp (fields (W:=w) A).length
  have initRun : init.Exec input (headerImage A P input) (headerCharge w A) := by
    intro H R K machine pc reg pub exit installed params cfg mem entry initial
    subst mem
    exact PhysicalInputPhases.writing_spec (headerTerm w A) Fin.elim0 A.temp (fields (W:=w) A).length
      initRows.room (fun m=>m=input) P.headerWord (by rintro _ rfl; exact initRows.value)
      machine pc reg pub exit installed params cfg input entry rfl
  let demand := portCode w A false init A.demandCap
  let supply := portCode w A true demand A.supplyCap
  have d : demand.Exec input (beforePort A P input false A.demandCap)
      (headerCharge w A+portCharge A P false A.demandCap) :=
    runPorts A P input hdr false init (headerCharge w A) initRun (portRows false) A.demandCap le_rfl
  have s : supply.Exec input (beforeGather A P input)
      (headerCharge w A+portCharge A P false A.demandCap+portCharge A P true A.supplyCap) :=
    runPorts A P input hdr true demand
    (headerCharge w A+portCharge A P false A.demandCap) d (portRows true) A.supplyCap le_rfl
  let g := gatherOffset A
  have h₀ := (descriptor A P input hdr true A.supplyCap g le_rfl (Nat.le_succ _)).trans hdr.gatherStart
  have h₁ := (descriptor A P input hdr true A.supplyCap (g+1) le_rfl le_rfl).trans hdr.gatherLength
  intro labels registers slots machine pc reg pub exit installed params cfg mem entry initial
  exact Procedure.Exec.then s (gatherRows.run (A.temp:Word w) g (g+1) h₀ h₁)
    machine pc reg pub exit installed params cfg mem entry initial

private theorem portPrefix_hit (A : Layout) (P : Plan w) (q : Bool) (m : Memory w) (n i x : ℕ)
    (hi : i<n) (lo : srcBase A q i≤x) (hx : x<srcBase A q i+P.width q i)
    (later : ∀ j, i<j → j<n → x<srcBase A q j ∨ srcBase A q j+P.width q j≤x) :
    portPrefix A P q m n x=P.sourceWord q i x := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [portPrefix_succ]
    by_cases e : i=n
    · subst i
      simp [fillSegment,lo,hx]
    · rw [fill_away _ _ x _ _ (later n (by omega) (Nat.lt_succ_self n))]
      exact ih (by omega) (fun j hj hn => later j hj (Nat.lt_succ_of_lt hn))

/-- A source aperture retains its generated word in the exact image consumed by the
final gather whenever subsequent port writes are disjoint from this address. -/
theorem beforeGather_source (A : Layout) (P : Plan w) (input : Memory w) (q : Bool) (i x : ℕ)
    (hi : i<cap A q) (lo : srcBase A q i≤x) (hx : x<srcBase A q i+P.width q i)
    (other : ∀ t j, j<cap A t → (q,i)≠(t,j) → x<srcBase A t j ∨ srcBase A t j+P.width t j≤x) :
    beforeGather A P input x=P.sourceWord q i x := by
  cases q with
  | false =>
    exact (portPrefix_away A P true _ A.supplyCap x (fun j hj => other true j hj (by simp))).trans
      (portPrefix_hit A P false _ A.demandCap i x hi lo hx
        (fun j hij hj => other false j hj (fun e => (Nat.ne_of_lt hij) (congrArg Prod.snd e))))
  | true =>
    exact portPrefix_hit A P true _ A.supplyCap i x hi lo hx
      (fun j hij hj => other true j hj (fun e => (Nat.ne_of_lt hij) (congrArg Prod.snd e)))

end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure DescriptorExpr DescriptorScan HistoryGatherBody
open scoped BigOperators Fin.CommRing
variable {w : ℕ}

/-- All control words come from the physical layout and its selected resident pages. -/
noncomputable def nativePlan (A : Layout) (input : Memory w) (sources : Bool → ℕ → ℕ → Word w)
    (gathered : ℕ → Word w) : Plan w where
  headerWord x := ((headerWords A input)[x-A.temp]?).getD 0
  width q j := (physicalWidth A input q j).val
  sourceWord := sources
  gatherBase := ((selected A input).privatePage 2).val
  gatherCount := (partyMapCount A input).val
  gatherWord := gathered

private theorem block_len {α : Type*} (n k : ℕ) (f : ℕ → List α) (len : ∀ j, (f j).length=k) :
    ((List.range n).flatMap f).length=k*n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.flatMap_append,ih,len,Nat.mul_succ]

private theorem block_get {α : Type*} (f : ℕ → List α) (k n j t : ℕ) (v : α)
    (len : ∀ i, (f i).length=k) (hj : j<n) (cell : (f j)[t]?=some v) :
    ((List.range n).flatMap f)[k*j+t]?=some v := by
  obtain ⟨ht',_⟩ := List.getElem?_eq_some_iff.1 cell
  have ht : t<k := by rwa [len j] at ht'
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases h : j=n
    · subst j
      rw [List.getElem?_append_right (by rw [block_len _ _ _ len]; omega),block_len _ _ _ len,
        Nat.add_sub_cancel_left]
      exact cell
    · have small : j+1≤n := by omega
      have m := Nat.mul_le_mul_left k small
      rw [Nat.mul_succ] at m
      rw [List.getElem?_append_left (by rw [block_len _ _ _ len]; omega)]
      exact ih (by omega)

private theorem chunk_get {α : Type*} (pre mid post : List α) (t : ℕ) (v : α) (hit : mid[t]?=some v) :
    (pre++mid++post)[pre.length+t]?=some v := by
  obtain ⟨inside,_⟩ := List.getElem?_eq_some_iff.1 hit
  rw [List.append_assoc,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left,
    List.getElem?_append_left inside,hit]

/-- Word-level values of the real header after its fixed scan. -/
private structure NativeLanes (A : Layout) (input written : Memory w) : Prop where
  pointer : written A.temp=((A.temp+1 : ℕ) : Word w)
  scan (q : Bool) (j : ℕ) (hj : j<cap A q) :
    written (A.temp+1+offset A q j)=(srcBase A q j : Word w) ∧
    written (A.temp+1+(offset A q j+1))=physicalWidth A input q j
  map : written (A.temp+1+gatherOffset A)=(selected A input).privatePage 2 ∧
    written (A.temp+1+(gatherOffset A+1))=partyMapCount A input
  outRow (j : ℕ) (hj : j<A.supplyCap) :
    written (supplyRows A+2*j)=(srcBase A true j : Word w) ∧
    written (supplyRows A+2*j+1)=payloadWidth A input j
  inRow (j : ℕ) (hj : j<A.demandCap) :
    written (demandRows A+3*j)=(srcBase A false j : Word w) ∧
    written (demandRows A+3*j+1)=physicalWidth A input false j ∧
    written (demandRows A+3*j+2)=tileWidth A input j

private theorem native_lanes (A : Layout) (m : Memory w) (sources : Bool→ℕ→ℕ→Word w)
    (gathered : ℕ→Word w) :
    NativeLanes A m (headerImage A (nativePlan A m sources gathered) m) := by
  let first : List (Word w) := [((A.temp+1 : ℕ) : Word w)]
  let port (q : Bool) (j : ℕ) : List (Word w) := [(srcBase A q j : Word w),physicalWidth A m q j]
  let d := (List.range A.demandCap).flatMap (port false)
  let s := (List.range A.supplyCap).flatMap (port true)
  let maps := [(selected A m).privatePage 2,partyMapCount A m]
  let outP (j : ℕ) : List (Word w) := [(srcBase A true j : Word w),payloadWidth A m j]
  let inP (j : ℕ) : List (Word w) := [(srcBase A false j : Word w),physicalWidth A m false j,tileWidth A m j]
  let o := (List.range A.supplyCap).flatMap outP
  let i := (List.range A.demandCap).flatMap inP
  have hd : d.length=2*A.demandCap := block_len _ _ _ (fun _=>rfl)
  have hs : s.length=2*A.supplyCap := block_len _ _ _ (fun _=>rfl)
  have ho : o.length=2*A.supplyCap := block_len _ _ _ (fun _=>rfl)
  let full := headerWords A m
  have shape : full=first++d++s++maps++o++i := rfl
  have get (pre mid post : List (Word w)) (hh : full=pre++mid++post) (t x : ℕ) (v : Word w)
      (idx : x=A.temp+pre.length+t) (hit : mid[t]?=some v) :
      headerImage A (nativePlan A m sources gathered) m x=v := by
    have key : full[pre.length+t]?=some v := by rw [hh]; exact chunk_get pre mid post t v hit
    obtain ⟨small,_⟩ := List.getElem?_eq_some_iff.1 key
    have size : (fields (W:=w) A).length=full.length := by
      simpa [full] using congrArg List.length (fields_value A m (0 : Word w))
    have lt : x<A.temp+(fields (W:=w) A).length := by omega
    have nonneg : A.temp≤x := by omega
    have pos : x-A.temp=pre.length+t := by omega
    change fillSegment _ _ (fun x=> (full[x-A.temp]?).getD 0) m x=_
    simp [fillSegment,nonneg,lt,pos,key]
  have gd (j : ℕ) (hj : j<A.demandCap) (t x : ℕ) (v : Word w)
      (idx : x=A.temp+1+2*j+t) (h : (port false j)[t]?=some v) := get first d (s++maps++o++i)
    (by simp only [shape,List.append_assoc]) (2*j+t) x v (by dsimp [first]; omega)
    (block_get _ 2 _ _ _ _ (fun _=>rfl) hj h)
  have gs (j : ℕ) (hj : j<A.supplyCap) (t x : ℕ) (v : Word w)
      (idx : x=A.temp+1+2*A.demandCap+2*j+t) (h : (port true j)[t]?=some v) :=
    get (first++d) s (maps++o++i) (by simp only [shape,List.append_assoc]) (2*j+t) x v
      (by simp only [List.length_append,hd]; dsimp [first]; omega)
      (block_get _ 2 _ _ _ _ (fun _=>rfl) hj h)
  have gm (t x : ℕ) (v : Word w) (idx : x=A.temp+1+2*(A.demandCap+A.supplyCap)+t)
      (h : maps[t]?=some v) := get (first++d++s) maps (o++i)
    (by simp only [shape,List.append_assoc]) t x v
    (by simp only [List.length_append,hd,hs]; dsimp [first]; omega) h
  have go (j : ℕ) (hj : j<A.supplyCap) (t x : ℕ) (v : Word w)
      (idx : x=supplyRows A+2*j+t) (h : (outP j)[t]?=some v) :=
    get (first++d++s++maps) o i (by simp only [shape,List.append_assoc]) (2*j+t) x v
      (by simp only [List.length_append,hd,hs]; dsimp [first,maps]; dsimp [supplyRows,gathers] at idx; omega)
      (block_get _ 2 _ _ _ _ (fun _=>rfl) hj h)
  have gi (j : ℕ) (hj : j<A.demandCap) (t x : ℕ) (v : Word w)
      (idx : x=demandRows A+3*j+t) (h : (inP j)[t]?=some v) :=
    get (first++d++s++maps++o) i [] (by simp only [shape,List.append_nil]) (3*j+t) x v
      (by simp only [List.length_append,hd,hs,ho]; dsimp [first,maps]; dsimp [supplyRows,demandRows,gathers] at idx; omega)
      (block_get _ 3 _ _ _ _ (fun _=>rfl) hj h)
  refine ⟨get [] first (d++s++maps++o++i) (by simp only [shape,List.nil_append,List.append_assoc]) 0 _ _
    (by simp) rfl,?_,⟨gm 0 _ _ (by dsimp [gatherOffset]) rfl,gm 1 _ _
      (by dsimp [gatherOffset]; omega) rfl⟩,?_,?_⟩
  · intro q j hj
    cases q with
    | false => exact ⟨gd j hj 0 _ _ (by simp [offset,slot]) rfl,gd j hj 1 _ _ (by dsimp [offset,slot]; omega) rfl⟩
    | true => exact ⟨gs j hj 0 _ _ (by dsimp [offset,slot]; omega) rfl,gs j hj 1 _ _ (by dsimp [offset,slot]; omega) rfl⟩
  · intro j hj
    exact ⟨go j hj 0 _ _ (Nat.add_zero _).symm rfl,go j hj 1 _ _ rfl rfl⟩
  · intro j hj
    exact ⟨gi j hj 0 _ _ (Nat.add_zero _).symm rfl,gi j hj 1 _ _ rfl rfl,gi j hj 2 _ _ rfl rfl⟩

theorem native_header (A : Layout) (input : Memory w) (sources : Bool→ℕ→ℕ→Word w)
    (gathered : ℕ→Word w) (room : headerEnd A≤2^w)
    (clear : ∀ q j, j<cap A q → (physicalWidth A input q j).val=0 ∨ headerEnd A≤ srcBase A q j) :
    Header A (nativePlan A input sources gathered) input := by
  have L := native_lanes A input sources gathered
  exact ⟨room,L.pointer,fun q j hj=>(L.scan q j hj).1,fun q j hj=>
    (L.scan q j hj).2.trans (Fin.cast_val_eq_self _).symm,
    L.map.1.trans (Fin.cast_val_eq_self _).symm,L.map.2.trans (Fin.cast_val_eq_self _).symm,clear⟩

end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan HistoryGatherBody
open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking
open Diagonal.HistogramTileNetwork BitLayout
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {W : ℕ}

theorem header_size (A : Layout) : (fields (W:=W) A).length=3+5*A.demandCap+4*A.supplyCap := by
  simp only [fields, List.length_append, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.length_range, List.sum_replicate_nat]; omega

def portsEnd (A : Layout) := A.temp+(1+A.demandCap+A.supplyCap)*A.party.V

private theorem slot_lt (A : Layout) (q : Bool) (j : ℕ) (hj : j<cap A q) :
    slot A q j<A.demandCap+A.supplyCap := by
  cases q <;> dsimp [slot,cap] at * <;> omega

private theorem slot_inj (A : Layout) (q t : Bool) (i j : ℕ) (hi : i<cap A q) (hj : j<cap A t)
    (diff : (q,i)≠(t,j)) : slot A q i ≠ slot A t j := by
  cases q <;> cases t <;> simp [slot,cap] at * <;> omega

theorem aperture (A : Layout) (q : Bool) (j : ℕ) (hj : j<cap A q) :
    A.temp+A.party.V≤ srcBase A q j ∧ srcBase A q j+A.party.V≤portsEnd A := by
  have small := slot_lt A q j hj
  have lo := Nat.mul_le_mul_right A.party.V (show 1≤1+slot A q j by omega)
  have hi := Nat.mul_le_mul_right A.party.V (show (1+slot A q j)+1≤1+A.demandCap+A.supplyCap by omega)
  simp only [one_mul,Nat.add_mul] at lo hi
  dsimp [srcBase,portsEnd]
  simp only [Nat.add_mul,one_mul]
  omega


/-- At any point of a native port scan, each word outside the full S17 interval still
has its value in the state returned by the party's paired copy. -/
theorem beforePort_frame (A : Layout) (P : Plan W) (input : Memory W)
    (q : Bool) (i : ℕ) (hi : i<cap A q) (scratch : Memory W)
    (current : agreesOutside (srcBase A q i) (srcBase A q i+P.width q i) scratch (beforePort A P input q i))
    (headSize : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (widths : ∀side j,j<cap A side→P.width side j≤A.party.V) :
    agreesOutside A.temp (portsEnd A) scratch input := by
  intro addr outside
  have apart (side j) (valid : j<cap A side) : addr<srcBase A side j ∨ srcBase A side j+P.width side j≤addr := by
    have span:=aperture A side j valid
    have fit:=widths side j valid
    omega
  have low:=(aperture A q i hi).1
  have high:=(aperture A q i hi).2
  have head:=(header_size (W:=W) A)
  exact (current addr (apart q i hi)).trans ((beforePort_away A P input q i addr hi.le apart).trans
    (fill_away _ _ _ _ _ (by omega)))

private theorem disjoint_source (A : Layout) (q t : Bool) (i j b : ℕ) (hi : i<cap A q) (hj : j<cap A t)
    (diff : (q,i)≠(t,j)) (hb : b<A.party.V) :
    srcBase A q i+b<srcBase A t j ∨ srcBase A t j+A.party.V≤ srcBase A q i+b := by
  have ne := slot_inj A q t i j hi hj diff
  rcases lt_or_gt_of_ne ne with h|h
  · have m := Nat.mul_le_mul_right A.party.V (show (1+slot A q i)+1≤1+slot A t j by omega)
    rw [Nat.succ_mul] at m
    dsimp [srcBase]
    omega
  · have m := Nat.mul_le_mul_right A.party.V (show (1+slot A t j)+1≤1+slot A q i by omega)
    rw [Nat.succ_mul] at m
    dsimp [srcBase]
    omega

variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h p : ℕ}

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- The party image holds throughout the final scan, including in the memory after
any initial portion of its output has overwritten the private map. The catalogue
hypothesis is the stored public page, indexed by physical column. -/
theorem native_image (A : Layout) (input scratch : Memory W) (sources : Bool→ℕ→ℕ→Word W)
    (gathered : ℕ→Word W)
    (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E → ℕ)
    (B : HistogramTileNetwork.Header (D.Port j) H (fun a=>base a.1.1) k n)
    (portsAt : Fin e ≃ (ports G).Port j) (sw : H→S→ℕ) (v : Histogram H r)
    (old : (a : D.Port j) → Fin (live a.1.1) → BitSource h p)
    (fresh : (a : (ports G).Port j) → Fin (histWidth sw v a.1.1+r*k) → BitSource h p)
    (page : ℕ) (demandCode : Fin n→ℕ) (supplyCode : Fin e→ℕ)
    (nst : n≤A.demandCap) (est : e≤A.supplyCap)
    (digitBound : (∑ u,base (B.ports u).1.1)≤A.digitCap)
    (positive : 0<A.party.V) (resident : portsEnd A≤2^W)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (fits : ∀ q i, i<cap A q → (physicalWidth A input q i).val≤A.party.V)
    (range : let P := nativePlan A input sources gathered
      portsEnd A≤P.gatherBase ∨ P.gatherBase+P.gatherCount≤A.temp)
    (frame : let P := nativePlan A input sources gathered
      agreesOutside P.gatherBase (P.gatherBase+P.gatherCount) scratch (beforeGather A P input))
    (pageClear : let hi := page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap
      (hi≤A.temp ∨ portsEnd A≤page) ∧
      (hi≤((selected A input).privatePage 2).val ∨
        ((selected A input).privatePage 2).val+(partyMapCount A input).val≤page))
    (stored : ∀ x, x<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap →
      (input (page+x)).val=(⟨demandCode,supplyCode,fun u=>base (B.ports u).1.1,
        (portsAt.symm (anchorPort G j)).val⟩ : HistoryPortCatalogue.Page n e).at
        A.demandCap A.supplyCap x)
    (layout : let T := gatherLayout A scratch
      T.copies=r ∧ T.selectorBits=k ∧ T.ports=e ∧ T.headerBits=B.arity ∧ T.tileBits=d ∧
      T.anchor=(portsAt.symm (anchorPort G j)).val ∧
      T.headerTable=page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap)
    (supWidth : ∀ u : Fin e, (physicalWidth A input true u.val).val=histWidth sw v (portsAt u).1.1+r*k)
    (payload : ∀ u : Fin e, (payloadWidth A input u.val).val=histWidth sw v (portsAt u).1.1)
    (demWidth : ∀ u : Fin n, (physicalWidth A input false u.val).val=live (B.ports u).1.1)
    (tile : ∀ u : Fin n, (tileWidth A input u.val).val=base (B.ports u).1.1)
    (oldWords : ∀ (u : Fin n) (b : Fin (live (B.ports u).1.1)),
      (sources false u.val (srcBase A false u.val+b.val)).val=sourceAddress (old (B.ports u) b))
    (newWords : ∀ (u : Fin e) (b : Fin (histWidth sw v (portsAt u).1.1+r*k)),
      (sources true u.val (srcBase A true u.val+b.val)).val=sourceAddress (fresh (portsAt u) b)) :
    HistoryPartyGather.Image (d:=d) D G j base live B portsAt sw v old fresh (gatherLayout A scratch)
      (fun x=>(scratch x).val) := by
  let P := nativePlan A input sources gathered
  let T := gatherLayout A scratch
  have outside (x : ℕ) (lo : A.temp≤x) (hi : x<portsEnd A) :
      scratch x=beforeGather A P input x := by
    apply frame x
    rcases range with before | after
    · exact Or.inl (hi.trans_le before)
    · exact Or.inr (after.trans lo)
  have vEnd : A.temp+A.party.V≤portsEnd A := by
    have m := Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using m) A.temp
  have hdr (x : ℕ) (lo : A.temp≤x) (hi : x<A.temp+A.party.V) : scratch x=headerImage A P input x := by
    rw [outside x lo (hi.trans_le vEnd)]
    exact beforePort_away A P input true _ x le_rfl
      (fun q i hi' => Or.inl (hi.trans_le (aperture A q i hi').1))
  have source (q : Bool) (i b : ℕ) (hi : i<cap A q) (hb : b<(physicalWidth A input q i).val) :
      scratch (srcBase A q i+b)=sources q i (srcBase A q i+b) := by
    have ap := aperture A q i hi
    have le := fits q i hi
    have h : b<P.width q i := hb
    rw [outside _ (by omega) (by omega)]
    apply beforeGather_source A P input q i _ hi (by omega) (by omega)
    intro t j hj diff
    have other := fits t j hj
    change _ ∨ _+(physicalWidth A input t j).val≤_
    rcases disjoint_source A q t i j b hi hj diff (hb.trans_le le) with sm|sm <;> omega
  have immutable (x : ℕ) (hx : x<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap) :
      scratch (page+x)=input (page+x) := by
    obtain ⟨a,b⟩ := pageClear
    have frame' : scratch (page+x)=beforeGather A P input (page+x) := by
      apply frame (page+x)
      rcases b with before | after
      · exact Or.inl ((Nat.add_lt_add_left hx page).trans_le before)
      · exact Or.inr (after.trans (Nat.le_add_right page x))
    apply frame'.trans
    refine (beforePort_away A P input true A.supplyCap (page+x) le_rfl ?_).trans ?_
    · intro q i hi
      have ap := aperture A q i hi
      have small := fits q i hi
      change _ ∨ _+(physicalWidth A input q i).val≤_
      omega
    · apply fill_away
      rw [header_size]
      omega
  have L := native_lanes A input sources gathered
  have ob (u : Fin e) : u.val<A.supplyCap := u.isLt.trans_le est
  have ib (u : Fin n) : u.val<A.demandCap := u.isLt.trans_le nst
  have out (u : Fin e) : (scratch (T.supplyRows+2*u.val)).val=srcBase A true u.val ∧
      (scratch (T.supplyRows+2*u.val+1)).val=histWidth sw v (portsAt u).1.1 := by
    change (scratch (supplyRows A+2*u.val)).val=_ ∧ (scratch (supplyRows A+2*u.val+1)).val=_
    have jsmall := ob u
    have ap := aperture A true u.val jsmall
    have ha : srcBase A true u.val<2^W := by omega
    rcases L.outRow u.val jsmall with ⟨st,ln⟩
    have bounds : A.temp≤ supplyRows A+2*u.val ∧ supplyRows A+2*u.val+1<A.temp+A.party.V := by
      dsimp [supplyRows,gathers]; omega
    rw [hdr _ bounds.1 (by omega),hdr _ (by omega) bounds.2,st,ln,Fin.val_cast_of_lt ha,payload]
    exact ⟨rfl,rfl⟩
  have inp (u : Fin n) : (scratch (T.demandRows+3*u.val)).val=srcBase A false u.val ∧
      (scratch (T.demandRows+3*u.val+1)).val=live (B.ports u).1.1 ∧
      (scratch (T.demandRows+3*u.val+2)).val=base (B.ports u).1.1 := by
    change (scratch (demandRows A+3*u.val)).val=_ ∧ (scratch (demandRows A+3*u.val+1)).val=_ ∧
      (scratch (demandRows A+3*u.val+2)).val=_
    have jsmall := ib u
    have ap := aperture A false u.val jsmall
    have ha : srcBase A false u.val<2^W := by omega
    obtain ⟨st,ln,bs⟩ := L.inRow u.val jsmall
    have bounds : A.temp≤demandRows A+3*u.val ∧ demandRows A+3*u.val+2<A.temp+A.party.V := by
      dsimp [demandRows,supplyRows,gathers]; omega
    rw [hdr _ bounds.1 (by omega),hdr _ (by omega) (by omega),hdr _ (by omega) bounds.2,
      st,ln,bs,Fin.val_cast_of_lt ha,demWidth,tile]
    exact ⟨rfl,rfl,rfl⟩
  obtain ⟨copies,selector,ports,header,tileBits,anchor,pageAddr⟩ := layout
  let pg : HistoryPortCatalogue.Page n e := ⟨demandCode,supplyCode,fun u=>base (B.ports u).1.1,
    (portsAt.symm (anchorPort G j)).val⟩
  have digits (u : Fin n) (b : Fin (base (B.ports u).1.1)) :
      (scratch (T.headerTable+2*(finSigmaFinEquiv (n:=fun u : Fin n => base (B.ports u).1.1) ⟨u,b⟩).val)).val=u.val ∧
      (scratch (T.headerTable+2*(finSigmaFinEquiv (n:=fun u : Fin n => base (B.ports u).1.1) ⟨u,b⟩).val+1)).val=b.val := by
    let q := finSigmaFinEquiv (n:=fun u : Fin n => base (B.ports u).1.1) ⟨u,b⟩
    let off := HistoryPortCatalogue.headerBase A.demandCap A.supplyCap+2*q.val
    have small : off+1<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap := by
      have := q.isLt
      dsimp [off,HistoryPortCatalogue.headerBase,HistoryPortCatalogue.supplyBase,HistoryPortCatalogue.stride]
      omega
    have pg0 := immutable off (by omega)
    have pg1 := immutable (off+1) small
    have vals := HistoryPortCatalogue.digits_row (D:=A.demandCap) (E:=A.supplyCap) pg u b
    change (scratch (T.headerTable+2*q.val)).val=u.val ∧ (scratch (T.headerTable+2*q.val+1)).val=b.val
    change T.headerTable=page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap at pageAddr
    rw [show T.headerTable+2*q.val=page+off by dsimp only [off]; omega,
      show page+off+1=page+(off+1) by omega,pg0,pg1,stored off (by omega),stored (off+1) small]
    exact vals
  refine ⟨copies,selector,ports,header,tileBits,anchor,fun u=>(out u).2,?_,fun u=>(inp u).2.1,
    fun u=>(inp u).2.2,?_,?_,fun u b=>(digits u b).1,fun u b=>(digits u b).2⟩
  · intro u b
    change (scratch ((scratch (T.supplyRows+2*u.val)).val+b.val)).val=_
    rw [(out u).1,source true u.val b.val (ob u) (by rw [supWidth]; exact b.isLt)]
    exact newWords u b
  · intro u
    have ap := (aperture A false u.val (ib u)).1
    change (scratch (T.demandRows+3*u.val)).val≠0
    rw [(inp u).1]
    omega
  · intro u b
    change (scratch ((scratch (T.demandRows+3*u.val)).val+b.val)).val=_
    rw [(inp u).1,source false u.val b.val (ib u) (by rw [demWidth]; exact b.isLt)]
    exact oldWords u b

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan HistoryGatherBody
open Diagonal LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking
open Diagonal.HistogramTileNetwork BitLayout
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {W : ℕ}

/-- The semantic private map is addressed by physical output word. -/
def gatheredWord {N : ℕ} (start : ℕ) (pin : Fin N→ℕ) (a : ℕ) : Word W :=
  if h : a-start<N then (pin ⟨a-start,h⟩ : Word W) else 0

variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h p : ℕ}

variable (A : Layout) (input : Memory W) (sources : Bool→ℕ→ℕ→Word W)
  (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E → ℕ)
  (B : HistogramTileNetwork.Header (D.Port j) H (fun a=>base a.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H→S→ℕ) (v : Histogram H r)
  (old : (a : D.Port j) → Fin (live a.1.1) → BitSource h p)
  (fresh : (a : (ports G).Port j) → Fin (histWidth sw v a.1.1+r*k) → BitSource h p)

private abbrev gatherMapBase (layout : Layout) (mem : Memory W) : ℕ :=
  ((selected layout mem).privatePage 2).val

local notation "mapBase" => gatherMapBase A input
local notation "pinCount" => r*(e*k)+(r*B.arity+e*(r*d))
local notation "mapWords" => gatheredWord mapBase
  (fun x : Fin pinCount => sourceAddress (partyPointer D G j base live B portsAt sw v old fresh x))
local notation "P₀" => nativePlan A input sources mapWords

/-- The word written at a live scan position is the address of the actual
input pin or supply pin. Both port orderings are exactly those of the tile. -/
def typedSources (A : Layout) (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E→ℕ)
    (B : HistogramTileNetwork.Header (D.Port j) H (fun a=>base a.1.1) k n)
    (portsAt : Fin e ≃ (ports G).Port j) (sw : H→S→ℕ) (v : Histogram H r)
    (old : (a : D.Port j)→Fin (live a.1.1)→BitSource h p)
    (fresh : (a : (ports G).Port j)→Fin (histWidth sw v a.1.1+r*k)→BitSource h p)
    (q : Bool) (i addr : ℕ) : Word W :=
  let b:=addr-srcBase A q i
  if q then
    if hi:i<e then
      let a:=portsAt ⟨i,hi⟩
      if hb:b<histWidth sw v a.1.1+r*k then (sourceAddress (fresh a ⟨b,hb⟩):Word W) else 0
    else 0
  else
    if hi:i<n then
      let a:=B.ports ⟨i,hi⟩
      if hb:b<live a.1.1 then (sourceAddress (old a ⟨b,hb⟩):Word W) else 0
    else 0
omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem typedSources_demand (i : Fin n) (b : Fin (live (B.ports i).1.1)) :
    typedSources (W:=W) A D G j base live B portsAt sw v old fresh false i.val
      (srcBase A false i.val+b.val)=(sourceAddress (old (B.ports i) b):Word W) := by
  simp [typedSources,i.isLt,b.isLt]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
theorem typedSources_supply (i : Fin e) (b : Fin (histWidth sw v (portsAt i).1.1+r*k)) :
    typedSources (W:=W) A D G j base live B portsAt sw v old fresh true i.val
      (srcBase A true i.val+b.val)=(sourceAddress (fresh (portsAt i) b):Word W) := by
  simp [typedSources,i.isLt,b.isLt]

/-- The header rows retain the physical source-base pointers throughout the
final gather. The only subsequent stores belong to disjoint port apertures
and the disjoint private map. -/
theorem native_bases (A : Layout) (input scratch : Memory W) (sources : Bool→ℕ→ℕ→Word W)
    (gathered : ℕ→Word W) (_positive : 0<A.party.V) (resident : portsEnd A≤2^W)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (range : let P := nativePlan A input sources gathered
      portsEnd A≤P.gatherBase ∨ P.gatherBase+P.gatherCount≤A.temp)
    (frame : let P := nativePlan A input sources gathered
      agreesOutside P.gatherBase (P.gatherBase+P.gatherCount) scratch (beforeGather A P input)) :
    (∀i,i<A.supplyCap → (scratch (supplyRows A+2*i)).val=srcBase A true i) ∧
    (∀i,i<A.demandCap → (scratch (demandRows A+3*i)).val=srcBase A false i) := by
  let P:=nativePlan A input sources gathered
  change portsEnd A ≤ P.gatherBase ∨ P.gatherBase + P.gatherCount ≤ A.temp at range
  change agreesOutside P.gatherBase (P.gatherBase + P.gatherCount) scratch
    (beforeGather A P input) at frame
  have vEnd : A.temp+A.party.V≤portsEnd A := by
    have m:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using m) A.temp
  have hdr (z : ℕ) (low : A.temp≤z) (high : z<A.temp+A.party.V) : scratch z=headerImage A P input z := by
    have outside : z < P.gatherBase ∨ P.gatherBase + P.gatherCount ≤ z :=
      range.imp (fun placed => high.trans_le (vEnd.trans placed)) (fun placed => placed.trans low)
    rw [frame z outside]
    exact beforePort_away A P input true _ z le_rfl
      (fun q i hi => Or.inl (high.trans_le (aperture A q i hi).1))
  let L:=native_lanes A input sources gathered
  constructor
  · intro i hi
    have ap:=aperture A true i hi
    rw [hdr _ (by dsimp [supplyRows,gathers];omega) (by dsimp [supplyRows,gathers];omega),
      (L.outRow i hi).1,Fin.val_cast_of_lt (by omega)]
  · intro i hi
    have ap:=aperture A false i hi
    rw [hdr _ (by dsimp [demandRows,supplyRows,gathers];omega) (by dsimp [demandRows,supplyRows,gathers];omega),
      (L.inRow i hi).1,Fin.val_cast_of_lt (by omega)]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- A gathered pin has all of its actual memory accesses in range whenever
the resident tables, source apertures and tile offsets fit the hardware word. -/
theorem native_gatherFits (scratch : Memory W)
    (I : HistoryPartyGather.Image (d:=d) D G j base live B portsAt sw v old fresh (gatherLayout A scratch)
      (fun a=>(scratch a).val))
    (nst : n≤A.demandCap) (est : e≤A.supplyCap)
    (head : (gatherLayout A scratch).headerTable+2*(∑u,base (B.ports u).1.1)≤2^W)
    (positive : 0<A.party.V) (resident : portsEnd A≤2^W)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (range : portsEnd A≤(P₀).gatherBase ∨ (P₀).gatherBase+(P₀).gatherCount≤A.temp)
    (frame : agreesOutside (P₀).gatherBase ((P₀).gatherBase+(P₀).gatherCount) scratch (beforeGather A P₀ input))
    (outFit : ∀u:Fin e,histWidth sw v (portsAt u).1.1+r*k≤A.party.V)
    (inFit : ∀u:Fin n,live (B.ports u).1.1≤A.party.V)
    (digit : ∀u:Fin n,base (B.ports u).1.1*r≤2^W)
    (scalar : 2+pinCount+k+e+B.arity+e*k+r*(e*k)+r*B.arity+r*d<2^W)
    (x : Fin pinCount) : HistoryPartyGather.formula.Fits W (fun _=>0) (fun a=>(scratch a).val)
      ((gatherLayout A scratch).args x.val) := by
  let T:=gatherLayout A scratch
  have bases:=native_bases A input scratch sources mapWords positive resident headerBound range frame
  have endHdr : A.temp+A.party.V≤2^W := by
    have m:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact (Nat.add_le_add_left (by simpa only [one_mul] using m) A.temp).trans resident
  apply HistoryPartyGather.fits_of_addresses W (fun _=>0) (gatherLayout A scratch) (fun a=>(scratch a).val) x.val
  · rw [I.copies,I.selectorBits,I.ports,I.headerBits,I.tileBits]
    have:=x.isLt
    omega
  · exact fun a=>(scratch a).isLt
  · apply HistoryPartyGather.Image.addressesFit D G j base live B portsAt sw v old fresh I W head (x:=x)
    · change supplyRows A+2*e≤2^W
      dsimp [supplyRows,gathers];omega
    · change demandRows A+3*n≤2^W
      dsimp [demandRows,supplyRows,gathers];omega
    · intro u
      have hi:=u.isLt.trans_le est
      have ap:=aperture A true u.val hi
      change (scratch (supplyRows A+2*u.val)).val+_≤_
      rw [bases.1 u.val hi]
      have:=outFit u
      omega
    · intro u
      have hi:=u.isLt.trans_le nst
      have ap:=aperture A false u.val hi
      change (scratch (demandRows A+3*u.val)).val+_≤_
      rw [bases.2 u.val hi]
      have:=inFit u
      omega
    · exact digit

/-- Static gather tariff of one physical family. Literal addresses and the
machine word width do not enter the coefficient. -/
def schemaCost (B : Layout) := headerCharge 0 B+13*(B.demandCap+B.supplyCap+1)+
  (2*sourceCost B.mode false+4)+(2*sourceCost B.mode true+4)+(2*(gatherTerm 0 B).binds+4)

theorem tariff_le (A B : Layout) (P : Plan W) (mode : A.mode=B.mode)
    (dem : A.demandCap=B.demandCap) (sup : A.supplyCap=B.supplyCap) :
    tariff W A P≤ schemaCost B*(1+widthSum P false A.demandCap+widthSum P true A.supplyCap+P.gatherCount) := by
  let base:=headerCharge 0 B+13*(B.demandCap+B.supplyCap+1)
  let d:=2*sourceCost B.mode false+4
  let s:=2*sourceCost B.mode true+4
  let g:=2*(gatherTerm 0 B).binds+4
  have header : headerCharge W A=headerCharge 0 B := by
    simp only [headerCharge,header_size,header_work (W:=W) (U:=0) A B mode dem sup,dem,sup]
  have hd : d≤ schemaCost B := by dsimp [d,schemaCost];omega
  have hs : s≤ schemaCost B := by dsimp [s,schemaCost];omega
  have hg : g≤ schemaCost B := by dsimp [g,schemaCost];omega
  have hb : base≤ schemaCost B := by dsimp [base,schemaCost];omega
  calc
    _ = base+widthSum P false A.demandCap*d+widthSum P true A.supplyCap*s+P.gatherCount*g := by
      unfold tariff portCharge
      rw [header,mode,gather_work W 0 A B]
      dsimp only [base,d,s,g]
      rw [dem,sup];ring
    _ ≤ schemaCost B+widthSum P false A.demandCap*schemaCost B+
        widthSum P true A.supplyCap*schemaCost B+P.gatherCount*schemaCost B := by gcongr
    _ = _ := by ring

private theorem range_eq {m n : ℕ} (fit : m≤n) (f : ℕ→ℕ) (value : Fin m→ℕ)
    (live : ∀i:Fin m,f i.val=value i) (off : ∀i,i<n→m≤ i→f i=0) :
    (∑i∈Finset.range n,f i)=∑i,value i := by
  have eq0 : (∑i∈Finset.range m,f i)=(∑i∈Finset.range n,f i) := by
    apply Finset.sum_subset (Finset.range_mono fit)
    intro i hn hm
    exact off i (Finset.mem_range.mp hn) (Nat.le_of_not_gt (fun hi=>hm (Finset.mem_range.mpr hi)))
  rw [←eq0,←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _=>live i)

theorem native_headerRows (A : Layout) (input : Memory W) (sources : Bool→ℕ→ℕ→Word W)
    (gathered : ℕ→Word W) (room : A.temp+(fields (W:=W) A).length<2^W)
    (headerStable : ∀ m, agreesOutside A.temp (A.temp+(fields (W:=W) A).length) m input →
      headerWords A m=headerWords A input) :
    ScanRows (headerTerm W A) input A.temp (fields (W:=W) A).length
      (nativePlan A input sources gathered).headerWord := by
  refine ⟨room,?_⟩
  intro ptr m lo hi frame
  let idx := ptr.val-A.temp
  have atPtr : ptr.val=A.temp+idx := by dsimp [idx]; omega
  have size : (headerWords A input).length=(fields (W:=W) A).length := by
    simpa using (congrArg List.length (fields_value A input ptr)).symm
  have valid : idx<(headerWords A input).length := by omega
  have stable := headerStable m frame
  have vm : idx<(headerWords A m).length := by rwa [stable]
  rw [headerTerm_at A m ptr idx atPtr vm]
  change _=((headerWords A input)[idx]?).getD 0
  simpa only [List.getElem?_eq_getElem vm,Option.getD_some] using
    congrArg (fun l : List (Word W) => (l[idx]?).getD 0) stable

/-- An unoccupied catalogue slot performs only the bounded header writes. Its
port scans and final map scan have zero iterations, including on a live node. -/
theorem execute_inactive (A : Layout) (input : Memory W) (inactive : ¬partyActive A input)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V) (resident : portsEnd A<2^W)
    (protectedMask : MaskRoom A input A.temp (A.temp+(fields (W:=W) A).length)) :
    let P := nativePlan A input (fun _ _ _=>0) (fun _=>0)
    (procedure W A).Exec input (headerImage A P input)
      (headerCharge W A+13*A.demandCap+13*A.supplyCap+13) := by
  let P := nativePlan A input (fun _ _ _=>0) (fun _=>0)
  have zero : ∀q j,P.width q j=0 := fun q j=>by
    change (physicalWidth A input q j).val=0
    rw [inactive_width A input inactive]
    rfl
  have noMap : P.gatherCount=0 := by simp [P,nativePlan,partyMapCount,inactive]
  have framePort (q : Bool) (m : Memory W) (n : ℕ) : portPrefix A P q m n=m := by
    induction n with
    | zero => rfl
    | succ n ih => rw [portPrefix_succ,zero,fillSegment_zero,ih]
  have unchanged : output A P input=headerImage A P input := by
    simp only [output,noMap,fillSegment_zero,beforeGather,beforePort,framePort,ite_true]
  have pay : tariff W A P=headerCharge W A+13*A.demandCap+13*A.supplyCap+13 := by
    simp [tariff,portCharge,widthSum,zero,noMap]
  change (procedure W A).Exec input (headerImage A P input) _
  rw [←unchanged,←pay]
  have limit : A.temp+A.party.V≤portsEnd A := by
    have bound:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using bound) A.temp
  have headerRoom : A.temp+(fields (W:=W) A).length<2^W := by rw [header_size];omega
  have ctrl : headerEnd A≤A.temp+A.party.V := by dsimp [headerEnd];omega
  apply execute A P input (native_header A input _ _ (by omega) (fun q i _=>Or.inl (zero q i)))
  · apply native_headerRows A input _ _ headerRoom
    intro m h
    exact inactive_stable A input m inactive (fun active=>inactive ((protectedMask.active h).mp active))
      (privatePage_stable A (h _ protectedMask.cursor) 2)
  · intro q i hi
    rw [zero]
    refine ⟨?_,fun a m lo up _=>False.elim (by omega)⟩
    have ap:=aperture A q i hi
    omega
  · rw [noMap]
    refine ⟨?_,fun a m lo up _=>False.elim (by omega)⟩
    simp [P,nativePlan]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- The native procedure writes the typed party map. Source geometry is read in the
memory current at that port. The final lookup consumes the retained real port image. -/
theorem execute_native
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V) (resident : portsEnd A<2^W)
    (fits : ∀ q i, i<cap A q → (physicalWidth A input q i).val≤A.party.V)
    (mapCount : (partyMapCount A input).val=pinCount) (mapRoom : mapBase+pinCount<2^W)
    (headerStable : ∀ m, agreesOutside A.temp (A.temp+(fields (W:=W) A).length) m input →
      headerWords A m=headerWords A input)
    (source : ∀ q i, i<cap A q → ∀ b, b<(physicalWidth A input q i).val → ∀ m,
      agreesOutside (srcBase A q i) (srcBase A q i+(physicalWidth A input q i).val) m
        (beforePort A P₀ input q i) →
      (geometryTerm W A q).eval (fun _=>0) m (sourceRegisters A m q i (b:Word W)) =
        sources q i (srcBase A q i+b))
    (baseStable : ∀ m, agreesOutside mapBase (mapBase+pinCount) m (beforeGather A P₀ input) →
      (selected A m).privatePage 2=(selected A input).privatePage 2)
    (gatherFits : ∀ m, agreesOutside mapBase (mapBase+pinCount) m (beforeGather A P₀ input) →
      ∀ x : Fin pinCount, HistoryPartyGather.formula.Fits W (fun _=>0) (fun a=>(m a).val)
        ((gatherLayout A m).args x.val))
    (image : ∀ m, agreesOutside mapBase (mapBase+pinCount) m (beforeGather A P₀ input) →
      HistoryPartyGather.Image (d:=d) D G j base live B portsAt sw v old fresh (gatherLayout A m)
        (fun a=>(m a).val)) :
    (procedure W A).Exec input (output A P₀ input) (tariff W A P₀) := by
  let P := P₀
  have limit : A.temp+A.party.V≤portsEnd A := by
    have b := Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using b) A.temp
  have ctrl : headerEnd A≤A.temp+A.party.V := by dsimp [headerEnd]; omega
  apply execute A P input (native_header A input sources _ (by omega) (fun q i hi =>
    Or.inr (ctrl.trans (aperture A q i hi).1)))
  · exact native_headerRows A input sources _ (by rw [header_size];omega) headerStable
  · intro q i hi
    have ap := aperture A q i hi
    have small := fits q i hi
    refine ⟨show srcBase A q i+(physicalWidth A input q i).val<2^W by omega,?_⟩
    intro ptr m lo hi' frame
    let b := ptr.val-srcBase A q i
    have key : ptr.val=srcBase A q i+b := by dsimp [b]; omega
    have wb : b<(physicalWidth A input q i).val := by
      change ptr.val<srcBase A q i+(physicalWidth A input q i).val at hi'
      omega
    rw [sourceTerm_value A m q i b ptr key]
    exact (source q i hi b wb m frame).trans (congrArg (sources q i) key.symm)
  · refine ⟨by change mapBase+(partyMapCount A input).val<2^W; rwa [mapCount],?_⟩
    intro ptr m lo hi frame
    change mapBase≤ptr.val at lo
    change ptr.val< mapBase+(partyMapCount A input).val at hi
    rw [mapCount] at hi
    change agreesOutside mapBase (mapBase+(partyMapCount A input).val) m (beforeGather A P input) at frame
    rw [mapCount] at frame
    have valid : ptr.val-mapBase<pinCount := by omega
    let x : Fin pinCount := ⟨ptr.val-mapBase,valid⟩
    have key : ptr.val=((selected A m).privatePage 2).val+x.val := by
      rw [baseStable m frame]
      change ptr.val=mapBase+(ptr.val-mapBase)
      omega
    rw [gatherTerm_party D G j base live B portsAt sw v old fresh A m ptr x key
      (gatherFits m frame x) (image m frame)]
    change (sourceAddress (partyPointer D G j base live B portsAt sw v old fresh x):Word W)=
      (mapWords) ptr.val
    simp only [gatheredWord,dite_eq_left valid,x]

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] [Nonempty H] in
/-- The complete port scans and the final gathered map, with the header,
cursor, source lists and map address ranges witnessed in their numeric RAM layout. -/
theorem emit_map
    (positive : 0<A.party.V) (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (resident : portsEnd A<2^W) (nst : n≤A.demandCap) (est : e≤A.supplyCap)
    (fits : ∀q i,i<cap A q → (physicalWidth A input q i).val≤A.party.V)
    (mapCount : (partyMapCount A input).val=pinCount) (mapRoom : mapBase+pinCount<2^W)
    (range : portsEnd A≤ mapBase ∨ mapBase+pinCount≤A.temp)
    (footprint : HeaderFootprint A input A.temp (A.temp+(fields (W:=W) A).length))
    (cursorPort : (A.nodePorts.cursor:Word W).val<A.temp ∨ portsEnd A≤(A.nodePorts.cursor:Word W).val)
    (cursorMap : (A.nodePorts.cursor:Word W).val< mapBase ∨ mapBase+pinCount≤(A.nodePorts.cursor:Word W).val)
    (outFit : ∀u:Fin e,histWidth sw v (portsAt u).1.1+r*k≤A.party.V)
    (inFit : ∀u:Fin n,live (B.ports u).1.1≤A.party.V)
    (digit : ∀u:Fin n,base (B.ports u).1.1*r≤2^W)
    (scalar : 2+pinCount+k+e+B.arity+e*k+r*(e*k)+r*B.arity+r*d<2^W)
    (source : ∀q i,i<cap A q → ∀b,b<(physicalWidth A input q i).val → ∀m,
      agreesOutside (srcBase A q i) (srcBase A q i+(physicalWidth A input q i).val) m
        (beforePort A P₀ input q i) →
      (geometryTerm W A q).eval (fun _=>0) m (sourceRegisters A m q i (b:Word W)) =
        sources q i (srcBase A q i+b))
    (tables : ∀m,agreesOutside mapBase (mapBase+pinCount) m (beforeGather A P₀ input) →
      (gatherLayout A m).headerTable+2*(∑u,base (B.ports u).1.1)≤2^W ∧
      HistoryPartyGather.Image (d:=d) D G j base live B portsAt sw v old fresh (gatherLayout A m)
        (fun a=>(m a).val)) :
    (procedure W A).Exec input (output A P₀ input) (tariff W A P₀) ∧
    ∀x:Fin pinCount, output A P₀ input (mapBase+x.val)=
      (sourceAddress (partyPointer D G j base live B portsAt sw v old fresh x):Word W) := by
  let ptr:=(A.nodePorts.cursor:Word W).val
  have stop : A.temp+A.party.V≤portsEnd A := by
    have m:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using m) A.temp
  constructor
  · apply execute_native A input sources D G j base live B portsAt sw v old fresh headerBound resident fits
      mapCount mapRoom (fun _ frame=>footprint.stable frame) source
    · intro m frame
      apply privatePage_stable A
      change m ptr=input ptr
      rw [frame ptr cursorMap]
      change beforePort A P₀ input true (cap A true) ptr=input ptr
      rw [beforePort_away A P₀ input true (cap A true) ptr le_rfl]
      · apply fill_away
        rw [header_size]
        dsimp only [ptr]
        omega
      · intro q i hi
        have bounds:=aperture A q i hi
        have wid:=fits q i hi
        change ptr<srcBase A q i ∨ srcBase A q i+(physicalWidth A input q i).val≤ptr
        dsimp only [ptr]
        omega
    · intro m frame x
      obtain ⟨head,pic⟩:=tables m frame
      have rc : portsEnd A≤(P₀).gatherBase ∨ (P₀).gatherBase+(P₀).gatherCount≤A.temp := by
        change portsEnd A≤ mapBase ∨ mapBase+(partyMapCount A input).val≤A.temp
        rwa [mapCount]
      apply native_gatherFits A input sources D G j base live B portsAt sw v old fresh m pic nst est head
        positive resident.le headerBound rc _ outFit inFit digit scalar x
      change agreesOutside mapBase (mapBase+(partyMapCount A input).val) m _
      rwa [mapCount]
    · exact fun m frame=>(tables m frame).2
  · intro x
    have live : mapBase≤ mapBase+x.val ∧ mapBase+x.val< mapBase+pinCount :=
      ⟨Nat.le_add_right _ _,Nat.add_lt_add_left x.isLt _⟩
    change fillSegment mapBase (partyMapCount A input).val mapWords _ (mapBase+x.val)=_
    simp only [fillSegment,mapCount,ite_eq_left live,gatheredWord,Nat.add_sub_cancel_left,dite_eq_left x.isLt]

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr HistoryGatherBody HistoryGeometryPointer
open Diagonal Diagonal.PhysicalStage Computability.VPVNP.Compression Diagonal.CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open LinearAlgebra.SpectralBooks Diagonal.MotifKernel Diagonal.HistoryContraction BitLayout
open scoped Classical Fin.NatCast
noncomputable section
set_option maxRecDepth 8192
set_option quotPrecheck false
open private rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
open private selectedSiteDecidableEq from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply
attribute [local instance 2000] selectedSiteDecidableEq

variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
  (A : PhysicalStage.State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "P" => shrinkRecordPacking s rem A
local notation "N" => Fintype.card (B).Base
local notation "δ" => (2^s : ℕ)
local notation "k" => (2*δ+1 : ℕ)
local notation "hc" => palette_two s
local notation "good" => rawConditions s rem B
local notation "shrinkGeometry" => shrinkStage s D
private abbrev shrinkGatherDims (s D rem : ℕ) (A : PhysicalStage.State (2^s) (shrinkCharge s+rem)) :=
  dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base) (CompressorPacking.tagBits (2^s)) rem
local notation "X" => shrinkGatherDims s D rem A
local notation "pad" => PhysicalShrink.padding k δ D
local notation "prior" => shrinkRecordWidth s rem A
local notation "issued" => shrinkIssuedWords T s D rem hD small A
local notation "raw" => Demand.key P (baseNat (B).order)
local notation "num" => motifNumbers P raw hc
variable {W K h p : ℕ} {cur : Word W} {boot published : Memory W} {c : Cursor}
local notation "ptrs" => pointers K c X
variable (branch : Fin (shrinkBinary T s D rem hD small A).rules.count)
  (z : ShrinkOutput (K:=K) T s D rem hD small A cur boot c branch published)
  (space : CursorSpace cur boot c K (shrinkGatherDims s D rem A)) (caps : ShrinkOldCaps s rem W)
  (extra : ShrinkOutputCaps s D (Fintype.card (shrinkRecordState s rem A).Base) W)
  (top : ℕ) (size : ∀ m j,shrinkIssuedWords T s D rem hD small A branch m j≤top) (bound : top<2^W)
  (L : HistoryGatherBody.Layout) (mode : L.mode=.shrink (shrinkStage s D)) (scratch : Memory W)
  (frame : Resident.GeometryFrame (shrinkGatherDims s D rem A) (pointers K c (shrinkGatherDims s D rem A))
    published scratch)
local notation "sel" => HistoryGatherBody.selected L scratch
variable (kernel : (scratch (HistoryGatherBody.selected L scratch).kernel.val).val=
    (pointers K c (shrinkGatherDims s D rem A)).ownHeader)
  (m : (shrinkRecordPacking s rem A).Motif) (u : Fin 6)
  (row : scratch (HistoryGatherBody.selected L scratch).incident.val=
    (Demand.key (shrinkRecordPacking s rem A) (baseNat (shrinkRecordState s rem A).order) m.val:Word W))
  (party : L.party.party=u.val) (j : ℕ)
local notation "lay" => ShrinkMotif.chooseWidths (issued branch)
local notation "G" => Resident.successor («pad»:=pad) shrinkGeometry P (B).order (shrinkPieceBound s D) lay hc good z.tagPos
local notation "regs" q:arg b:arg => sourceRegisters L scratch q j (b:Word W)

local notation "motifRow" => (shrinkRecordOrder s rem A m).val

private theorem shrink_width_room {x : Dimensions} (report : CursorSpace cur boot c K x)
    (q : Bool) (row e : ℕ) (hr : row < x.motifs) (he : e < (if q then 8 else 2)) :
    (if q then (pointers K c x).supply else (pointers K c x).demands) +
      ((if q then 8 else 2) * row + e) < 2^W := by
  obtain ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9⟩ := report.allocated
  have stop := report.end_lt
  cases q <;> simp only [Bool.false_eq_true, ite_false, ite_true] at he ⊢ <;> omega

set_option maxHeartbeats 800000 in
include z frame kernel in
theorem shrink_issued_address (q : Bool) (e : ℕ)
    (stride : L.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (hist : (wordAt scratch (sel).incident 1).val=c.dense+motifRow*K)
    (port : HistoryGatherBody.portCode L scratch q j=(e:Word W))
    (edge : e<(if q then 8 else 2)) :
    issuedCell L scratch q j=(if q then (ptrs).supply else (ptrs).demands)+((if q then 8 else 2)*motifRow+e) := by
  let I:=z.reopenAt scratch frame (sel).kernel kernel
  have dense : c.dense<2^W := by
    have := (wordAt scratch (sel).incident 1).isLt
    omega
  have denseWord : wordAt scratch (scratch (sel).kernel.val) 1=(c.dense:Word W) := I.hdr.native 1
  have pos : 0 < L.histogramStride := stride.symm ▸ positive
  have span : L.histogramStride < 2^W := stride.symm ▸ strideFit
  refine HistoryGatherBody.shrink_address (W := W) L scratch q j motifRow e c.dense
    (if q then (ptrs).supply else (ptrs).demands) pos span ?_ ?_ port ?_ ?_
  · exact stride.symm ▸ hist
  · rw [denseWord,Fin.val_cast_of_lt dense]
  · cases q with
    | false => exact I.hdr.native 8
    | true => exact I.hdr.native 3
  · exact shrink_width_room (x := X) z.cursor q motifRow e (shrinkRecordOrder s rem A m).isLt edge

include z frame kernel mode in
private theorem shrink_width_cell (q : Bool) (e : ℕ) (enable : portActive L scratch q j)
    (stride : L.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (hist : (wordAt scratch (sel).incident 1).val=c.dense+motifRow*K)
    (port : HistoryGatherBody.portCode L scratch q j=(e:Word W))
    (edge : e<(if q then 8 else 2)) :
    physicalWidth L scratch q j=
      scratch ((if q then (ptrs).supply else (ptrs).demands)+((if q then 8 else 2)*motifRow+e)) := by
  simp only [physicalWidth,ite_eq_left enable,mode]
  exact congrArg scratch (shrink_issued_address T s D rem hD small A branch z L scratch frame kernel m j q e
    stride positive strideFit hist port edge)

include z frame kernel mode in
/-- Demand-port widths are the persistent cells written by the actual old-graph scan. -/
theorem shrink_demand_width_at (e : Fin 2) (enable : portActive L scratch false j)
    (stride : L.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (hist : (wordAt scratch (sel).incident 1).val=c.dense+motifRow*K)
    (port : HistoryGatherBody.portCode L scratch false j=(e.val:Word W))
    (keep : scratch ((ptrs).demands+motifRow*2+e.val)=published ((ptrs).demands+motifRow*2+e.val)) :
    (physicalWidth L scratch false j).val=demandWidth P prior num m e := by
  have word:=shrink_width_cell T s D rem hD small A branch z L mode scratch frame kernel m j false e.val
    enable stride positive strideFit hist port e.isLt
  rw [word]
  change (scratch ((ptrs).demands+(2*motifRow+e.val))).val=_
  rw [←Nat.add_assoc,Nat.mul_comm 2,keep]
  exact z.demandWords m e

include z frame kernel mode in
/-- Supply-port widths are the issued split-slot cells of the admitted row. -/
theorem shrink_supply_width_at (e : Fin 8) (enable : portActive L scratch true j)
    (stride : L.histogramStride=K) (positive : 0<K) (strideFit : K<2^W)
    (hist : (wordAt scratch (sel).incident 1).val=c.dense+motifRow*K)
    (port : HistoryGatherBody.portCode L scratch true j=(e.val:Word W)) (fit : issued branch m e<2^W) :
    (physicalWidth L scratch true j).val=issued branch m e := by
  have word:=shrink_width_cell T s D rem hD small A branch z L mode scratch frame kernel m j true e.val
    enable stride positive strideFit hist port e.isLt
  have I:=z.reopenAt scratch frame (sel).kernel kernel
  rw [word]
  change (scratch ((ptrs).supply+(8*motifRow+e.val))).val=_
  rw [←Nat.add_assoc,Nat.mul_comm 8]
  have stored : scratch ((ptrs).supply+motifRow*8+e.val) = (issued branch m e : Word W) :=
    I.issuedRows m e
  exact (congrArg Fin.val stored).trans (Fin.val_cast_of_lt fit)

open private selected_bundle_positive from OAI.ThreeFlat.Diagonal.ShrinkSelectedGeometry

private theorem shrink_word {S : Graph.Stage} {L : HistoryGatherBody.Layout} {scratch : Memory W}
    (mode : L.mode=.shrink S) (q : Bool) (port b : ℕ) (loc : Fin 4→ℕ) (target : BitSource h p)
    (fields : ∀ i : Fin 4,
      (((BitOrigins.lookup S q (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit i.val) : Formula 13).compile
        (fun _=>(0:Fin 1))).eval (fun _=>0) scratch (sourceRegisters L scratch q port (b:Word W)))=
        (loc i:Word W))
    (fits : ReadFits scratch (sourceRegisters L scratch q port (b:Word W)) loc)
    (meaning : HistoryScopeAddress.Read (layoutOf (sourceRegisters L scratch q port (b:Word W)))
      (fun x=>(scratch x).val) loc target) :
    (geometryTerm W L q).eval (fun _=>0) scratch (sourceRegisters L scratch q port (b:Word W)) =
      (sourceAddress target : Word W) ∧
    ∀ (ptr : Word W), ptr.val=srcBase L q port+b →
      (sourceTerm W L q port).eval Fin.elim0 scratch (fun _=>ptr)=(sourceAddress target:Word W) := by
  have closed (i : Fin 4) :
      (HeaderScan.closed (BitOrigins.lookup S q (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5)
        (.lit i.val) : Formula 13)).eval Fin.elim0 scratch (sourceRegisters L scratch q port (b:Word W))=
        (loc i:Word W) := by
    simpa only [HeaderScan.eval_closed,Formula.eval_compile,Function.comp_def] using fields i
  refine ⟨?_,?_⟩
  · rw [geometryTerm,mode]
    exact read_shrink S q scratch _ loc target closed fits meaning
  · intro ptr key
    exact HistoryGatherBody.shrink_source L scratch q port b ptr S mode key loc target closed fits meaning

include z space caps extra size bound frame kernel row party mode in
/-- A demand from the selected, persisted shrink is read at the actual gather's
kernel, incident, catalogue port, party and bit registers. -/
theorem shrink_demand_at (port : demandGraph.Port u) (bit : Fin (demandWidth P prior num m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch false j).val=port.val.1.val) (wide : A.maxWidth<2^W)
    (total : thickWidth P prior ((P).bundle m)<2^W) (target : BitSource h p) :
    let site:=partySite P lay m u
    let req:=ChildSend.request P raw prior (selected_bundle_positive s) num m port.val.2 port.val.1 bit
    let placed:=ChildSend.at_party raw (selected_bundle_positive s) num (motifNumbers_bundle P raw hc) lay m (v:=site) rfl port bit
    let loc:=ChildSend.words P prior lay site req placed
    ReadFits scratch (regs false bit.val) loc →
    HistoryScopeAddress.Read (layoutOf (regs false bit.val)) (fun x=>(scratch x).val) loc target →
    (geometryTerm W L false).eval (fun _=>0) scratch (regs false bit.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase L false j+bit.val →
      (sourceTerm W L false j).eval Fin.elim0 scratch (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro site req placed loc fits meaning
  apply shrink_word mode false j bit.val loc target _ fits meaning
  intro field
  have pu : L.party.party<2^W := by rw [party]; have := u.isLt; have := caps.eight; omega
  have rp : ((regs false bit.val) 3).val=u.val := by
    change (L.party.party:Word W).val=u.val
    rw [Fin.val_cast_of_lt pu,party]
  exact ShrinkOutput.demandBitAt T s D rem hD small A branch z space caps extra top size bound
    scratch frame (regs false bit.val) kernel m u port bit field row rp code rfl wide total

include z space caps extra size bound frame kernel row party mode in
/-- Issued and absorbed supply bits use the native split-piece/hidden selector of
the same shrink output, in the scratch memory currently consumed by the port scan. -/
theorem shrink_supply_at (port : supplyGraph.Port u) (bit : Fin (issued branch m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch true j).val=port.val.1.val) (target : BitSource h p) :
    let loc:=PhysicalStage.supplyField T s D rem hD small A branch G m u port.val.1 bit
    ReadFits scratch (regs true bit.val) loc →
    HistoryScopeAddress.Read (layoutOf (regs true bit.val)) (fun x=>(scratch x).val) loc target →
    (geometryTerm W L true).eval (fun _=>0) scratch (regs true bit.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase L true j+bit.val →
      (sourceTerm W L true j).eval Fin.elim0 scratch (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro loc fits meaning
  apply shrink_word mode true j bit.val loc target _ fits meaning
  intro field
  have pu : L.party.party<2^W := by rw [party]; have := u.isLt; have := caps.eight; omega
  have rp : ((regs true bit.val) 3).val=u.val := by
    change (L.party.party:Word W).val=u.val
    rw [Fin.val_cast_of_lt pu,party]
  exact ShrinkOutput.supplyBitAt T s D rem hD small A branch z space caps extra top size bound scratch
    frame (regs true bit.val) kernel m u port bit field row rp code rfl

include z space caps extra size bound frame kernel row party mode in
/-- The selected old source is the exact `oldPinSource` of the local party. The five
resident words below are its child ID, half-table, child prefix and half prefix. -/
theorem shrink_demand_oldPin {Pins E : Type} [Fintype E]
    (old : WordLayout (oldGraph P) prior Pins)
    {next : PortGraph (Site (B).Base (BitWord (CompressorPacking.tagBits δ)) (BitWord rem)) E} {width : E→ℕ}
    (fresh : WordLayout next width Pins) (h : ℕ) (port : demandGraph.Port u)
    (bit : Fin (demandWidth P prior num m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch false j).val=port.val.1.val) (wide : A.maxWidth<2^W)
    (total : thickWidth P prior ((P).bundle m)<2^W) (child header table : ℕ) :
    let site := partySite P lay m u
    let req := ChildSend.request P raw prior (selected_bundle_positive s) num m port.val.2 port.val.1 bit
    let placed := ChildSend.at_party raw (selected_bundle_positive s) num (motifNumbers_bundle P raw hc) lay m
      (v:=site) rfl port bit
    let i := ChildSend.ownedChild lay site req placed
    let a := ChildSend.ownedPort lay site req placed
    let loc := ChildSend.words P prior lay site req placed
    let H := layoutOf (regs false bit.val)
    let count := fun _ : Site (B).Base (BitWord (CompressorPacking.tagBits δ)) (BitWord rem) => δ*2^k
    let ord := Owner.childOrder P lay
    let target := oldPinSource (h:=h) P prior raw (selected_bundle_positive s) num lay site
      (WordLayout.oldPin old fresh ((P).placement lay) count ord site) m u port bit
    H.childIDs+loc 1<2^W ∧ H.nodes+(8*child+6)<2^W ∧ header+1<2^W ∧
      table+(4*loc 2+3)<2^W ∧ H.childStarts+loc 1<2^W →
    (scratch (H.childIDs+loc 1)).val=child → (scratch (H.nodes+(8*child+6))).val=header →
    (scratch (header+1)).val=table →
    (scratch (H.childStarts+loc 1)).val=WordLayout.childStart old ((P).placement lay) count ord site i →
    (scratch (table+(4*loc 2+3))).val=old.ports.start i.val a →
    (geometryTerm W L false).eval (fun _=>0) scratch (regs false bit.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase L false j+bit.val →
      (sourceTerm W L false j).eval Fin.elim0 scratch (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro site req placed i a loc H count ord target extent node halves rows start first
  have tag : loc 0=1 := rfl
  have fits : ReadFits scratch (regs false bit.val) loc := by
    apply readFits_of_addresses _ _ _ (by omega) (lt_trans (by decide : 3<8) caps.eight)
    · intro _
      rw [←rows,←halves,←node] at extent
      exact extent
    · intro bad
      omega
    · intro bad
      omega
  apply shrink_demand_at T s D rem hD small A branch z space caps extra top size bound L mode scratch
    frame kernel m u row party j port bit code wide total target fits
  exact HistoryScopeAddress.Read.oldShrinkRequest P raw prior (selected_bundle_positive s) num (motifNumbers_bundle P raw hc)
    lay site old fresh m (party:=u) rfl port bit H (fun x=>(scratch x).val) child header table
    node halves rows start first

open Diagonal.MotifOuterTerms
open scoped BigOperators
open private copiesPositive from OAI.ThreeFlat.Diagonal.ShrinkSelectedSupply

local notation "chosen" => PhysicalShrink.widths T P prior (shrinkRecordCode s rem A) hc
local notation "many" => PhysicalShrink.r T P prior (shrinkRecordCode s rem A) hc
local notation "tiles" => PhysicalShrink.tile T P prior (shrinkRecordCode s rem A) hc
local notation "hist" => shrinkIssuedBranch T s D rem hD small A branch
local notation "edgeOrd" => edgeOrder P (baseNat (B).order) (tagOrdinal (CompressorPacking.tagBits δ)).toEmbedding
  (shrinkGeometry).pieces (shrinkGeometry).pieceRadix (shrinkPieceBound s D)
local notation "padding" => tagPadding (V:=(B).Base) (L:=BitWord rem) (tagOne z.tagPos) (tagOne_ne z.tagPos) pad
local notation "outWidth" => outputWidth P chosen many tiles hist binary_neg good lay (shrinkGeometry).pieces edgeOrd hc pad
local notation "freshG" => outGraph P binary_neg good lay (shrinkGeometry).pieces edgeOrd hc pad padding
local notation "Vtx" => Site (B).Base (BitWord (CompressorPacking.tagBits δ)) (BitWord rem)
local notation "count" => (fun _ : Vtx => δ*2^k)
local notation "ord" => Owner.childOrder P lay
local notation "own" => (P).placement lay

private theorem crossingReadFits {fields : Fin 4→ℕ} {number offset : ℕ}
    (printed : fields=![2,0,number,offset]) (mem : Memory W) (vs : Fin 13→Word W) (table : ℕ)
    (enough : 3<2^W) (headerFit : (layoutOf vs).newHalves+1<2^W)
    (headerWord : (mem ((layoutOf vs).newHalves+1)).val=table)
    (slotFit : table+(4*number+3)<2^W) : ReadFits mem vs fields := by
  subst fields
  apply readFits_of_addresses mem vs ![2,0,number,offset] (by change (2 : ℕ)≤3; decide) enough
  · intro bad; change (2 : ℕ)=1 at bad; omega
  · intro _
    change (layoutOf vs).newHalves+1<2^W ∧ (mem ((layoutOf vs).newHalves+1)).val+(4*number+3)<2^W
    rw [headerWord]
    exact ⟨headerFit,slotFit⟩
  · intro bad; change (2 : ℕ)=3 at bad; omega

private theorem absorbedReadFits {fields : Fin 4→ℕ} {edge offset : ℕ}
    (printed : fields=![3,edge,offset,0]) (mem : Memory W) (vs : Fin 13→Word W) (enough : 3<2^W)
    (slotFit : (layoutOf vs).privateStarts+edge<2^W) : ReadFits mem vs fields := by
  subst fields
  apply readFits_of_addresses mem vs ![3,edge,offset,0] (by change (3 : ℕ)≤3; decide) enough
  · intro bad; change (3 : ℕ)=1 at bad; omega
  · intro bad; change (3 : ℕ)=2 at bad; omega
  · intro _; exact slotFit

open Diagonal.MotifBinaryPacking in
private theorem supplyReadFits {colors degree : ℕ} {Vertex Group Tag Label : Type}
    [AddCommGroup Group] [AddCommGroup Tag] [AddCommGroup Label]
    [Fintype Vertex] [Fintype Group] [Fintype Tag] [Fintype Label]
    (packing : PackingData Vertex Group Tag Label degree colors)
    (baseWidth : packing.Motif → Fin 2 → ℕ) (repeats : packing.Motif → ℕ)
    (tile : ∀ motif, FixedMotifTile demandGraph supplyGraph (baseWidth motif) F)
    (history : Histories packing baseWidth repeats tile) (negTag : ∀ a : Tag, -a = a)
    (conditions : TagConditions packing.slots (shift packing) packing.offset) (layoutSide : Bool)
    (copies : Fin 4 → ℕ) (copiesPos : ∀ i, 0 < copies i) (orderMap : ShrinkEdge packing copies ↪ ℕ)
    (colorsTwo : 2 ≤ colors) (extraDegree : ℕ) (extraSlots : LiftedSlots (Vertex × Tag) extraDegree Label)
    (v : Site Vertex Tag Label) (motif : packing.Motif)
    (graph : LiftedSlots (Vertex × Tag) (usedDegree copies colors degree + extraDegree) Label)
    (partyAt : {u // partySite packing layoutSide motif u = v}) (q : supplyGraph.Port partyAt.val)
    (bit : Fin (historyWidth packing baseWidth repeats tile history motif q.val.1))
    (mem : Memory W) (vs : Fin 13 → Word W) (table : ℕ) (enough : 3 < 2^W)
    (headerFit : (layoutOf vs).newHalves+1 < 2^W)
    (halfFit : ∀ a : (outGraph packing negTag conditions layoutSide copies orderMap colorsTwo
      extraDegree extraSlots).Port v, table+(4*SupplySend.halfOrdinal graph a.val.1 a.val.2+3) < 2^W)
    (privateFit : (layoutOf vs).privateStarts+q.val.1.val < 2^W)
    (rows : (mem ((layoutOf vs).newHalves+1)).val = table) :
    ReadFits mem vs (SupplySend.fieldValues packing negTag conditions layoutSide copies copiesPos
      orderMap colorsTwo extraDegree (historyWidth packing baseWidth repeats tile history) graph
      motif partyAt.val q.val.1 bit) := by
  by_cases cross : wireOwner supplyGraph.tail supplyGraph.head (partySite packing layoutSide motif) q.val.1 = none
  · let req := SupplySend.request packing baseWidth repeats tile history negTag conditions layoutSide
      copies copiesPos orderMap colorsTwo extraDegree extraSlots v motif (PrivateOrder.onSide partyAt q cross) bit
    have printed := SupplySend.fieldValues_request packing baseWidth repeats tile history negTag conditions
      layoutSide copies copiesPos orderMap colorsTwo extraDegree extraSlots graph v motif partyAt q cross bit
    exact crossingReadFits printed mem vs table enough headerFit rows (halfFit req.1)
  · exact absorbedReadFits (dite_eq_right cross) mem vs enough privateFit

set_option maxHeartbeats 1600000 in
include z space caps extra size bound frame kernel row party mode in
/-- The supply row is the selected occupied-tree source on the issued split edge,
or its true private bit when both ends belong to this site. -/
theorem shrink_supply_partySource {Pins : Type} (v : Vtx) (atSite : partySite P lay m u=v)
    (O : WordLayout (oldGraph P) prior Pins) (B' : WordLayout freshG outWidth Pins)
    (port : supplyGraph.Port u) (bit : Fin (issued branch m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch true j).val=port.val.1.val) (table : ℕ) :
    let place := partySite P lay m
    let active := fun e => wireOwner supplyGraph.tail supplyGraph.head place e=some v
    let priv := HistogramTileNetwork.order («k»:=(tiles m).bits) ShrinkMotif.supply place v (tiles m).output
      (hist m) (HistoryMaskOrder.order active)
    let pin := WordLayout.newPin O B' own count ord v
    let cross := crossingPin P chosen many tiles hist binary_neg good lay (shrinkGeometry).pieces (copiesPositive s D hD small)
      edgeOrd hc pad padding v pin m
    let pu : {i // place i=v} := ⟨u,atSite⟩
    let target := priv.partySource cross pu port bit
    let H := layoutOf (regs true bit.val)
    H.publicPins=WordLayout.argSize O B' own count ord v → H.oldBits=WordLayout.prior O own count ord v →
    H.newHalves+1<2^W → (∀ a : (freshG).Port v, table+(4*SupplySend.halfOrdinal G a.val.1 a.val.2+3)<2^W) →
    H.privateStarts+port.val.1.val<2^W →
    (scratch (H.newHalves+1)).val=table →
    (∀ a : (freshG).Port v, (scratch (table+(4*SupplySend.halfOrdinal G a.val.1 a.val.2+3))).val=
      B'.ports.start v a) →
    (scratch (H.privateStarts+port.val.1.val)).val=
      (∑ e ∈ Finset.univ.filter (fun e=>active e ∧ e<port.val.1),issued branch m e) →
    (geometryTerm W L true).eval (fun _=>0) scratch (regs true bit.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase L true j+bit.val →
      (sourceTerm W L true j).eval Fin.elim0 scratch (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro place active priv pin cross pu target H publicBits oldBits headerFit halfFit privateFit rows half privateStartWord
  have enough := lt_trans (by decide : (3 : ℕ)<8) caps.eight
  have fit := supplyReadFits P chosen many tiles hist binary_neg good lay (shrinkGeometry).pieces
    (copiesPositive s D hD small) edgeOrd hc pad padding v m G pu port bit
    scratch (regs true bit.val) table enough headerFit (fun a => halfFit a) privateFit rows
  have meaning := HistoryScopeAddress.Read.supplyField (Pins:=Pins) T s D rem hD small A branch z.tagPos
    v m O B' pu port bit H (fun x => (scratch x).val) table publicBits oldBits rows
    (fun a => half a) privateStartWord
  apply shrink_supply_at T s D rem hD small A branch z space caps extra top size bound L mode scratch
    frame kernel m u row party j port bit code target fit
  exact meaning


/-- Literal child-directory and predecessor-half values required for a selected old bit.
The child, header and table addresses come directly from the current physical memory. -/
def DemandCells {Pins E : Type} [Fintype E] (old : WordLayout (oldGraph P) prior Pins)
    {next : PortGraph Vtx E} {width : E→ℕ} (_fresh : WordLayout next width Pins)
    (v : Vtx) (owned : partySite P lay m u=v) (port : demandGraph.Port u)
    (bit : Fin (demandWidth P prior num m port.val.1)) : Prop :=
  let req:=ChildSend.request P raw prior (selected_bundle_positive s) num m port.val.2 port.val.1 bit
  let placed:=ChildSend.at_party raw (selected_bundle_positive s) num (motifNumbers_bundle P raw hc) lay m (v:=v) owned port bit
  let i:=ChildSend.ownedChild lay v req placed
  let a:=ChildSend.ownedPort lay v req placed
  let loc:=ChildSend.words P prior lay v req placed
  let H:=layoutOf (regs false bit.val)
  let child:=(scratch (H.childIDs+loc 1)).val
  let header:=(scratch (H.nodes+(8*child+6))).val
  let table:=(scratch (header+1)).val
  (H.childIDs+loc 1<2^W ∧ H.nodes+(8*child+6)<2^W ∧ header+1<2^W ∧
    table+(4*loc 2+3)<2^W ∧ H.childStarts+loc 1<2^W) ∧
    (scratch (H.childStarts+loc 1)).val=WordLayout.childStart old ((P).placement lay) count ord v i ∧
    (scratch (table+(4*loc 2+3))).val=old.ports.start i.val a

include z caps extra size bound frame kernel row party mode in
theorem demand_of_cells {Pins E : Type} [Fintype E] (old : WordLayout (oldGraph P) prior Pins)
    {next : PortGraph Vtx E} {width : E→ℕ} (fresh : WordLayout next width Pins)
    (v : Vtx) (atSite : partySite P lay m u=v) (h : ℕ) (port : demandGraph.Port u)
    (bit : Fin (demandWidth P prior num m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch false j).val=port.val.1.val) (wide : A.maxWidth<2^W)
    (total : thickWidth P prior ((P).bundle m)<2^W)
    (cells : DemandCells T s D rem hD small A branch L scratch m u j old fresh v atSite port bit) :
    (geometryTerm W L false).eval (fun _=>0) scratch (regs false bit.val)=
      (sourceAddress (oldPinSource (h:=h) P prior raw (selected_bundle_positive s) num lay v
        (WordLayout.oldPin old fresh ((P).placement lay) count ord v) m u port bit):Word W) := by
  subst v
  exact (shrink_demand_oldPin T s D rem hD small A branch z z.cursor caps extra top size bound L mode scratch
    frame kernel m u row party j old fresh h port bit code wide total _ _ _ cells.1 rfl rfl rfl cells.2.1 cells.2.2).1

/-- Literal successor half-table, absorbed-edge prefix, and bit lengths for this port. -/
def SupplyCells {Pins : Type} (O : WordLayout (oldGraph P) prior Pins)
    (B' : WordLayout freshG outWidth Pins) (v : Vtx) (port : supplyGraph.Port u)
    (bit : Fin (issued branch m port.val.1)) : Prop :=
  let H:=layoutOf (regs true bit.val)
  let table:=(scratch (H.newHalves+1)).val
  let active:=fun e=>wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) e=some v
  H.publicPins=WordLayout.argSize O B' own count ord v ∧ H.oldBits=WordLayout.prior O own count ord v ∧
    H.newHalves+1<2^W ∧ (∀a:(freshG).Port v,table+(4*SupplySend.halfOrdinal G a.val.1 a.val.2+3)<2^W) ∧
    H.privateStarts+port.val.1.val<2^W ∧
    (∀a:(freshG).Port v,(scratch (table+(4*SupplySend.halfOrdinal G a.val.1 a.val.2+3))).val=B'.ports.start v a) ∧
    (scratch (H.privateStarts+port.val.1.val)).val=
      (∑e∈Finset.univ.filter (fun e=>active e ∧ e<port.val.1),issued branch m e)

include z caps extra size bound frame kernel row party mode in
theorem supply_of_cells {Pins : Type} (O : WordLayout (oldGraph P) prior Pins)
    (B' : WordLayout freshG outWidth Pins) (v : Vtx) (atSite : partySite P lay m u=v)
    (port : supplyGraph.Port u) (bit : Fin (issued branch m port.val.1))
    (code : (HistoryGatherBody.portCode L scratch true j).val=port.val.1.val)
    (cells : SupplyCells T s D rem hD small A branch z L scratch m u j O B' v port bit) :
    let place := partySite P lay m
    let active := fun e => wireOwner supplyGraph.tail supplyGraph.head place e=some v
    let priv:=HistogramTileNetwork.order («k»:=(tiles m).bits) ShrinkMotif.supply place v (tiles m).output
      (hist m) (HistoryMaskOrder.order active)
    let cross:=crossingPin P chosen many tiles hist binary_neg good lay (shrinkGeometry).pieces (copiesPositive s D hD small)
      edgeOrd hc pad padding v (WordLayout.newPin O B' own count ord v) m
    (geometryTerm W L true).eval (fun _=>0) scratch (regs true bit.val)=
      (sourceAddress (priv.partySource cross ⟨u,atSite⟩ port bit):Word W) := by
  obtain ⟨publicBits,oldBits,headerFit,halfFit,privateFit,half,prefixBit⟩:=cells
  exact (shrink_supply_partySource T s D rem hD small A branch z z.cursor caps extra top size bound L mode scratch
    frame kernel m u row party j v atSite O B' port bit code _ publicBits oldBits headerFit halfFit privateFit rfl half prefixBit).1

end
end ThreeFlat.RAM.HistoryGatherExecution



namespace ThreeFlat.RAM.HistoryGatherExecution
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan HistoryGatherBody HistoryStageBody.Physical
open Diagonal PhysicalStage
open scoped Classical Fin.NatCast
noncomputable section
variable {F : Type} [Field F] [Fintype F] {W height n p : ℕ}
variable {B : Block F} {G : Grid F} {pre tail : List (Grid F)} {f : Fin n→Fin p→Party F}
variable (A : Layout) (mem : Memory W)
local notation "R" => selected A mem

/-- Numerically indexed genuine catalogue in the retained S38 library. -/
structure ReadPage (P : Party F) (arity page : ℕ) : Prop where
  base : (R).portPage=(page:Word W)
  extent : page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap≤2^W
  kinds : ∀i:Fin 7,(wordAt mem (R).kindPage i.val).val=(P.kind arity).words i
  ports : ∀i,i<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap →
    (mem (page+i)).val=P.port.at A.demandCap A.supplyCap i

def ReadPage.memory {A : Layout} {m : Memory W} {P : Party F} {ar q : ℕ}
    (_ : ReadPage A m P ar q) : Memory W := m

def ReadPage.start {A : Layout} {m : Memory W} {P : Party F} {ar q : ℕ}
    (_ : ReadPage A m P ar q) : ℕ := q

variable {start : ℕ}
local notation "g" => G.family (Mounted.base B height start pre)

theorem read_mounted (M : Mounted B height W start mem) (stage : grids B=pre++G::tail)
    (rows : G.rows=grid f) (i : Fin n) (j : Fin p)
    (kindBase : A.party.kinds=(g).kinds) (portBase : A.catalogue=(g).ports)
    (dem : A.demandCap=G.demand) (sup : A.supplyCap=G.supply) (dig : A.digitCap=G.digits)
    (ps : A.party.parties=p) (atP : A.party.party=j.val) (shape : wordAt mem (R).incident 2=(i.val:Word W))
    (kindRoom : (g).kinds+7*(i.val*p+j.val)+7≤2^W)
    (portRoom : (g).ports+G.stride*(i.val*p+j.val)+G.stride≤2^W)
    (kindFit : ∀k:Fin 7,((f i j).kind (arity B)).words k<2^W)
    (portFit : ∀k:Fin G.stride,(f i j).port.at G.demand G.supply k.val<2^W) :
    ReadPage A mem (f i j) (arity B) ((g).ports+G.stride*(i.val*p+j.val)) := by
  have pair:=Mounted.selected_pages (B:=B) (G:=G) (pre:=pre) (m:=mem) A i j kindBase portBase
    dem sup dig ps atP shape
  have stride : HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap=G.stride := by rw [dem,sup,dig];rfl
  refine ⟨pair.2,by rwa [stride],?_,?_⟩
  · intro k
    have memAt:=Mounted.kindAt M stage rows i j k
    have low:=k.isLt
    unfold wordAt
    rw [pair.1,←Nat.cast_add,Fin.val_cast_of_lt (by omega),memAt,Fin.val_cast_of_lt (kindFit k)]
  · intro k hk
    rw [stride] at hk
    have here:=Mounted.portAt M stage rows i j ⟨k,hk⟩
    rw [here,Fin.val_cast_of_lt (portFit ⟨k,hk⟩),dem,sup]

variable {A mem}
omit [Field F] in
theorem ReadPage.word {P : Party F} {a page : ℕ} (R0 : ReadPage A mem P a page) (i : ℕ)
    (hi:i<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap) :
    (wordAt mem (selected A mem).portPage i).val=P.port.at A.demandCap A.supplyCap i := by
  unfold wordAt
  rw [R0.base,←Nat.cast_add,Fin.val_cast_of_lt (by have:=R0.extent;omega)]
  exact R0.ports i hi

omit [Field F] in
/-- The retained header words and the immutable catalogue stay live at every
gather iteration if their numerical addresses avoid both scratch ranges. -/
theorem ReadPage.retain {P : Party F} {a page : ℕ} {input scratch : Memory W}
    (page0 : ReadPage A input P a page) (image : Plan W)
    (header : A.temp+(fields (W:=W) A).length≤A.temp+A.party.V)
    (fits : ∀q i,i<cap A q → image.width q i≤A.party.V)
    (frame : agreesOutside image.gatherBase (image.gatherBase+image.gatherCount)
      scratch (beforeGather A image input))
    (keep : ∀addr,let old:=selected A input
      addr=(A.nodePorts.cursor:Word W).val ∨ addr=(nodeWord A input+5).val ∨ addr=(old.kernel+4).val ∨
      addr=(old.incident+2).val ∨ addr=(old.incident+3).val ∨
      (∃i:Fin 7,addr=(old.kindPage+(i.val:Word W)).val) ∨
      (page≤addr ∧ addr<page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap) →
      (addr<A.temp ∨ portsEnd A≤addr) ∧ (addr< image.gatherBase ∨ image.gatherBase+image.gatherCount≤addr)) :
    ReadPage A scratch P a page ∧ wordAt scratch (selected A scratch).incident 3=wordAt input (selected A input).incident 3 := by
  have vEnd : A.temp+A.party.V≤portsEnd A := by
    have m:=Nat.mul_le_mul_right A.party.V (show 1≤1+A.demandCap+A.supplyCap by omega)
    exact Nat.add_le_add_left (by simpa only [one_mul] using m) A.temp
  have save (addr : ℕ) (h : (addr<A.temp ∨ portsEnd A≤addr) ∧
      (addr< image.gatherBase ∨ image.gatherBase+image.gatherCount≤addr)) : scratch addr=input addr := by
    have ports : ∀ q i, i<cap A q → addr<srcBase A q i ∨ srcBase A q i+image.width q i≤addr := by
      intro q i hi
      have ap:=aperture A q i hi
      have width:=fits q i hi
      rcases h.1 with z|z <;> omega
    exact (frame _ h.2).trans ((beforePort_away A image input true A.supplyCap addr le_rfl ports).trans
      (fill_away A.temp (fields (W:=W) A).length addr image.headerWord input
        (by rcases h.1 with z|z <;> omega)))
  have sel:=selected_rows_same A (save _ (keep _ (.inl rfl))) (save _ (keep _ (.inr (.inl rfl))))
    (save _ (keep _ (.inr (.inr (.inl rfl))))) (save _ (keep _ (.inr (.inr (.inr (.inl rfl))))))
  refine ⟨⟨sel.2.2.trans page0.base,page0.extent,?_,?_⟩,?_⟩
  · intro i
    unfold wordAt
    rw [sel.2.1,save _ (keep _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨i,rfl⟩)))))))]
    exact page0.kinds i
  · intro i hi
    rw [save _ (keep _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega,by omega⟩)))))))]
    exact page0.ports i hi
  · unfold wordAt
    rw [sel.1]
    exact save _ (keep _ (.inr (.inr (.inr (.inr (.inl rfl))))))

omit [Field F] in
/-- All seven layout parameters of the final native map lookup. -/
theorem ReadPage.layout {P : Party F} {a page copies : ℕ} (R0 : ReadPage A mem P a page)
    (count : (wordAt mem (selected A mem).incident 3).val=copies)
    (header : page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap<2^W) :
    let T:=gatherLayout A mem
    T.copies=copies ∧ T.selectorBits=P.codeBits ∧ T.ports=P.supplies ∧ T.headerBits=P.header ∧
      T.tileBits=P.maxDigit ∧ T.anchor=P.port.anchor ∧
      T.headerTable=page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap := by
  have kind (i : Fin 7):=R0.kinds i
  have anch:=R0.word 2 (by simp [HistoryPortCatalogue.stride];omega)
  dsimp only [HistoryGatherBody.gatherLayout]
  refine ⟨count,kind 2,kind 0,kind 3,kind 4,?_,?_⟩
  · simpa [HistoryPortCatalogue.Page.at] using anch
  · rw [R0.base,←Nat.cast_add,Fin.val_cast_of_lt header]

omit [Field F] in
/-- Each selected input-port slot is enabled and its ROM word is the actual edge code. -/
theorem ReadPage.demand {P : Party F} {a page : ℕ} (R0 : ReadPage A mem P a page)
    (room : P.demands≤A.demandCap) (u : Fin P.demands) (active : partyActive A mem) :
    portActive A mem false u.val ∧ (HistoryGatherBody.portCode A mem false u.val).val=P.port.demand u := by
  have extent:=R0.extent
  dsimp only [HistoryPortCatalogue.stride] at extent
  have pos:=u.isLt.trans_le room
  have len:=R0.word 0 (by simp [HistoryPortCatalogue.stride])
  have n : (wordAt mem (selected A mem).portPage 0).val=P.demands := by
    simpa [HistoryPortCatalogue.Page.at] using len
  refine ⟨(portActive_iff A mem false u.val (by omega)).2 ⟨active,?_⟩,?_⟩
  · change u.val< (wordAt mem (selected A mem).portPage 0).val
    rw [n];exact u.isLt
  · exact (R0.word (HistoryPortCatalogue.demandBase+2*u.val) (by dsimp only [HistoryPortCatalogue.stride,HistoryPortCatalogue.demandBase];omega)).trans
      (HistoryPortCatalogue.demand_row P.port room u).1

omit [Field F] in
/-- Each selected supply slot is enabled and reads the second port directory. -/
theorem ReadPage.supply {P : Party F} {a page : ℕ} (R0 : ReadPage A mem P a page)
    (room : P.supplies≤A.supplyCap) (u : Fin P.supplies) (active : partyActive A mem) :
    portActive A mem true u.val ∧ (HistoryGatherBody.portCode A mem true u.val).val=P.port.supply u := by
  have extent:=R0.extent
  dsimp only [HistoryPortCatalogue.stride] at extent
  have pos:=u.isLt.trans_le room
  have len:=R0.word 1 (by dsimp only [HistoryPortCatalogue.stride];omega)
  have n : (wordAt mem (selected A mem).portPage 1).val=P.supplies := by
    simpa [HistoryPortCatalogue.Page.at] using len
  refine ⟨(portActive_iff A mem true u.val (by omega)).2 ⟨active,?_⟩,?_⟩
  · change u.val< (wordAt mem (selected A mem).portPage 1).val
    rw [n];exact u.isLt
  · exact (R0.word (HistoryPortCatalogue.supplyBase A.demandCap+u.val) (by dsimp only [HistoryPortCatalogue.stride,HistoryPortCatalogue.supplyBase];omega)).trans
      (HistoryPortCatalogue.supply_row P.port room u)

omit [Field F] in
theorem ReadPage.tile {P : Party F} {a page : ℕ} (R0 : ReadPage A mem P a page)
    (room : P.demands≤A.demandCap) (u : Fin P.demands)
    (active : partyActive A mem) (_fit : u.val<2^W) :
    (tileWidth A mem u.val).val=P.port.baseWidth u := by
  have live:=(R0.demand room u active).1
  have pos:=u.isLt.trans_le room
  have row:=R0.word (HistoryPortCatalogue.demandBase+2*u.val+1)
    (by simp [HistoryPortCatalogue.stride,HistoryPortCatalogue.demandBase];omega)
  change (if portActive A mem false u.val then _ else (0:Word W)).val=_
  rw [ite_eq_left live]
  exact row.trans (HistoryPortCatalogue.demand_row P.port room u).2

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan HistoryGatherBody HistoryStageBody.Physical
open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector Diagonal Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking
open Diagonal.HistogramTileNetwork BitLayout
open scoped Classical BigOperators Fin.NatCast
noncomputable section
variable {F J E S : Type} [Field F] [Fintype F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  {e n r h p W : ℕ}
variable (A : Layout) (input scratch : Memory W) (gathered : ℕ→Word W)
  (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E→ℕ)
  (tile : FixedMotifTile D (ports G) base F)
  (dp : Fin n ≃ D.Port j) (sp : Fin e ≃ (ports G).Port j) (di : Fin n→ℕ) (si : Fin e→ℕ)
  (v : Histogram tile.Alphabet r) (old : (a : D.Port j)→Fin (live a.1.1)→BitSource h p)
  (fresh : (a : (ports G).Port j)→Fin (histWidth tile.output v a.1.1+r*tile.bits)→BitSource h p)
local instance : Nonempty tile.Alphabet := tile.hasLetter
private abbrev admittedTileHeader : HistogramTileNetwork.Header (D.Port j) tile.Alphabet
    (fun a=>base a.1.1) tile.bits n :=
  ⟨dp,tile.encode⟩

local notation "B" => admittedTileHeader D G j base tile dp
local notation "rec" => Party.ofTile D G j base tile dp sp di si
local notation "ss" => typedSources (W:=W) A D G j base live B sp tile.output v old fresh
local notation "P" => nativePlan A input ss gathered

/-- The actual kind and port pages of a finite RAM tile supply the complete
semantic image used by the final gather. Only the graph's logical widths
and the genuine physical copy-count word vary across sites. -/
theorem image_from_pages (page a : ℕ) (initial : ReadPage A input rec a page)
    (later : ReadPage A scratch rec a page)
    (headAddress : page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap<2^W)
    (active : partyActive A input)
    (copies : (wordAt input (selected A input).incident 3).val=r)
    (copies' : (wordAt scratch (selected A scratch).incident 3).val=r)
    (nst : n≤A.demandCap) (est : e≤A.supplyCap) (digitBound : (∑i,base (dp i).1.1)≤A.digitCap)
    (positive : 0<A.party.V) (resident : portsEnd A≤2^W)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (fits : ∀q i,i<cap A q → (physicalWidth A input q i).val≤A.party.V)
    (range : portsEnd A≤(P).gatherBase ∨ (P).gatherBase+(P).gatherCount≤A.temp)
    (frame : agreesOutside (P).gatherBase ((P).gatherBase+(P).gatherCount) scratch (beforeGather A P input))
    (pageClear : let hi:=page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap
      (hi≤A.temp ∨ portsEnd A≤page) ∧
      (hi≤(P).gatherBase ∨ (P).gatherBase+(P).gatherCount≤page))
    (supWidth : ∀u:Fin e,(physicalWidth A input true u.val).val=histWidth tile.output v (sp u).1.1+r*tile.bits)
    (demWidth : ∀u:Fin n,(physicalWidth A input false u.val).val=live (dp u).1.1)
    (oldRoom : ∀q b,sourceAddress (old q b)<2^W)
    (newRoom : ∀q b,sourceAddress (fresh q b)<2^W) :
    HistoryPartyGather.Image (d:=tile.bitCap) D G j base live B sp tile.output v old fresh (gatherLayout A scratch)
      (fun i=>(scratch i).val) := by
  apply native_image A input scratch ss gathered D G j base live B sp tile.output v old fresh
    page di si nst est digitBound positive resident headerBound fits range frame pageClear initial.ports
  · exact later.layout copies' headAddress
  · exact supWidth
  · intro u
    have hr:=supWidth u
    have lim : histWidth tile.output v (sp u).1.1+r*tile.bits<2^W := by rw [←hr];exact (physicalWidth A input true u.val).isLt
    have cod : (wordAt input (selected A input).kindPage 2).val=tile.bits:=initial.kinds 2
    have pay:=payloadWidth_eq A input u.val _ r tile.bits active
      ((Fin.cast_val_eq_self _).symm.trans (congrArg (fun z:ℕ=>(z:Word W)) copies))
      ((Fin.cast_val_eq_self _).symm.trans (congrArg (fun z:ℕ=>(z:Word W)) cod))
      ((Fin.cast_val_eq_self _).symm.trans (congrArg (fun z:ℕ=>(z:Word W)) hr)) lim
    rw [pay,Fin.val_cast_of_lt (by omega)]
  · exact demWidth
  · intro u
    have extent:=initial.extent
    dsimp [HistoryPortCatalogue.stride] at extent
    have fit:=u.isLt.trans_le nst
    exact initial.tile nst u active (by omega)
  · intro i b
    rw [typedSources_demand,Fin.val_cast_of_lt (oldRoom _ _)]
  · intro i b
    rw [typedSources_supply,Fin.val_cast_of_lt (newRoom _ _)]


local notation "mapBase" => gatherMapBase A input
local notation "size" => r*(e*tile.bits)+(r*HistogramTileNetwork.Header.arity B+e*(r*tile.bitCap))
local notation "mapWords" => gatheredWord mapBase
  (fun x : Fin size=>sourceAddress (partyPointer D G j base live B sp tile.output v old fresh x))
local notation "runPlan" => nativePlan A input ss mapWords

private theorem padded_width_zero (a page : ℕ) (initial : ReadPage A input rec a page)
    (q : Bool) (i : ℕ) (fit : i<cap A q) (off : (if q then e else n)≤ i) :
    (physicalWidth A input q i).val=0 := by
  have extent:=initial.extent
  dsimp only [HistoryPortCatalogue.stride] at extent
  have ch : q.toNat<HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap := by
    cases q <;> simp [HistoryPortCatalogue.stride]; omega
  have len:=initial.word q.toNat ch
  have bound : i<2^W := by cases q <;> dsimp [cap] at fit <;> omega
  have no : ¬portActive A input q i := by
    intro active
    have used:=((portActive_iff A input q i bound).1 active).2
    rw [len] at used
    cases q <;> simp [HistoryPortCatalogue.Page.at,Party.ofTile] at used off <;> omega
  simp [physicalWidth,no]

/-- The heterogeneous scanner only visits actual demand and supply words.
Padding rows are unreachable because the admitted page has its true port counts. -/
theorem source_rows (a page : ℕ) (initial : ReadPage A input rec a page)
    (supWidth : ∀u:Fin e,(physicalWidth A input true u.val).val=histWidth tile.output v (sp u).1.1+r*tile.bits)
    (demWidth : ∀u:Fin n,(physicalWidth A input false u.val).val=live (dp u).1.1)
    (demand : ∀(u:Fin n) (b:Fin (live (dp u).1.1)) m,
      agreesOutside (srcBase A false u.val) (srcBase A false u.val+live (dp u).1.1) m
        (beforePort A runPlan input false u.val) →
      (geometryTerm W A false).eval (fun _=>0) m (sourceRegisters A m false u.val (b.val:Word W))=
      (sourceAddress (old (dp u) b):Word W))
    (supply : ∀(u:Fin e) (b:Fin (histWidth tile.output v (sp u).1.1+r*tile.bits)) m,
      agreesOutside (srcBase A true u.val) (srcBase A true u.val+(histWidth tile.output v (sp u).1.1+r*tile.bits)) m
        (beforePort A runPlan input true u.val) →
      (geometryTerm W A true).eval (fun _=>0) m (sourceRegisters A m true u.val (b.val:Word W))=
      (sourceAddress (fresh (sp u) b):Word W)) :
    ∀q i,i<cap A q → ∀b,b<(physicalWidth A input q i).val → ∀m,
      agreesOutside (srcBase A q i) (srcBase A q i+(physicalWidth A input q i).val) m
        (beforePort A runPlan input q i) →
      (geometryTerm W A q).eval (fun _=>0) m (sourceRegisters A m q i (b:Word W))=
        ss q i (srcBase A q i+b) := by
  intro q i hi b hb m frame
  cases q with
  | false =>
    have u : i<n := by
      by_contra! no
      have zero:=padded_width_zero A input D G j base tile dp sp di si a page initial false i hi no
      omega
    have width:=demWidth ⟨i,u⟩
    change (physicalWidth A input false i).val=_ at width
    rw [width] at hb frame
    exact (demand ⟨i,u⟩ ⟨b,hb⟩ m frame).trans
      (typedSources_demand A D G j base live B sp tile.output v old fresh ⟨i,u⟩ ⟨b,hb⟩).symm
  | true =>
    have u : i<e := by
      by_contra! no
      have zero:=padded_width_zero A input D G j base tile dp sp di si a page initial true i hi no
      omega
    have width:=supWidth ⟨i,u⟩
    change (physicalWidth A input true i).val=_ at width
    rw [width] at hb frame
    exact (supply ⟨i,u⟩ ⟨b,hb⟩ m frame).trans
      (typedSources_supply A D G j base live B sp tile.output v old fresh ⟨i,u⟩ ⟨b,hb⟩).symm

/-- For a tile in the published S38 array, the native map scan and all its
source rows follow from the actual retained region and the typed bit lookups. -/
theorem emit_tile (page a : ℕ) (initial : ReadPage A input rec a page)
    (active : partyActive A input) (copies : (wordAt input (selected A input).incident 3).val=r)
    (nst : n≤A.demandCap) (est : e≤A.supplyCap) (digitBound : (∑i,base (dp i).1.1)≤A.digitCap)
    (positive : 0<A.party.V) (resident : portsEnd A<2^W)
    (headerBound : 3+5*A.demandCap+4*A.supplyCap≤A.party.V)
    (fits : ∀q i,i<cap A q → (physicalWidth A input q i).val≤A.party.V)
    (mapCount : (partyMapCount A input).val=size) (mapRoom : mapBase+size<2^W)
    (range : portsEnd A≤ mapBase ∨ mapBase+size≤A.temp)
    (header : HeaderFootprint A input A.temp (A.temp+(fields (W:=W) A).length))
    (keep : ∀addr,let sel:=selected A input
      addr=(A.nodePorts.cursor:Word W).val ∨ addr=(nodeWord A input+5).val ∨ addr=(sel.kernel+4).val ∨
      addr=(sel.incident+2).val ∨ addr=(sel.incident+3).val ∨
      (∃i:Fin 7,addr=(sel.kindPage+(i.val:Word W)).val) ∨
      (page≤addr ∧ addr<page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap) →
      (addr<A.temp ∨ portsEnd A≤addr) ∧ (addr< mapBase ∨ mapBase+size≤addr))
    (pageClear : let endPage:=page+HistoryPortCatalogue.stride A.demandCap A.supplyCap A.digitCap
      (endPage≤A.temp ∨ portsEnd A≤page) ∧ (endPage≤ mapBase ∨ mapBase+size≤page))
    (headAddress : page+HistoryPortCatalogue.headerBase A.demandCap A.supplyCap<2^W)
    (digit : ∀u:Fin n,base (dp u).1.1*r≤2^W)
    (scalar : 2+size+tile.bits+e+(B).arity+e*tile.bits+r*(e*tile.bits)+r*(B).arity+r*tile.bitCap<2^W)
    (supWidth : ∀u:Fin e,(physicalWidth A input true u.val).val=histWidth tile.output v (sp u).1.1+r*tile.bits)
    (demWidth : ∀u:Fin n,(physicalWidth A input false u.val).val=live (dp u).1.1)
    (oldRoom : ∀q b,sourceAddress (old q b)<2^W)
    (newRoom : ∀q b,sourceAddress (fresh q b)<2^W)
    (demand : ∀(u:Fin n) (b:Fin (live (dp u).1.1)) m,
      agreesOutside (srcBase A false u.val) (srcBase A false u.val+live (dp u).1.1) m
        (beforePort A runPlan input false u.val) →
      (geometryTerm W A false).eval (fun _=>0) m (sourceRegisters A m false u.val (b.val:Word W))=
      (sourceAddress (old (dp u) b):Word W))
    (supply : ∀(u:Fin e) (b:Fin (histWidth tile.output v (sp u).1.1+r*tile.bits)) m,
      agreesOutside (srcBase A true u.val) (srcBase A true u.val+(histWidth tile.output v (sp u).1.1+r*tile.bits)) m
        (beforePort A runPlan input true u.val) →
      (geometryTerm W A true).eval (fun _=>0) m (sourceRegisters A m true u.val (b.val:Word W))=
      (sourceAddress (fresh (sp u) b):Word W)) :
    (procedure W A).Exec input (output A runPlan input) (tariff W A runPlan) ∧
    ∀x:Fin size,output A runPlan input (mapBase+x.val)=
      (sourceAddress (partyPointer D G j base live B sp tile.output v old fresh x):Word W) := by
  have saved:=keep (A.nodePorts.cursor:Word W).val (.inl rfl)
  have capEq : (runPlan).gatherCount=size := mapCount
  have mapRange : portsEnd A≤(runPlan).gatherBase ∨ (runPlan).gatherBase+(runPlan).gatherCount≤A.temp := by
    rw [capEq];exact range
  have outFit (u:Fin e):histWidth tile.output v (sp u).1.1+r*tile.bits≤A.party.V := by
    rw [←supWidth];exact fits true u.val (u.isLt.trans_le est)
  have inFit (u:Fin n):live (dp u).1.1≤A.party.V := by
    rw [←demWidth];exact fits false u.val (u.isLt.trans_le nst)
  have source:=source_rows A input D G j base live tile dp sp di si v old fresh a page
    initial supWidth demWidth demand supply
  apply emit_map A input ss D G j base live B sp tile.output v old fresh positive headerBound resident
    nst est fits mapCount mapRoom range header saved.1 saved.2 outFit inFit digit scalar source
  intro scratch frame
  have scratchFrame : agreesOutside (runPlan).gatherBase ((runPlan).gatherBase+(runPlan).gatherCount)
      scratch (beforeGather A runPlan input) := by rw [capEq];exact frame
  have persistent:=initial.retain runPlan (by rw [header_size];omega) fits scratchFrame (by
    change ∀addr, _ → (_ ∨ _) ∧ (_ ∨ (runPlan).gatherBase+(runPlan).gatherCount≤addr)
    rw [capEq]
    exact keep)
  have nl := persistent.1.layout ((congrArg Fin.val persistent.2).trans copies) headAddress
  have extent:=initial.extent
  constructor
  · rw [nl.2.2.2.2.2.2]
    dsimp only [HistoryPortCatalogue.stride,HistoryPortCatalogue.headerBase,HistoryPortCatalogue.supplyBase] at *
    omega
  · apply image_from_pages A input scratch mapWords D G j base live tile dp sp di si v old fresh page a
      initial persistent.1 headAddress active copies ((congrArg Fin.val persistent.2).trans copies)
      nst est digitBound positive resident.le headerBound fits mapRange scratchFrame _ supWidth demWidth oldRoom newRoom
    change _ ∧ (_ ∨ (runPlan).gatherBase+(runPlan).gatherCount≤page)
    rw [capEq];exact pageClear
/-- Cost at a real admitted tile. The copy count alone bounds the sum of
all live port widths, including duplicated selector bits in the supply. -/
theorem tile_tariff_le (template : Layout) (mode : A.mode=template.mode)
    (dem : A.demandCap=template.demandCap) (sup : A.supplyCap=template.supplyCap)
    (a page : ℕ) (initial : ReadPage A input rec a page) (nst : n≤A.demandCap) (est : e≤A.supplyCap)
    (demWidth : ∀u:Fin n,(physicalWidth A input false u.val).val=live (dp u).1.1)
    (supWidth : ∀u:Fin e,(physicalWidth A input true u.val).val=histWidth tile.output v (sp u).1.1+r*tile.bits)
    (copyFit : ∀u:Fin n,live (dp u).1.1≤base (dp u).1.1*r)
    (mapLength : (partyMapCount A input).val=r*(e*tile.bits)+(r*(B).arity+e*(r*tile.bitCap))) :
    tariff W A P≤ schemaCost template*(1+r*((∑u,base (dp u).1.1)+
      e*(tile.bitCap+tile.bits)+e*tile.bits+(B).arity+e*tile.bitCap)) := by
  have zeroWidth := padded_width_zero A input D G j base tile dp sp di si a page initial
  have dsum : widthSum P false A.demandCap=∑u,live (dp u).1.1 :=
    range_eq nst _ _ demWidth (fun i hi off=>zeroWidth false i hi off)
  have ssum : widthSum P true A.supplyCap=∑u,(histWidth tile.output v (sp u).1.1+r*tile.bits) :=
    range_eq est _ _ supWidth (fun i hi off=>zeroWidth true i hi off)
  have db : (∑u,live (dp u).1.1)≤(∑u,base (dp u).1.1)*r := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun u _=>copyFit u)
  have sb : (∑u:Fin e,(histWidth tile.output v (sp u).1.1+r*tile.bits))≤e*(r*tile.bitCap+r*tile.bits) := by
    calc
      _ ≤ ∑_u:Fin e,(r*tile.bitCap+r*tile.bits) := Finset.sum_le_sum (fun u _=>
        Nat.add_le_add_right (FixedMotifMaxWidth.histWidth_le _ v _ _ (fun a=>tile.output_le_cap a _)) _)
      _ = _ := by simp
  apply (tariff_le A template P mode dem sup).trans
  apply Nat.mul_le_mul_left
  change 1+widthSum P false A.demandCap+widthSum P true A.supplyCap+(partyMapCount A input).val≤_
  rw [dsum,ssum,mapLength]
  calc
    _ ≤ 1+((∑u,base (dp u).1.1)*r)+e*(r*tile.bitCap+r*tile.bits)+
        (r*(e*tile.bits)+(r*(B).arity+e*(r*tile.bitCap))) := by gcongr
    _ = _ := by ring

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryScopeAddress
open Diagonal Diagonal.RefreshParty Diagonal.RefreshTies LinearAlgebra.SpectralBooks Expander
open scoped BigOperators Classical
noncomputable section

/-- Four resident pointers for the singleton old child of a refresh site. -/
structure RefreshOld (T : Layout) (mem : ℕ→ℕ) where
  child : ℕ
  header : ℕ
  table : ℕ
  start : ℕ
  idAt : mem T.childIDs=child
  headerAt : mem (T.nodes+(8*child+6))=header
  tableAt : mem (header+1)=table
  startAt : mem T.childStarts=start

def RefreshOld.pin {T : Layout} {mem : ℕ→ℕ} (O : RefreshOld T mem) (half bit : ℕ) :=
  O.start+(mem (O.table+(4*half+3))+bit)

/-- Retained successor half rows start at this pointer. -/
structure RefreshNew (T : Layout) (mem : ℕ→ℕ) where
  table : ℕ
  tableAt : mem (T.newHalves+1)=table

def RefreshNew.pin {T : Layout} {mem : ℕ→ℕ} (N : RefreshNew T mem) (half bit : ℕ) :=
  T.oldBits+(mem (N.table+(4*half+3))+bit)

private def cappedPin (p x : ℕ) : Fin (p+1) := ⟨min x p,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem cappedPin_inj {p x : ℕ} (i : Fin p) (eq : cappedPin p x=cappedPin p i.val) : x=i.val := by
  have val := congrArg Fin.val eq
  change min x p=min i.val p at val
  rw [Nat.min_eq_left i.isLt.le] at val
  by_cases h : x≤p
  · rwa [Nat.min_eq_left h] at val
  · rw [Nat.min_eq_right (by omega)] at val
    have := i.isLt
    omega

variable {U : Type} [Fintype U] {n h pad p hidden : ℕ} (π : Equiv.Perm (Address U n))
  (δ : U×Fin n→U×Fin n) (dest : ∀ e : Address U n,δ (e.1,e.2.2)=((π e).1,(π e).2.2))
  (c : Fin n→Fin n→ℕ) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (w : Address U n→ℕ) (s : U→Arc c→ℕ) (u : U) (v : Fin n)
variable (old : (q : (oldPortGraph π).Port (u,v))→Fin (w q.val.1)→Fin p)
  (fresh : (q : (rawGraph δ (fun _ : U => ports c)).Port (u,v))→Fin (rawWidth w s q.val.1)→Fin p)

omit [Fintype U] in
private theorem mapDemand {b : ℕ} (f : Fin p→Fin b) (q : (RefreshMotif.denseGraph n).Port v)
    (i : Fin (w (addr π u q.val.1))) :
    demandPin π δ dest (fun _ : U => ports c) w s u v (fun q k=>f (old q k)) (fun q k=>f (fresh q k)) q i =
      f (demandPin π δ dest (fun _ : U => ports c) w s u v old fresh q i) := by
  obtain ⟨⟨⟨dir,a,b'⟩,side⟩,eq⟩ := q
  cases side with
  | false => change a=v at eq; subst v; cases dir <;> rfl
  | true => change b'=v at eq; subst v; cases dir <;> rfl

omit [Fintype U] in
private theorem mapSparse {b : ℕ} (f : Fin p→Fin b) (q : (ports c).Port v) (i : Fin (s u q.val.1)) :
    sparsePin δ (fun _ : U => ports c) w s u v (fun q k=>f (fresh q k)) q i = f (sparsePin δ (fun _ : U => ports c) w s u v fresh q i) := by
  obtain ⟨⟨a,side⟩,eq⟩:=q
  cases side <;> rfl

variable (T : Layout) (mem : ℕ→ℕ) (O : RefreshOld T mem) (N : RefreshNew T mem)

omit [Fintype U] in
/-- Resolve the numerical dense location to its genuine `demandPin`. In the
bundle case its final bit includes the prefix over all earlier departure ports. -/
theorem Read.refreshDemand (q : (RefreshMotif.denseGraph n).Port v) (i : Fin (w (addr π u q.val.1)))
    (oldPrefix : ∀ (a : (oldPortGraph π).Port (u,v)) (k : Fin (w a.val.1)), O.pin (oldHalf π u v a) k.val=(old a k).val)
    (newPrefix : ∀ (a : (rawGraph δ (fun _ : U => ports c)).Port (u,v)) (k : Fin (rawWidth w s a.val.1)), N.pin (freshHalf (pad:=pad) δ c sym rows u v a) k.val=(fresh a k).val) :
    let loc := demandLocation (h:=h) (pad:=pad) π w u v q i.val
    Read T mem (fun j : Fin 4 => component loc j.val) (.pin (demandPin π δ dest (fun _ : U => ports c) w s u v old fresh q i) : BitSource hidden p) := by
  intro loc
  let pin := demandPin π δ dest (fun _ : U => ports c) w s u v old fresh q i
  let f : Fin p→Fin (p+1) := fun t=>cappedPin p t.val
  have Omap : (fun (a : (oldPortGraph π).Port (u,v)) (k : Fin (w a.val.1))=>cappedPin p (O.pin (oldHalf π u v a) k.val)) = (fun a k=>f (old a k)) := by
    funext a k; rw [oldPrefix]
  have Nmap : (fun (a : (rawGraph δ (fun _ : U => ports c)).Port (u,v)) (k : Fin (rawWidth w s a.val.1))=>cappedPin p (N.pin (freshHalf (pad:=pad) δ c sym rows u v a) k.val)) = (fun a k=>f (fresh a k)) := by
    funext a k; rw [newPrefix]
  have decoded := demandLocation_pin (h:=h) (pad:=pad) π δ dest c sym rows w s u v (0 : Fin (p+1))
    (fun a b=>cappedPin p (O.pin a b)) (fun a b=>cappedPin p (N.pin a b)) q i
  rw [Omap,Nmap,mapDemand] at decoded
  change resolve _ _ _ loc=f pin at decoded
  have tags : loc.scope=1 ∨ loc.scope=2 := by
    dsimp [loc,demandLocation]
    rw [ite_eq_left i.isLt]
    cases q.val.2 <;> simp
  have singleton : loc.child=0 := rfl
  rcases tags with oldTag|newTag
  · have val := cappedPin_inj pin (by simpa only [resolve,oldTag,ite_true] using decoded)
    apply Read.old pin O.child O.header O.table O.start (mem (O.table+(4*loc.half+3)))
    · simpa [component] using oldTag
    · simpa [component,singleton] using O.idAt
    · exact O.headerAt
    · exact O.tableAt
    · simpa [component,singleton] using O.startAt
    · simp [component]
    · simpa [component,RefreshOld.pin] using val.symm
  · have val := cappedPin_inj pin (by simpa only [resolve,newTag,show ¬(2:ℕ)=1 by decide,ite_false,ite_true] using decoded)
    apply Read.fresh pin N.table (mem (N.table+(4*loc.half+3)))
    · simpa [component] using newTag
    · exact N.tableAt
    · simp [component]
    · simpa [component,RefreshNew.pin] using val.symm

omit [Fintype U] in
/-- A live sparse bit resolves to the successor's typed port at its actual ordered half. -/
theorem Read.refreshSupply (q : (ports c).Port v) (i : Fin (s u q.val.1))
    (newPrefix : ∀ (a : (rawGraph δ (fun _ : U => ports c)).Port (u,v)) (k : Fin (rawWidth w s a.val.1)), N.pin (freshHalf (pad:=pad) δ c sym rows u v a) k.val=(fresh a k).val) :
    let loc:=sparseLocation (pad:=pad) c sym rows s u v q i.val
    Read T mem (fun j : Fin 4 => component loc j.val) (.pin (sparsePin δ (fun _ : U => ports c) w s u v fresh q i) : BitSource hidden p) := by
  intro loc
  let pin := sparsePin δ (fun _ : U => ports c) w s u v fresh q i
  let f : Fin p→Fin (p+1) := fun t=>cappedPin p t.val
  have Nmap : (fun (a : (rawGraph δ (fun _ : U => ports c)).Port (u,v)) (k : Fin (rawWidth w s a.val.1))=>cappedPin p (N.pin (freshHalf (pad:=pad) δ c sym rows u v a) k.val)) = (fun a k=>f (fresh a k)) := by
    funext a k; rw [newPrefix]
  let oldDummy := fun _ _ : ℕ=> (0 : Fin (p+1))
  have decoded := sparseLocation_pin (pad:=pad) δ c sym rows w s u v (0 : Fin (p+1)) oldDummy
    (fun a b=>cappedPin p (N.pin a b)) q i
  rw [Nmap,mapSparse] at decoded
  change resolve _ _ _ loc=f pin at decoded
  have tag : loc.scope=2 := by dsimp [loc,sparseLocation]; rw [ite_eq_left i.isLt]
  have val := cappedPin_inj pin (by simpa only [resolve,tag,show ¬(2:ℕ)=1 by decide,ite_false,ite_true] using decoded)
  apply Read.fresh pin N.table (mem (N.table+(4*loc.half+3)))
  · simpa [component] using tag
  · exact N.tableAt
  · simp [component]
  · simpa [component,RefreshNew.pin] using val.symm

end
end ThreeFlat.RAM.HistoryScopeAddress

namespace ThreeFlat.RAM.HistoryGatherExecution
open Diagonal Diagonal.HistoryContraction Diagonal.RefreshTies Diagonal.RefreshParty LinearAlgebra.SpectralBooks
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression Expander HistoryScopeAddress
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {V C L Pins : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L]
  {n h pad : ℕ} (G : LiftedSlots V n (C×L)) (port : Fin n≃C) (c : Fin n→Fin n→ℕ)
  (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h) (zero : ∀ i,c i i=0) (hn : 2≤n)
  (w : Address (V×L) n→ℕ) (s : V×L→Arc c→ℕ)
set_option quotPrecheck false
local notation "π" => arrival G port
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hn pad)
local notation "bw" => termWidth c w s
local notation "P" => (fun _ : V×L=>ports c)
variable (O : WordLayout (oldPortGraph (arrival G port)) w Pins)
  (N : WordLayout (actualPortGraph (outputGraph G c sym rows zero hn pad))
    (freshWidth c rows (termWidth c w s) pad) Pins)
  (own : (V×L)×Fin n → (V×L)×Fin n) (count : (V×L)×Fin n → ℕ)
  (ord : ∀ u,Fin (count u)≃{i // own i=u})
  (u : V×L) (v : Fin n) (fixed : own (u,v)=(u,v))
  {T : HistoryScopeAddress.Layout} {mem : ℕ→ℕ}

/-- The saved prefix in the actual singleton child yields the old pin used at this site. -/
theorem refresh_old_prefix (store : RefreshOld T mem)
    (start : store.start=WordLayout.childStart O own count ord (u,v) ⟨(u,v),fixed⟩)
    (half : ∀ q : (oldPortGraph π).Port (u,v),
      mem (store.table+(4*oldHalf π u v q+3))=O.ports.start (u,v) q)
    (q : (oldPortGraph π).Port (u,v)) (i : Fin (w q.val.1)) :
    store.pin (oldHalf π u v q) i.val=(WordLayout.oldPin O N own count ord (u,v) ⟨(u,v),fixed⟩ q i).val := by
  rw [RefreshOld.pin,start,half,WordLayout.oldPin_val]

/-- The public successor prefix uses the same numerical half ordinal as the padded
physical successor graph. The bit cast in `actualBit` preserves its offset. -/
theorem refresh_new_prefix (store : RefreshNew T mem)
    (oldBits : T.oldBits=WordLayout.prior O own count ord (u,v))
    (half : ∀ q : (Y).Port (u,v), mem (store.table+(4*physicalHalf (outputGraph G c sym rows zero hn pad)
      q.val.1 q.val.2+3))=N.ports.start (u,v) q)
    (q : (rawGraph (externalSite G) P).Port (u,v)) (i : Fin (bw q.val.1)) :
    store.pin (freshHalf (pad:=pad) (externalSite G) c sym rows u v q) i.val=
      (actualBit G c sym rows zero hn pad bw (WordLayout.newPin O N own count ord (u,v)) q i).val := by
  rw [RefreshNew.pin,oldBits,freshHalf_physical G c sym rows zero hn pad]
  change _+(_+(i.val))=(WordLayout.newPin O N own count ord (u,v) (actualHalf G c sym rows zero hn pad q) _).val
  rw [WordLayout.newPin_val]
  dsimp only [Fin.val_cast]
  rw [←half]; rfl

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution
open Diagonal Computability.VPVNP.Compression Diagonal.CompressorPacking.Native Diagonal.RefreshParty
open Diagonal.RefreshDemandRows Diagonal.RefreshTies MotifRows HistoryGeometryPointer
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr HistoryGatherBody BitLayout
open LinearAlgebra.SpectralBooks Expander HistoryScopeAddress
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {v a t h pad hidden pins W : ℕ}
  {G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t)}
  {C : SlotImage.Columns} {split : ℕ} {w : SlotImage.RefreshInput v a t→ℕ}
  (A : HistoryGatherBody.Layout) (m : Memory W) (mode : A.mode=.refresh (mPort a) h pad)
  (c : Fin (mPort a)→Fin (mPort a)→ℕ) (sym : ∀ i j,c i j=c j i)
  (rows : ∀ i,∑ j,c i j=h) (zero : ∀ i,c i i=0) (hn : 2≤ mPort a)
  (sw : Block v t→Arc c→ℕ) (z : Block v t) (p : Fin (mPort a)) (j : ℕ)
set_option quotPrecheck false
local notation "π" => arrival G (tagOrdinal a).symm
local notation "w₀" => SlotImage.demandWidth w
local notation "P" => (fun _ : Block v t=>ports c)
local notation "bw" => termWidth c (SlotImage.demandWidth w) sw
variable (old : (q : (oldPortGraph (arrival G (tagOrdinal a).symm)).Port (z,p)) →
    Fin (SlotImage.demandWidth w q.val.1) → Fin pins)
  (new : (q : (actualPortGraph (outputGraph G c sym rows zero hn pad)).Port (z,p)) →
    Fin (freshWidth c rows (termWidth c (SlotImage.demandWidth w) sw) pad q.val.1) → Fin pins)
local notation "src" => actualBit G c sym rows zero hn pad (termWidth c (SlotImage.demandWidth w) sw) new
local notation "regs" q:arg b:arg => sourceRegisters A m q j (b:Word W)
local notation "mu" => (fun x=>(m x).val)

theorem source_from_geometry (A : HistoryGatherBody.Layout) (m : Memory W) (q : Bool) (j b : ℕ)
    (answer : Word W) (room : srcBase A q j+b<2^W)
    (run : ∀ ptr : Word W,ptr.val=srcBase A q j+b →
      (sourceTerm W A q j).eval Fin.elim0 m (fun _=>ptr)=answer) :
    (geometryTerm W A q).eval (fun _=>0) m (sourceRegisters A m q j (b:Word W))=answer ∧
    ∀ ptr : Word W,ptr.val=srcBase A q j+b → (sourceTerm W A q j).eval Fin.elim0 m (fun _=>ptr)=answer := by
  let ptr : Word W := ((srcBase A q j+b : ℕ):Word W)
  have key : ptr.val=srcBase A q j+b := Fin.val_cast_of_lt room
  exact ⟨(sourceTerm_value A m q j b ptr key).symm.trans (run ptr key),run⟩

include mode in
/-- The live dense row evaluates to the old pin or its actual bundled successor
pin. The two aperture prefixes are supplied by `refresh_old_prefix` and
`refresh_new_prefix` on the chronological WordLayouts. -/
theorem refresh_demand_at (s : Fin (mPort a)) (dir side : Bool)
    (i : Fin (w₀ (addr π z (denseEnds p (dir,side,s)).val.1)))
    (store : Source m (refreshWidthRegisters A m false j) G C split w)
    (block : (m (selected A m).incident.val).val=blockId z)
    (party : (A.party.party:Word W).val=p.val)
    (code : (HistoryGatherBody.portCode A m false j).val=((if dir then 2 else 0)+(if side then 1 else 0))*mPort a+s.val)
    (banks : 3*mPort a<2^W) (lane : 2^t<2^W) (space : 4≤2^W) (room : srcBase A false j+i.val<2^W)
    (O : RefreshOld (layoutOf (regs false i.val)) mu) (N : RefreshNew (layoutOf (regs false i.val)) mu)
    (oldPrefix : ∀ (q : (oldPortGraph π).Port (z,p)) (b : Fin (w₀ q.val.1)), O.pin (oldHalf π z p q) b.val=(old q b).val)
    (newPrefix : ∀ (q : (rawGraph (externalSite G) P).Port (z,p)) (b : Fin (bw q.val.1)),
      N.pin (freshHalf (pad:=pad) (externalSite G) c sym rows z p q) b.val=(src q b).val) :
    let q:=denseEnds p (dir,side,s)
    let loc:=demandLocation (h:=h) (pad:=pad) π w₀ z p q i.val
    let H:=layoutOf (regs false i.val)
    let target : BitSource hidden pins:=.pin (demandPin π (externalSite G) (external_site G (tagOrdinal a).symm)
      P w₀ sw z p old src q i)
    (loc.scope=1 → H.childIDs<2^W ∧ H.nodes+(8*O.child+6)<2^W ∧ O.header+1<2^W ∧
      O.table+(4*loc.half+3)<2^W ∧ H.childStarts<2^W) →
    (loc.scope=2 → H.newHalves+1<2^W ∧ N.table+(4*loc.half+3)<2^W) →
    (geometryTerm W A false).eval (fun _=>0) m (regs false i.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase A false j+i.val →
      (sourceTerm W A false j).eval Fin.elim0 m (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro q loc H target oldRoom newRoom
  let locs := denseLocation G w h pad z p s dir side i.val
  have meaning : HistoryScopeAddress.Read H mu locs target :=
    HistoryScopeAddress.Read.refreshDemand (pad:=pad) π (externalSite G) (external_site G (tagOrdinal a).symm)
      c sym rows w₀ sw z p old src H mu O N q i oldPrefix newPrefix
  have tags : loc.scope=1 ∨ loc.scope=2 := by
    dsimp [loc,demandLocation]; rw [ite_eq_left i.isLt]; cases q.val.2 <;> simp
  have tag : locs 0=loc.scope := rfl
  have child : locs 1=0 := rfl
  have half : locs 2=loc.half := rfl
  have fits : ReadFits m (regs false i.val) locs := by
    apply readFits_of_addresses _ _ _ (by omega) (by omega)
    · intro select
      simpa only [child,half,Nat.add_zero,O.idAt,O.headerAt,O.tableAt] using oldRoom (tag ▸ select)
    · intro select
      simpa only [half,N.tableAt] using newRoom (tag ▸ select)
    · intro bad; omega
  apply source_from_geometry A m false j i.val _ room
  intro ptr key
  exact refresh_demand_source A m mode j i.val ptr z p s dir side key store block party code banks lane space target fits meaning

include mode in
/-- The live sparse row uses the half selected by the port's orientation and
actual sparse slot in the successor. It resolves to the same pin as `siteTree`. -/
theorem refresh_supply_at (q : (ports c).Port p) (i : Fin (sw z q.val.1))
    (store : Source m (refreshWidthRegisters A m true j) G C split w)
    (siteCount : ℕ) (siteBound : (wordAt m (selected A m).kernel 1).val<siteCount)
    (code : (HistoryGatherBody.portCode A m true j).val=((sparseOrder c sym rows p).symm q).val)
    (degree : h<2^W) (space : 4≤2^W) (apertureRoom : srcBase A true j+i.val<2^W)
    (N : RefreshNew (layoutOf (regs true i.val)) mu)
    (newPrefix : ∀ (e : (rawGraph (externalSite G) P).Port (z,p)) (b : Fin (bw e.val.1)),
      N.pin (freshHalf (pad:=pad) (externalSite G) c sym rows z p e) b.val=(src e b).val) :
    let s:=(numbering c rows (if q.val.2 then DoublePorts.reverseArc c sym q.val.1 else q.val.1)).2
    let stage:=m (selected A m).kernel.val
    let table:=(m (stage.val+40)).val
    let site:=(wordAt m (selected A m).kernel 1).val
    let half:=1+(if q.val.2 then 1+h+pad else 0)+s.val
    let target : BitSource hidden pins:=.pin (sparsePin (externalSite G) P w₀ sw z p src q i)
    (m (table+((site*(2*(1+h+pad))+half)*4+2))).val=sw z q.val.1 →
    table+siteCount*(2*(1+h+pad))*4≤2^W →
    (layoutOf (regs true i.val)).newHalves+1<2^W → N.table+(4*half+3)<2^W →
    (geometryTerm W A true).eval (fun _=>0) m (regs true i.val)=(sourceAddress target:Word W) ∧
    ∀ ptr : Word W, ptr.val=srcBase A true j+i.val →
      (sourceTerm W A true j).eval Fin.elim0 m (fun _=>ptr)=(sourceAddress target:Word W) := by
  intro s stage table site half target row tableRoom headerFit halfFit
  let locs:=sparseLocationWords h pad s q.val.2 i.val (sw z q.val.1)
  have meaning : HistoryScopeAddress.Read (layoutOf (regs true i.val)) mu locs target :=
    HistoryScopeAddress.Read.refreshSupply (pad:=pad) (externalSite G) c sym rows w₀ sw z p src _
      mu N q i newPrefix
  have tag : locs 0=2 := by simp [locs,sparseLocationWords,component,i.isLt]
  have H : locs 2=half := rfl
  have fits : ReadFits m (regs true i.val) locs := by
    apply readFits_of_addresses _ _ _ (by omega) (by omega)
    · intro bad; omega
    · intro _
      simpa only [H,N.tableAt] using And.intro headerFit halfFit
    · intro bad; omega
  apply source_from_geometry A m true j i.val _ apertureRoom
  intro ptr key
  have localCode : (HistoryGatherBody.portCode A m true j).val=(if q.val.2 then h else 0)+s.val :=
    code.trans (sparse_index c sym rows p q)
  exact refresh_supply_source A m mode j i.val ptr store siteCount siteBound s q.val.2 localCode
    (sw z q.val.1) row tableRoom degree key space target fits meaning

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan HistoryGatherBody BitLayout
open Diagonal Diagonal.RefreshTies Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks Expander
open Diagonal.HistoryContraction Diagonal.MotifOuterTerms Diagonal.HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section
variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F] [Fintype F]
  {m h p W : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m→Fin m→ℕ)
  (w : Address (V×L) m→ℕ) (base : V×L→Bool×Fin m×Fin m→ℕ) (r : V×L→ℕ)
  (T : ∀u,FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F) (x : Histories c base r T)
  (hm : 2≤ m) (hh : 0<h) (pad : ℕ) (sym : ∀i j,c i j=c j i) (rows : ∀i,∑j,c i j=h)
  (zero : ∀i,c i i=0) {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (u : V×L) (v : Fin m)

local notation "π" => arrival G port
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hm pad)
local notation "sparseW" => sparseWidth c base r T x
local notation "bw" => termWidth c w sparseW
local notation "newW" => freshWidth c rows bw pad
local notation "D" => RefreshMotif.denseGraph m
local notation "P" => (fun _ : V×L=>ports c)
local notation "S" => DoublePorts.connectedSupply c hh rows sym bound

open private outputPins pullPins from OAI.ThreeFlat.Diagonal.RefreshSiteTree

variable (old : (a : (oldPortGraph (arrival G port)).Port (u,v)) → Fin (w a.1.1) → Fin p)
variable (new : outputPins G c hm pad sym rows zero (termWidth c w (sparseWidth c base r T x)) (u,v) p)

attribute [local irreducible] actualPortGraph freshWidth

set_option maxHeartbeats 600000 in
/-- Specialize the emitted map to the unique refresh incident and its elected
raw party. The returned words refer to the demand and supply pins of siteTree. -/
abbrev emit_refresh (layout : HistoryGatherBody.Layout) (input : Memory W) :=
  letI : Nonempty (Fin m) := ⟨v⟩
  letI := (T u).hasLetter
  let A := {layout with party:={layout.party with motif:=0,party:=v.val}}
  let sa:=RefreshParty.sparseOrder c sym rows v
  let src := pullPins G c hm pad sym rows zero bw (u,v) p new
  let oi:=(fun q b=>(.pin (demandPin π (externalSite G) (external_site G port) P w sparseW u v old src q b):BitSource 0 p))
  let fi:=(fun q b=>(.pin (sparsePin (externalSite G) P w sparseW u v src q b):BitSource 0 p))
  emit_tile (F:=F) (W:=W) (p:=p) (h:=0) (r:=r u) (n:=4*m) (e:=2*h)
    A input D S v (base u) (profile G port w u) (T u)
    (RefreshParty.denseOrder v) sa Fin.val Fin.val (x u) oi fi

end
end ThreeFlat.RAM.HistoryGatherExecution

namespace ThreeFlat.RAM.HistoryGatherExecution

open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open Diagonal Diagonal.CompressorPacking Diagonal.HistoryContraction Diagonal.MotifKernel
open Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking Diagonal.HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

variable {c d Q p W : ℕ} {V H Tag L F : Type} [Field F] [Fintype F]
  [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  (P : PackingData V H Tag L d c) (w : Arc V H Tag L d c→ℕ) (code : Arc V H Tag L d c ↪ ℕ)
  (hQ : 0<Q) (num : P.Motif ≃ (Site V Tag L×Fin d)×Fin Q)
  (base : P.Motif→Fin 2→ℕ) (r : P.Motif→ℕ) (T : ∀m,FixedMotifTile demandGraph supplyGraph (base m) F)
  (x : Histories P base r T) (hn : ∀a : Tag,-a=a) (good : TagConditions P.slots (shift P) P.offset)
  (n : Fin 4→ℕ) (positive : ∀i,0<n i) (edgeOrder : ShrinkEdge P n ↪ ℕ) (hc : 2≤c) (pad : ℕ)
  (padding : LiftedSlots (V×Tag) pad L) (site : Site V Tag L)

local notation "lay" => historyLayout P base r T x
local notation "outG" => outGraph P hn good lay n edgeOrder hc pad padding
local notation "outW" => outputWidth P base r T x hn good lay n edgeOrder hc pad

open private sitePins from OAI.ThreeFlat.Diagonal.ShrinkSiteTree

attribute [local irreducible] historyLayout shrinkingGraph slotPortGraph SlotRefinement.actualWidth allPieceSlots

set_option maxHeartbeats 600000 in
private abbrev gatherShrinkAt (choice : Bool)
    (old : (i : {i // P.placement choice i = site}) →
      (q : (oldGraph P).Port i.val) → Fin (w q.1.1) → Fin p)
    (new : sitePins (outGraph P hn good choice n edgeOrder hc pad padding)
      (outputWidth P base r T x hn good choice n edgeOrder hc pad) site p)
    (m : P.Motif) (part : {u // partySite P choice m u = site})
    (layout : HistoryGatherBody.Layout) (incident : ℕ) (input : Memory W) :=
  letI := (T m).hasLetter
  let A := {layout with party:={layout.party with motif:=incident,party:=part.val.val}}
  let dp := (Fintype.equivFin (demandGraph.Port part.val)).symm
  let sp := (Fintype.equivFin (supplyGraph.Port part.val)).symm
  let place := partySite P choice m
  let owned := HistoryMaskOrder.order (fun e=>wireOwner supplyGraph.tail supplyGraph.head place e=some site)
  let priv := HistogramTileNetwork.order (k:=(T m).bits) ShrinkMotif.supply place site (T m).output (x m) owned
  let cross := crossingPin (p:=p) P base r T x hn good choice n positive edgeOrder hc pad padding site new m
  let oi := oldPinSource (h:=priv.bits) P w code hQ num choice site old m part.val
  emit_tile (F:=F) (W:=W) (p:=p) (h:=priv.bits) (r:=r m)
    (n:=Fintype.card (demandGraph.Port part.val)) (e:=Fintype.card (supplyGraph.Port part.val))
    A input demandGraph ShrinkMotif.supply part.val (base m) (demandWidth P w num m) (T m)
    dp sp (fun i=>(dp i).val.1.val) (fun i=>(sp i).val.1.val) (x m) oi (priv.partySource cross part)

/-- Run the gather for one actual party of an occupied shrinkPiece. Its supply
callback uses the original masked private-edge order and numbered successor slots. -/
abbrev emit_shrink :=
  gatherShrinkAt (p:=p) (W:=W) P w code hQ num base r T x hn good n positive edgeOrder hc pad padding
    site (historyLayout P base r T x)


end
end ThreeFlat.RAM.HistoryGatherExecution

end OAI
