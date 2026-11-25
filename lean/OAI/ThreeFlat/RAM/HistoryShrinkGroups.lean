import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.Diagonal.HistorySiteFootprint
import OAI.ThreeFlat.Diagonal.ShrinkDemandPrefix
import OAI.ThreeFlat.Diagonal.ShrinkSupplyPrefix
import OAI.ThreeFlat.RAM.HistoryStageSetup
import OAI.ThreeFlat.Diagonal.ShrinkLayerCopies
import OAI.ThreeFlat.RAM.HistoryMotifJoin
import OAI.ThreeFlat.RAM.HistoryRefreshEmitter
import OAI.ThreeFlat.RAM.HistoryGatherExecution
import OAI.ThreeFlat.Diagonal.ShrinkSiteTree

namespace OAI
/-! # Emission of the occupied-party and active-motif joins of a physical shrink -/
set_option quotPrecheck false
set_option maxErrors 600
namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure BitLayout
open HistoryMotifJoin HistoryBoundedJoin HistoryBoundedBody HistoryJoinScan
open Diagonal.HistoryContraction BitNetwork.Ordered
open scoped Fin.CommRing BigOperators

noncomputable section
variable {W n h p : ℕ} {F : Type} {arity : Fin n → ℕ}
  (A : HistoryGatherBody.Layout) (group : Bool) (node : ℕ) (m : Memory W)
  (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p)

def sector (i : Fin n) (col : ℕ) := sourceBank A node group i.val (role A m i.val) col

private abbrev out (j : ℕ) := resultBank A node group j
private abbrev T := groupHub A m group node p h n

def copy (i : Fin n) : Header ℕ :=
  ⟨sector A group node m i 0,out A group node 0 + 4*Tree.before (fun j=>(N j).cells) i,
    sector A group node m i 3,arity i,p,h+Tree.before (fun j=>(N j).internal) i⟩

def mapRow (i : Fin n) : Tape.MapRow :=
  ⟨if group then 10 else 11,(groupLink A m group node i.val).operand,
    if group then sector A group node m i 2 else 2,0,0⟩

/-- The group writer visits the masks in ascending raw-party order and the outer
site writer visits the dense incidence list in physical order. Both store a four-word
link referencing the stream already produced at the selected chronological child. -/
structure Roots (raw : ℕ→ℕ) : Prop where
  links : ∀ (i : Fin n) (j : Fin 4),raw ((T A group node m (h:=h) (p:=p) (n:=n)).children+(4*i.val+j.val)) =
    (groupLink A m group node i.val).words j
  headers : ∀ (i : Fin n) (j : Fin 4),raw (sector A group node m i 1+j.val) =
    (Info.mk (sector A group node m i 0) (arity i) (N i).cells (N i).internal).words j

local notation "HUB" => groupHub A m group node p h n
local notation "src" => sector A group node m
local notation "dest" => out A group node
local notation "qa" => copy A group node m N (h:=h) (p:=p)
local notation "ma" => mapRow A group node m (n:=n)

private theorem child_from_words (hub : Hub) (raw : ℕ→ℕ) (index : ℕ) (c : Child)
    (word : ∀ j : Fin 4,raw (hub.children+(4*index+j.val))=c.words j) :
    child hub raw index=c := by
  cases c with
  | mk node map opcode operand =>
    have h₀ : raw (hub.children+4*index)=node := word 0
    have h₁ : raw (hub.children+4*index+1)=map := word 1
    have h₂ : raw (hub.children+4*index+2)=opcode := word 2
    have h₃ : raw (hub.children+4*index+3)=operand := word 3
    simp only [HistoryBoundedJoin.child,h₀,h₁,h₂,h₃]

private theorem info_from_words (raw : ℕ→ℕ) (addr : ℕ) (data : Info)
    (word : ∀ j : Fin 4,raw (addr+j.val)=data.words j) : read addr raw=data := by
  cases data with
  | mk stream pins factors hidden =>
    have h₀ : raw addr=stream := word 0
    have h₁ : raw (addr+1)=pins := word 1
    have h₂ : raw (addr+2)=factors := word 2
    have h₃ : raw (addr+3)=hidden := word 3
    simp only [HistoryBoundedJoin.read,h₀,h₁,h₂,h₃]

theorem Roots.link {raw : ℕ→ℕ} (R : Roots A group node m N (h:=h) (p:=p) raw) (i : Fin n) :
    child HUB raw i.val=groupLink A m group node i.val := by
  exact child_from_words HUB raw i.val _ (R.links i)

theorem Roots.get {raw : ℕ→ℕ} (R : Roots A group node m N (h:=h) (p:=p) raw) (i : Fin n) :
    read (child HUB raw i.val).node raw=⟨src i 0,arity i,(N i).cells,(N i).internal⟩ := by
  rw [Roots.link A group node m N R i]
  exact info_from_words raw (src i 1) _ (R.headers i)

include wire in
theorem Roots.commands {raw : ℕ→ℕ} (R : Roots A group node m N (h:=h) (p:=p) raw)
    (shared : (if group then h else 0)=h) (i : Fin n) :
    command HUB raw i.val false= ![(ma i).arg,(qa i).pins,(ma i).op,0,0,0,(qa i).pins+arity i] ∧
    command HUB raw i.val true= ![(HUB).arguments+7*i.val,(qa i).dest,1,0,0,0,(qa i).dest+4*(N i).cells] ∧
    arguments HUB raw i.val= ![(qa i).source,(qa i).dest,(qa i).pins,arity i,p,(qa i).offset,(qa i).dest+4*(N i).cells] := by
  have records (j : Fin n) :
    read (child HUB raw j.val).node raw=⟨(read (child HUB raw j.val).node raw).stream,
      arity j,(N j).cells,(N j).internal⟩ := by rw [Roots.get A group node m N R j]
  have move:=moved_eq N wire HUB raw i shared records
  simp only [command,arguments,Roots.get A group node m N R i,move.1,move.2]
  simp only [Roots.link A group node m N R i]; exact ⟨rfl,rfl,rfl⟩

/-- The result pointer and its six-word hub are completely determined by
the selected node, local masks and interval prefix. -/
def build : Build W := groupBuild A group (groupHub A m group node p h n) m

local notation "B" => build A group node m (p:=p) (h:=h) (n:=n)

variable (id : ((Fin 3→Bool)→F)→ℕ)

structure Reads : Prop where
  records : ∀ i,HistoryCompiledRows.Records id (N i) (src i 0) m
  info : ∀ i j,m (src i 1+j.val)=((Info.mk (src i 0) (arity i) (N i).cells (N i).internal).words j:Word W)
  mapped : ∀ i (j : Fin (arity i)),group=true → m (src i 2+j.val)=(sourceAddress (wire i j):Word W)
  identity : ∀ i (j : Fin (arity i)),group=false → sourceAddress (wire i j)=2+j.val

/-- The physical group header is written to the small seed region. Input stream,
child Info, and copied pin map lie in the private cache sectors. -/
def inChild (x : ℕ) := ∃ i : Fin n,
  (src i 0≤x ∧ x<src i 0+4*(N i).cells) ∨
  (src i 1≤x ∧ x<src i 1+4) ∨ (group=true ∧ src i 2≤x ∧ x<src i 2+arity i)

def inLayout (x : ℕ) :=
  (A.party.seed+64≤x ∧ x<A.party.seed+64+7+
       (4*(if group then A.party.parties else A.party.motifs)+3*(if group then A.party.parties else A.party.motifs))) ∨
    inChild A group node m N x

structure LayoutRoom : Prop where
  hubRoom : A.party.seed+64+(HistoryMotifJoin.rows A W group).length<2^W
  infoFit : ∀ (i : Fin n) (j : Fin 4),(Info.mk (src i 0) (arity i) (N i).cells (N i).internal).words j<2^W
  linkFit : ∀ (i : Fin n) (j : Fin 4),(groupLink A m group node i.val).words j<2^W
  childAway : ∀ x,inChild A group node m N x→x<A.party.seed+64 ∨ A.party.seed+64+(HistoryMotifJoin.rows A W group).length≤x
  seedAway : ∀ x,inLayout A group node m N x→x<(B).layout.seed ∨ (B).layout.seed+9≤x
  cmdAway : ∀ x,inLayout A group node m N x→x<(B).layout.commands ∨ (B).layout.commands+14*n≤x
  argsAway : ∀ x,inLayout A group node m N x→x<(B).hub.arguments ∨ (B).hub.arguments+7*n≤x

theorem sourceWord (_read : Reads A group node m N wire id) (room : LayoutRoom A group node m N (h:=h) (p:=p))
    (x : ℕ) (hx : inChild A group node m N x) : (B).input x=m x := by
  have off : ¬(A.party.seed+64≤x ∧ x<A.party.seed+64+(HistoryMotifJoin.rows A W group).length) := by
    rcases room.childAway x hx with h|h <;>omega
  change headerImage _ _ _ m x=_
  simp [headerImage,fillSegment,off]

theorem prepFrame (room : LayoutRoom A group node m N (h:=h) (p:=p)) (x : ℕ)
    (hx : inLayout A group node m N x) :
    (B).seeded x=(B).input x ∧ (B).commands x=(B).input x ∧ (B).entered x=(B).input x := by
  have hs:=room.seedAway x hx
  have hc:=room.cmdAway x hx
  have ha:=room.argsAway x hx
  have bs:¬((B).layout.seed≤x ∧ x<(B).layout.seed+9):=by omega
  have bc:¬((B).layout.commands≤x ∧ x<(B).layout.commands+14*(B).hub.argc):=by
    change ¬((B).layout.commands≤x ∧ x<(B).layout.commands+14*n);omega
  have ba:¬((B).hub.arguments≤x ∧ x<(B).hub.arguments+7*(B).hub.argc):=by
    change ¬((B).hub.arguments≤x ∧ x<(B).hub.arguments+7*n);omega
  simp [Build.seeded,Build.commands,Build.entered,fillSegment,bs,bc,ba]

theorem disk {snap : Memory W} (read : Reads A group node m N wire id)
    (room : LayoutRoom A group node m N (h:=h) (p:=p))
    (bound : n≤ if group then A.party.parties else A.party.motifs)
    (links : ∀ (i : Fin n) (j : Fin 4),(B).input ((HUB).children+(4*i.val+j.val))=
        ((groupLink A m group node i.val).words j:Word W))
    (frame : ∀ x,inLayout A group node m N x→snap x=(B).input x) :
    Roots A group node m N (h:=h) (p:=p) (HistoryPartyBatchExec.numeric snap) := by
  constructor
  · intro i j
    have lo : inLayout A group node m N ((HUB).children+(4*i.val+j.val)) := Or.inl (by
      change A.party.seed+64≤A.party.seed+64+7+(4*i.val+j.val) ∧ _
      have := i.isLt
      have := j.isLt
      dsimp only [groupHub]
      omega)
    rw [HistoryPartyBatchExec.numeric,frame _ lo,links,Fin.val_cast_of_lt (room.linkFit i j)]
  · intro i j
    have lo : inChild A group node m N (src i 1+j.val) := ⟨i,Or.inr (Or.inl (by have:=j.isLt;omega))⟩
    rw [HistoryPartyBatchExec.numeric,frame _ (Or.inr lo),sourceWord A group node m N wire id read room _ lo,
      read.info,Fin.val_cast_of_lt (room.infoFit i j)]


local notation "jobs" => Tape.tape (W:=W) N wire id qa

/-- These inequalities protect the two emitted regions (pin maps and output
rows) against the numeric source slots and the two controller tables. -/
structure Bounds : Prop where
  commands : ∀ i : Fin n,∀ b : Bool,∀ j : Fin 7,(B).protectedAt N qa
    ((B).layout.commands+(14*i.val+7*b.toNat+j.val))
  operands : ∀ i : Fin n,∀ j : Fin 3,(B).protectedAt N qa ((ma i).arg+j.val)
  arguments : ∀ i : Fin n,∀ j : Fin 6,(B).protectedAt N qa ((B).hub.arguments+(7*i.val+j.val))
  readStream : ∀ i, ∀ r : Fin (N i).cells, ∀ j : Fin 4,(B).protectedAt N qa (src i 0+(4*r.val+j.val))
  readMap : ∀ i : Fin n,group=true→∀ j : Fin (arity i),(B).protectedAt N qa (src i 2+j.val)
  operandEnd : ∀ i : Fin n,(ma i).arg+4<2^W

theorem group_banks (read : Reads A group node m N wire id) (room : LayoutRoom A group node m N (h:=h) (p:=p))
    (held : Bounds A group node m N (h:=h) (p:=p))
    (source : (B).Source jobs) (shared : (if group then h else 0)=h)
    (links : ∀ (i : Fin n) (j : Fin 4),(B).input ((HUB).children+(4*i.val+j.val))=
        ((groupLink A m group node i.val).words j:Word W))
    (ops : ∀ (i : Fin n) (j : Fin 3),(B).input ((groupLink A m group node i.val).operand+j.val)=
      groupArgs A m group node i.val j) : (B).Banks N wire id qa ma := by
  have cap : n≤ if group then A.party.parties else A.party.motifs:=source.cap
  have atSeed:=disk A group node m N wire id read room cap links (fun x h=>(prepFrame A group node m N room x h).1)
  have atCommands:=disk A group node m N wire id read room cap links (fun x h=>(prepFrame A group node m N room x h).2.1)
  have ctl : (B).control.val=(B).layout.seed+7:=Fin.val_cast_of_lt (by have:=source.seedRoom;omega)
  have argLoc (i : Fin n) (j : Fin 3) : inLayout A group node m N ((ma i).arg+j.val) := Or.inl (by
    change A.party.seed+64≤A.party.seed+64+7+4*(if group then A.party.parties else A.party.motifs)+3*i.val+j.val ∧ _
    have := i.isLt
    have := j.isLt
    dsimp only [mapRow,groupLink]
    omega)
  have old {x : ℕ} (ok : inChild A group node m N x) : (B).entered x=m x :=
    ((prepFrame A group node m N room x (.inr ok)).2.2).trans (sourceWord A group node m N wire id read room x ok)
  refine ⟨rfl,?_,source.commandRoom.le,.inl source.order.2,held.commands,?_,?_,held.operandEnd,?_,?_,?_,?_,
    source.argumentsRoom.le,held.arguments,?_,held.readStream,?_⟩
  · rw [ctl]
    exact ((B).entered_word jobs source 7).trans ((B).seeded_word 7)
  · intro i
    exact congrFun (Roots.commands A group node m N wire atSeed shared i).1 2
  · intro i
    exact congrFun (Roots.commands A group node m N wire atSeed shared i).1 0
  · intro i j used
    have hj:j.val<3 := by rcases used with u|u;exact u;cases group <;> simp [mapRow] at u
    exact held.operands i ⟨j.val,hj⟩
  · intro i j used
    have hj:j.val<3 := by rcases used with u|u;exact u;cases group <;> simp [mapRow] at u
    let k:Fin 3:=⟨j.val,hj⟩
    rw [((prepFrame A group node m N room _ (argLoc i k)).2.2)]
    have count:=read.info i (1:Fin 4)
    change m (src i 1+1)=(arity i:Word W) at count
    have fields (q : Fin 3) : groupArgs A m group node i.val q =
        ((![ (qa i).pins,arity i,(ma i).split,(ma i).first,(ma i).second]
          (q.castLE (by decide : 3 ≤ 5)) : ℕ) : Word W) := by
      fin_cases q
      · rfl
      · exact count
      · rfl
    have index : k.castLE (by decide : 3 ≤ 5) = j := Fin.ext rfl
    have argAddress : (ma i).arg = (groupLink A m group node i.val).operand := rfl
    rw [argAddress]
    simpa only [index] using (ops i k).trans (fields k)
  · intro i j
    by_cases yes : group=true
    · have e:(ma i).op=10:=by simp [mapRow,yes]
      have split:(ma i).split=src i 2:=by simp [mapRow,yes]
      have key : inChild A group node m N (src i 2+j.val) := ⟨i,Or.inr (Or.inr ⟨yes,by omega,by have:=j.isLt;omega⟩)⟩
      simpa [Tape.MapRow.value,e,split,old key] using read.mapped i j yes
    · have no : group=false:=by cases group <;> simp_all
      simp [Tape.MapRow.value,mapRow,no,read.identity i j no]
  · intro i r j
    have yes : group=true := by cases group <;> simp_all [mapRow]
    have split : (ma i).split = src i 2 := by simp [mapRow,yes]
    rw [split]
    exact held.readMap i yes j
  · intro i j
    have eqn:=congrFun (Roots.commands A group node m N wire atCommands shared i).2.2 j.castSucc
    fin_cases j <;> exact eqn
  · intro i r j
    have key : inChild A group node m N (src i 0+(4*r.val+j.val)) :=
      ⟨i,Or.inl (by have:=r.isLt;have:=j.isLt;omega)⟩
    exact (old key).trans (read.records i r j)


/-- The stream of each selected party, and later the stream of each selected
motif, is joined inside one reserved sector. A map sector is private to its child. -/
structure Space : Prop where
  room : ∀ i,(qa i).pins+arity i≤2^W
  copyRoom : ∀ i,group=true→src i 2+arity i≤2^W
  splitRoom : ∀ i,(ma i).split<2^W
  maps : ∀ i j,(qa j).pins+arity j≤(qa i).dest ∨ (qa i).dest+4*(N i).cells≤(qa j).pins
  cursorPins : ∀ i,(B).control.val<(qa i).pins ∨ (qa i).pins+arity i≤(B).control.val
  cursorRows : ∀ i,(B).control.val<(qa i).dest ∨ (qa i).dest+4*(N i).cells≤(B).control.val
  streams : ∀ i,src i 0+4*(N i).cells≤2^W
  pinCount : ∀ i,2+arity i<2^W
  words : ∀ i r j,HistoryCompiledRows.metadata id (N i) r j<2^W
  rowCount : 4*(∑ i,(N i).cells)≤A.party.V

theorem nextResult : dest 1=dest 0+A.party.V := by
  cases group <;> simp [out,resultBank,bankAddr,HistoryScratch.atWord,HistoryScratch.sector] <;> ring


structure SourceBounds : Prop where
  wide : 14<2^W
  capacity : (if group then A.party.parties else A.party.motifs)≤2^W
  seed : (B).layout.seed+9<2^W
  order : (B).layout.seed+9≤(B).layout.commands ∧ (B).layout.commands+14*n≤(HUB).arguments
  commands : (B).layout.commands+14*n<2^W
  arguments : (HUB).arguments+7*n<2^W
  links : (HUB).children+4*n≤2^W
  children : ∀ i : Fin n,src i 1+3<2^W
  result : dest 1+4<2^W
  resultDisjoint : ∀ x,inLayout A group node m N x→x<dest 1 ∨ dest 1+4≤x
  controlAway : HistoryReadyTape.Away (B).layout.seed 9 jobs ∧ HistoryReadyTape.Away (B).layout.commands (14*n) jobs
  limits : ∀ j∈jobs,j.finish<2^W

theorem headLoc (j : Fin 7) : inLayout A group node m N ((B).layout.hub+j.val) :=
  Or.inl (by
    change A.party.seed+64≤A.party.seed+64+j.val ∧ A.party.seed+64+j.val<
      A.party.seed+64+7+(4*(if group then A.party.parties else A.party.motifs)+
        3*(if group then A.party.parties else A.party.motifs))
    have bounded := j.isLt
    omega)

theorem group_source (read : Reads A group node m N wire id) (room : LayoutRoom A group node m N (h:=h) (p:=p))
    (bounds : SourceBounds A group node m N wire id) (bound : n≤ if group then A.party.parties else A.party.motifs)
    (shared : (if group then h else 0)=h)
    (hw : ∀ j : Fin 6,(B).input ((B).layout.hub+j.val)=((HUB).words j:Word W))
    (destWord : (B).input ((B).layout.hub+6)=(dest 1:Word W))
    (links : ∀ (i : Fin n) (j : Fin 4),(B).input ((HUB).children+(4*i.val+j.val))=
      ((groupLink A m group node i.val).words j:Word W))
    (hubFit : ∀ j : Fin 6,(HUB).words j<2^W)
    (keep : ∀ x,inLayout A group node m N x→x≠(B).control.val ∧ ∀ j∈jobs,x<j.start ∨ j.finish≤x) :
    (B).Source jobs := by
  have seeds:=disk A group node m N wire id read room bound links (fun x h=>(prepFrame A group node m N room x h).1)
  have cmds:=disk A group node m N wire id read room bound links (fun x h=>(prepFrame A group node m N room x h).2.1)
  have atEnd (x : ℕ) (hi : inLayout A group node m N x) : (B).reached jobs x=(B).input x :=
    (HistoryReadyTape.after_away _ _ _ x (keep x hi).1 (keep x hi).2).trans (prepFrame A group node m N room x hi).2.2
  have done_:=disk A group node m N wire id read room bound links atEnd
  have first (j : Fin 6) : HistoryPartyBatchExec.numeric (B).input ((B).layout.hub+j.val)=(HUB).words j :=
    (congrArg Fin.val (hw j)).trans (Fin.val_cast_of_lt (hubFit j))
  have ed (j : Fin 6) : HistoryPartyBatchExec.numeric ((B).reached jobs) ((B).layout.hub+j.val)=(HUB).words j :=
    (congrArg Fin.val (atEnd _ (headLoc A group node m N (h:=h) (p:=p) j.castSucc))).trans (first j)
  have base : (B).outputBase=dest 1:=by
    rw [Build.outputBase,HistoryPartyBatchExec.numeric,destWord,Fin.val_cast_of_lt (by have:=bounds.result;omega)]
  have byFrame (μ : Memory W) (im : Roots A group node m N (h:=h) (p:=p) (HistoryPartyBatchExec.numeric μ))
      (lo len : ℕ) (off : ∀ x,inLayout A group node m N x→x<lo ∨ lo+len≤x) :
      HistoryBoundedBody.Frame (B).layout HUB μ lo len := by
    constructor
    · intro j;exact off _ (headLoc A group node m N (h:=h) (p:=p) j)
    · intro i j
      apply off _ (Or.inl ?_)
      change A.party.seed+64 ≤ A.party.seed+64+7+4*i.val+j.val ∧
        A.party.seed+64+7+4*i.val+j.val < A.party.seed+64+7+
          (4*(if group then A.party.parties else A.party.motifs)+
           3*(if group then A.party.parties else A.party.motifs))
      have hi:i.val<n:=i.isLt
      have := j.isLt
      omega
    · intro i j
      rw [Roots.link A group node m N im i]
      apply off _ (Or.inr ⟨i,Or.inr (Or.inl ?_)⟩)
      change src i 1≤ src i 1+j.val ∧ src i 1+j.val<src i 1+4
      have:=j.isLt
      omega
  have cmdsAt (i : Fin n) := Roots.commands A group node m N wire seeds shared i
  have load := (B).loaded N wire id qa rfl (Or.inl bounds.order.2)
    (fun i=>congrFun (cmdsAt i).1 1) (fun i=>congrFun (cmdsAt i).1 6)
    (fun i=>congrFun (cmdsAt i).2.1 1) (fun i=>congrFun (cmdsAt i).2.1 6)
  let endMem:=HistoryPartyBatchExec.numeric ((B).reached jobs)
  have read : readHub (B).layout endMem=HUB := by
    change Hub.mk _ _ _ _ _ _ = Hub.mk (HUB).stream (HUB).pins (HUB).shared
      (HUB).argc (HUB).children (HUB).arguments
    congr 1
    · exact ed 0
    · exact ed 1
    · exact ed 2
    · exact ed 3
    · exact ed 4
    · exact ed 5
  have count : endMem ((B).layout.hub+3)=n:=ed 3
  have children : endMem ((B).layout.hub+4)=(HUB).children:=ed 4
  refine ⟨bound,bounds.seed,?_,.inr ?_,bounds.order,bounds.commands,bounds.arguments,first,?_,
    byFrame (B).seeded seeds _ _ room.cmdAway,byFrame (B).commands cmds _ _ room.argsAway,bounds.wide,
    bounds.capacity,bounds.links,?_,Tape.tape_length N wire id qa,bounds.controlAway,bounds.limits,load,
    ?_,?_,?_,?_,?_⟩
  · have h:=room.hubRoom
    rw [rows_len] at h
    change A.party.seed+64+7<2^W;omega
  · change A.party.seed+9≤A.party.seed+64;omega
  · intro j
    have h:=prepFrame A group node m N room _ (headLoc A group node m N (h:=h) (p:=p) j.castSucc)
    exact ⟨(congrArg Fin.val h.1).trans (first j),(congrArg Fin.val h.2.1).trans (first j)⟩
  · intro i
    change (child HUB (HistoryPartyBatchExec.numeric (B).seeded) i.val).node+3<2^W ∧
      (child HUB (HistoryPartyBatchExec.numeric (B).commands) i.val).node+3<2^W
    rw [Roots.link A group node m N seeds i,Roots.link A group node m N cmds i]
    exact ⟨bounds.children i,bounds.children i⟩
  · rw [base];exact bounds.result
  · rw [base,read];exact byFrame _ done_ _ _ bounds.resultDisjoint
  · exact congrArg Fin.val (atEnd _ (headLoc A group node m N (h:=h) (p:=p) 6))
  · dsimp only;change endMem ((B).layout.hub+4)+4*endMem ((B).layout.hub+3)≤2^W;rw [count,children];exact bounds.links
  · dsimp only;change ∀ k : Fin (endMem ((B).layout.hub+3)),endMem (endMem ((B).layout.hub+4)+4*k.val)+3<2^W
    rw [count,children];intro k
    have ptr:=done_.links k (0:Fin 4)
    change endMem ((HUB).children+(4*k.val+0))=src k 1 at ptr
    rw [Nat.add_zero] at ptr
    rw [ptr];exact bounds.children k

theorem group_emit (read : Reads A group node m N wire id) (room : LayoutRoom A group node m N (h:=h) (p:=p))
    (held : Bounds A group node m N (h:=h) (p:=p)) (space : Space A group node m N id (h:=h) (p:=p))
    (stable : HistoryPartyBatchExec.Protected (joinHeader A W group) m (A.party.seed+64) (HistoryMotifJoin.rows A W group).length)
    (G : GroupRead A group m) (live : G.count=n) (atNode : G.node=node)
    (pins : G.pins=p) (shared : (if group then G.shared else 0)=h)
    (sourceRoom : SourceBounds A group node m N wire id)
    (keep : ∀ x,inLayout A group node m N x→x≠(B).control.val ∧ ∀ j∈jobs,x<j.start ∨ j.finish≤x)
    (hubFit : ∀ j : Fin 6,(HUB).words j<2^W) :
    (join A W group).Exec m ((B).output jobs)
      (4+(HistoryMotifJoin.rows A W group).length*(2*(joinHeader A W group).binds+4)+(B).ticks jobs) ∧
    HistoryCompiledRows.Records id (glue N wire) (dest 0) ((B).output jobs) ∧
    ∀ j : Fin 4,(B).output jobs (dest 1+j.val)=
      ((Info.mk (dest 0) p (glue N wire).cells (glue N wire).internal).words j:Word W) := by
  have shar : (if group then h else 0)=h := by
    by_cases yes : group=true
    · exact ite_eq_left yes
    · simpa only [ite_eq_right yes] using shared
  have image := GroupRead.group_image A G room.hubRoom
  have hubEq : groupHub A m group G.node G.pins G.shared G.count=HUB := by
    simp only [groupHub,atNode,pins,live,shared,shar]
  have gw (j : Fin 6) : (B).input ((B).layout.hub+j.val)=((HUB).words j:Word W) :=
    (image.1 j).trans (congrArg (fun z : Hub => (z.words j:Word W)) hubEq)
  have go : (B).input ((B).layout.hub+6)=(dest 1:Word W) := by
    simpa only [build,groupBuild,groupHub,out,atNode] using image.2.1
  have link (i : Fin n) (j : Fin 4) : (B).input ((HUB).children+(4*i.val+j.val))=
      ((groupLink A m group node i.val).words j:Word W) := by
    simpa only [build,groupBuild,groupHub,Fin.val_cast,atNode] using image.2.2.1 (Fin.cast live.symm i) j
  have arg (i : Fin n) (j : Fin 3) : (B).input ((groupLink A m group node i.val).operand+j.val)=
      groupArgs A m group node i.val j := by
    simpa only [build,groupBuild,groupHub,Fin.val_cast,atNode] using image.2.2.2 (Fin.cast live.symm i) j
  have bound : n≤ if group then A.party.parties else A.party.motifs := live.ge.trans G.countCap
  have srcRun:=group_source A group node m N wire id read room sourceRoom bound shar gw go link hubFit keep
  have resultFit : dest 1<2^W:=by have:=sourceRoom.result;omega
  have bank:=group_banks A group node m N wire id read room held srcRun shar link arg
  have outInfo : (B).outputBase=dest 1 := by
    change ((B).input ((B).layout.hub+6)).val=_
    rw [go,Fin.val_cast_of_lt resultFit]
  have incoming (i : Fin n) (op : (ma i).op=10) : (ma i).split+arity i≤2^W := by
    by_cases yes : group=true
    · simpa only [mapRow,ite_eq_left yes] using space.copyRoom i yes
    · simp [mapRow,yes] at op
  have res:=(B).resident_of_banks N wire id qa ma bank (dest 0) (by have:=srcRun.small;omega)
    (fun i=>by cases group <;> simp [mapRow]) space.splitRoom space.room
    incoming
    space.maps space.cursorPins space.cursorRows space.streams space.pinCount (fun _=>⟨rfl,rfl,rfl⟩)
    (fun _=>rfl) space.words (Or.inr (by rw [outInfo,nextResult];exact Nat.add_le_add_left space.rowCount _))
  have result:=join_exec A group HUB N wire id qa ma (dest 0) m room.hubRoom stable srcRun res
  refine ⟨result.1,result.2,?_⟩
  have stay (x : ℕ) (hi : inLayout A group node m N x) : (B).reached jobs x=(B).input x :=
    (HistoryReadyTape.after_away _ _ _ x (keep x hi).1 (keep x hi).2).trans (prepFrame A group node m N room x hi).2.2
  have raw (j : Fin 6) : HistoryPartyBatchExec.numeric ((B).reached jobs) ((B).layout.hub+j.val)=(HUB).words j := by
    have key : inLayout A group node m N ((B).layout.hub+j.val) :=
      headLoc A group node m N (h:=h) (p:=p) j.castSucc
    change (((B).reached jobs) ((B).layout.hub+j.val)).val=_
    rw [stay _ key,gw,Fin.val_cast_of_lt (hubFit j)]
  have root:=disk A group node m N wire id read room srcRun.cap link stay
  have actualHead : let raw:=HistoryPartyBatchExec.numeric ((B).reached jobs)
      raw (B).layout.hub=dest 0 ∧ raw ((B).layout.hub+1)=p ∧ raw ((B).layout.hub+2)=h ∧ raw ((B).layout.hub+3)=n := by
    refine ⟨?_,raw 1,?_,raw 3⟩
    · have first := raw 0
      change HistoryPartyBatchExec.numeric ((B).reached jobs) ((B).layout.hub+0)=dest 0 at first
      exact first
    · exact (raw 2).trans shar
  have childRows (i : Fin n) : let r:=HistoryPartyBatchExec.numeric ((B).reached jobs)
      let root:=r (r ((B).layout.hub+4)+4*i.val)
      r (root+2)=(N i).cells ∧ r (root+3)=(N i).internal := by
    dsimp only
    have ch : HistoryPartyBatchExec.numeric ((B).reached jobs) ((B).layout.hub+4)=(HUB).children:=raw 4
    rw [ch]
    have pt:=root.links i (0:Fin 4)
    change HistoryPartyBatchExec.numeric ((B).reached jobs) ((HUB).children+(4*i.val+0))=src i 1 at pt
    rw [Nat.add_zero] at pt
    rw [pt]
    exact ⟨root.headers i 2,root.headers i 3⟩
  intro j
  have word := (B).result_info N jobs bound (dest 0) p h actualHead childRows j
  rw [outInfo] at word
  exact word


section Sectors
open HistoryScratch

local notation "M" => A.party.motifs
local notation "P" => A.party.parties
local notation "V" => A.party.V
local notation "start" => A.party.arena

def childLocal (i : Fin n) (col : ℕ) : Local := if group then
  ⟨A.party.motif+2,role A m i.val+2,2,col⟩ else ⟨i.val+2,0,3,col⟩
def parentLocal (col : ℕ) : Local := if group then ⟨A.party.motif+2,0,3,col⟩ else ⟨0,0,4,col⟩

/-- The two sorts of cells use disjoint geometric families inside S12.
These premises involve only the layout constants, live count and total emitted
rows/arity. They allow arbitrary subsets of the six active role bits. -/
structure Capacity : Prop where
  nodeBound : node<V^2
  sectors : (M+2)*(P+2)*8*32≤V
  motif : group=true→A.party.motif<M
  slots : group=false→n≤M
  roles : ∀ i : Fin n,group=true→ role A m i.val<P
  demand : ∀ i : Fin n,arity i≤V
  cells : 4*(∑ i,(N i).cells)≤V
  controlLower : start+V^4≤(B).control.val
  wordRoom : (B).control.val+V+2<2^W
  metadata : ∀ i r j,HistoryCompiledRows.metadata id (N i) r j<2^W

theorem childLocal_valid (C : Capacity A group node m N id (h:=h) (p:=p)) (i : Fin n) (j : Fin 4) :
    (childLocal A group m i j.val).Valid M P := by
  cases b:group
  · have z:=C.slots b
    have hi:=i.isLt;have hj:=j.isLt
    simp only [childLocal,Bool.false_eq_true,ite_false,Local.Valid];omega
  · have z:=C.motif b; have k:=C.roles i b;have hj:=j.isLt
    simp only [childLocal,ite_true,Local.Valid];omega

theorem parentLocal_valid (C : Capacity A group node m N id (h:=h) (p:=p)) (j : Fin 4) :
    (parentLocal A group j.val).Valid M P := by
  cases b:group
  · simp only [parentLocal,Bool.false_eq_true,ite_false,Local.Valid];have:=j.isLt;omega
  · have z:=C.motif b;simp only [parentLocal,ite_true,Local.Valid];have:=j.isLt;omega

theorem childLoc (i : Fin n) (b : ℕ) :
    sector A group node m i b=atWord start V M P node (childLocal A group m i b) 0 := by
  cases group <;> rfl

theorem rootLoc (j : ℕ) : dest j=atWord start V M P node (parentLocal A group j) 0 := by
  cases group <;> rfl

private theorem cellEnd (C : Capacity A group node m N id (h:=h) (p:=p)) (z : Local) (ok : z.Valid M P) :
    atWord start V M P node z 0+V≤ start+V^4 := by
  have room:=C.sectors
  have pos:0<V:=by
    have : 0<(M+2)*(P+2)*8*32:=by positivity
    omega
  have lastWord := HistoryScratch.fits (base := start) C.nodeBound C.sectors ok
    (show V - 1 < V by omega)
  unfold atWord at lastWord ⊢
  omega

private theorem cellApart (C : Capacity A group node m N id (h:=h) (p:=p)) (a b : Local)
    (ha : a.Valid M P) (hb : b.Valid M P) (ne : a≠b) :
    atWord start V M P node a 0+V≤atWord start V M P node b 0 ∨
    atWord start V M P node b 0+V≤atWord start V M P node a 0 := by
  let x:=atWord start V M P node a 0
  let y:=atWord start V M P node b 0
  change x+V≤y ∨ y+V≤x
  by_contra! bad
  have pos:0<V:=by omega
  by_cases hxy:x≤y
  · have offset : y-x<V := by omega
    have eq : atWord start V M P node a (y-x)=atWord start V M P node b 0 := by
      change x+(y-x)=y;omega
    exact ne (separated C.sectors ha hb offset pos eq).2.1
  · have offset : x-y<V := by omega
    have eq : atWord start V M P node a 0=atWord start V M P node b (x-y) := by
      change x=y+(x-y);omega
    exact ne (separated C.sectors ha hb pos offset eq).2.1

theorem physical_space (C : Capacity A group node m N id (h:=h) (p:=p)) :
    Space A group node m N id (h:=h) (p:=p) := by
  have live (i : Fin n) (col : ℕ) (inside : col < 4) : src i col + V ≤ start + V^4 := by
    rw [childLoc]
    exact cellEnd A group node m N id C _ (childLocal_valid A group node m N id C i ⟨col,inside⟩)
  have dst : dest 0+V≤ start+V^4:=by
    rw [rootLoc];exact cellEnd A group node m N id C _ (parentLocal_valid A group node m N id C 0)
  have endRow (i : Fin n) : (qa i).dest+4*(N i).cells≤dest 0+V := by
    have lt:=Tree.prefix_next_le (fun t=>(N t).cells) i
    have:=C.cells
    change dest 0+4*Tree.before (fun t=>(N t).cells) i+4*(N i).cells≤dest 0+V
    omega
  have endPins (i : Fin n) : (qa i).pins+arity i≤ start+V^4 := by
    have l:=live i 3 (by decide);have v:=C.demand i
    change src i 3+arity i≤_;omega
  have sub (i : Fin n) : 4*(N i).cells≤V := by
    have := Tree.prefix_next_le (fun t=>(N t).cells) i;have:=C.cells;omega
  have biggest:=C.controlLower;have word:=C.wordRoom
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,C.metadata,C.cells⟩
  · intro i;exact (endPins i).trans (by omega)
  · intro i _;have:=live i 2 (by decide);have:=C.demand i;omega
  · intro i
    change (if group then src i 2 else 2) < 2^W
    have copyEnd := live i 2 (by decide)
    split <;> omega
  · intro i j
    have ap:=cellApart A group node m N id C (childLocal A group m j 3) (parentLocal A group 0)
      (childLocal_valid A group node m N id C j 3) (parentLocal_valid A group node m N id C 0)
      (by
        intro same
        have sameFamily := congrArg Local.family same
        cases group <;> simp [childLocal,parentLocal] at sameFamily)
    rw [←childLoc,←rootLoc] at ap
    have row:=endRow i;have v:=C.demand j
    have lower:dest 0≤(qa i).dest:=Nat.le_add_right _ _
    change src j 3+arity j≤_ ∨ _≤ src j 3
    omega
  · intro i;right;exact (endPins i).trans biggest
  · intro i;right;exact (endRow i).trans (dst.trans biggest)
  · intro i;have a:=live i 0 (by decide);have b:=sub i;omega
  · intro i;have:=C.demand i;omega

end Sectors

open scoped Classical

/-- All fields in this chart are arithmetic properties of the actual arrays.
The four-word records for the selected children are supplied separately by the
induction over raw slots. -/
structure Chart : Prop where
  layout : LayoutRoom A group node m N (h:=h) (p:=p)
  ranges : Bounds A group node m N (h:=h) (p:=p)
  capacity : Capacity A group node m N id (h:=h) (p:=p)
  source : SourceBounds A group node m N wire id
  headerReads : HistoryPartyBatchExec.Protected (joinHeader A W group) m (A.party.seed+64) (HistoryMotifJoin.rows A W group).length
  cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W)
  ports : let R:=HistoryGatherBody.selected A m
    R.oldBits+R.newBits=(p:Word W)
  free : group=true→m (((A.privateStarts+8:ℕ):Word W).val)=(h:Word W)
  active : group=true→n=Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}
  dense : group=false→HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3=(n:Word W)
  size : n≤ if group then A.party.parties else A.party.motifs
  maskRoom : 2^A.party.parties<2^W
  infoRoom : ∀ i : Fin n,src i 1+1<2^W
  hubFit : ∀ j : Fin 6,(HUB).words j<2^W
  retained : ∀ x,inLayout A group node m N x→x≠(B).control.val ∧ ∀ j∈jobs,x<j.start ∨ j.finish≤x

section ChartWindows
open HistoryScratch
local notation "V₀" => A.party.V
local notation "cacheEnd" => A.party.arena+V₀^4
local notation "lim" => (if group then A.party.parties else A.party.motifs)
local notation "seed" => A.party.seed
local notation "cmd" => A.party.commands
local notation "arg" => A.party.arguments

/-- Recover both join controllers' read protection and all descriptor bounds from
the real order of the cache, header, command and argument intervals. -/
theorem Chart.of_windows (C : Capacity A group node m N id (h:=h) (p:=p))
    (positive : 4≤V₀) (cache : cacheEnd≤ seed) (control : (B).control.val=seed+7)
    (ncap : n≤lim) (hdrEnd : seed+64+7+7*lim+4≤cmd)
    (cmdEnd : cmd+14*n≤arg) (argEnd : arg+7*n<2^W)
    (dim : p<2^W ∧ h<2^W ∧ ∀ i,(N i).internal<2^W)
    (protectedHeader : HistoryPartyBatchExec.Protected (joinHeader A W group) m
      (seed+64) (HistoryMotifJoin.rows A W group).length)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (ports : let R:=HistoryGatherBody.selected A m; R.oldBits+R.newBits=(p:Word W))
    (free : group=true→m (((A.privateStarts+8:ℕ):Word W).val)=(h:Word W))
    (active : group=true→n=Fintype.card {j : Fin A.party.parties // selectedBit A m j.val})
    (dense : group=false→HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3=(n:Word W))
    (maskRoom : 2^A.party.parties<2^W) : Chart A group node m N wire id := by
  have shape:=HistoryMotifJoin.rows_len (W:=W) A group
  have chi (i : Fin n) (j : Fin 4) : src i j.val+V₀≤cacheEnd := by
    rw [childLoc];exact cellEnd A group node m N id C _ (childLocal_valid A group node m N id C i j)
  have dst (j : Fin 4) : dest j.val+V₀≤cacheEnd := by
    rw [rootLoc];exact cellEnd A group node m N id C _ (parentLocal_valid A group node m N id C j)
  have span (i : Fin n) : 4*Tree.before (fun t=>(N t).cells) i+4*(N i).cells≤V₀ := by
    have:=Tree.prefix_next_le (fun t=>(N t).cells) i;have:=C.cells;omega
  have c4 (i : Fin n) : 4*(N i).cells≤V₀:=by have:=span i;omega
  have endMap (i : Fin n) : (qa i).pins+arity i≤cacheEnd:=by
    exact (Nat.add_le_add_left (C.demand i) (src i 3)).trans (chi i 3)
  have endRows (i : Fin n) : (qa i).dest+4*(N i).cells≤dest 0+V₀:=by
    change dest 0+4*Tree.before (fun t=>(N t).cells) i+4*(N i).cells≤_;have:=span i;omega
  have jobEnd {j : HistoryReadyTape.Job W} (hj : j∈jobs) : j.finish≤cacheEnd := by
    obtain ⟨i,_,mem⟩:=List.mem_flatMap.mp hj
    rcases (by simpa only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] using mem :
      j=⟨(qa i).pins,arity i,_⟩ ∨ j=⟨(qa i).dest,4*(N i).cells,_⟩) with rfl|rfl
    · exact endMap i
    · exact (endRows i).trans (dst 0)
  have childClass {x} (hx : inChild A group node m N x) :
      ∃ (i : Fin n) (b : Fin 3),src i b.val≤x ∧ x<src i b.val+V₀ := by
    obtain ⟨i,hx⟩:=hx
    rcases hx with h₀|h₁|h₂
    · exact ⟨i,0,h₀.1,h₀.2.trans_le (Nat.add_le_add_left (c4 i) _)⟩
    · exact ⟨i,1,h₁.1,h₁.2.trans_le (Nat.add_le_add_left positive _)⟩
    · exact ⟨i,2,h₂.2.1,h₂.2.2.trans_le (Nat.add_le_add_left (C.demand i) _)⟩
  have childLow {x} (hx : inChild A group node m N x) : x<seed:=by
    obtain ⟨i,b,lo,hi⟩:=childClass hx
    exact hi.trans_le ((chi i (Fin.castLE (by decide : 3≤4) b)).trans cache)
  have headerLow {x} (hx : inLayout A group node m N x) : x<cmd:=by
    rcases hx with h|h
    · omega
    · have:=childLow h;omega
  have childSeparate (i : Fin n) (b : Fin 3) (j : Fin n) :
      src i b.val+V₀≤ src j 3 ∨ src j 3+V₀≤ src i b.val := by
    let b' := Fin.castLE (by decide : 3≤4) b
    have eq:=cellApart A group node m N id C _ _
      (childLocal_valid A group node m N id C i b') (childLocal_valid A group node m N id C j 3)
      (by cases group <;> simp [childLocal,b']; all_goals omega)
    simpa only [←childLoc,b',Fin.val_castLE,show (3 : Fin 4).val = 3 from rfl] using eq
  have rootSeparate (i : Fin n) (b : Fin 3) (k : Fin 4) :
      src i b.val+V₀≤dest k.val ∨ dest k.val+V₀≤ src i b.val := by
    let b' := Fin.castLE (by decide : 3≤4) b
    have eq:=cellApart A group node m N id C _ _
      (childLocal_valid A group node m N id C i b') (parentLocal_valid A group node m N id C k)
      (by cases group <;> simp [childLocal,parentLocal])
    simpa only [←childLoc,←rootLoc,b',Fin.val_castLE] using eq
  have childCache (i : Fin n) (k : ℕ) (hk : k<4) : src i k+V₀≤cacheEnd :=
    chi i ⟨k,hk⟩
  have rootCache0 : dest 0+V₀≤cacheEnd := dst 0
  have rootCache1 : dest 1+V₀≤cacheEnd := dst 1
  have highProtect (x : ℕ) (past : seed+7<x) : (B).protectedAt N qa x := by
    refine ⟨by omega,fun i=>⟨Or.inr (by have:=endMap i;omega),
      Or.inr (by have:=endRows i;omega)⟩⟩
  have lowProtect {x} (hx : inChild A group node m N x) : (B).protectedAt N qa x := by
    have low:=childLow hx
    obtain ⟨i,b,lo,hi⟩:=childClass hx
    refine ⟨by omega,fun j=>⟨?_,?_⟩⟩
    · have ap:=childSeparate i b j
      have:=C.demand j
      change x<src j 3 ∨ src j 3+arity j≤x;omega
    · have ap : src i b.val+V₀≤dest 0 ∨ dest 0+V₀≤ src i b.val := rootSeparate i b 0
      have:=endRows j
      change x<dest 0+4*Tree.before (fun t=>(N t).cells) j ∨ _;omega
  have allProtect {x} (hx : inLayout A group node m N x) : (B).protectedAt N qa x := by
    rcases hx with h|h
    · exact highProtect x (by omega)
    · exact lowProtect h
  have inJob {x} (safe : (B).protectedAt N qa x) {j : HistoryReadyTape.Job W} (hj : j∈jobs) :
      x<j.start ∨ j.finish≤x := by
    obtain ⟨i,_,mem⟩:=List.mem_flatMap.mp hj
    change j ∈ Tape.jobs N wire id (qa i) i at mem
    simp only [Tape.jobs,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact (safe.2 i).1
    · exact (safe.2 i).2
  have fitInfo (i : Fin n) (j : Fin 4) :
      (Info.mk (src i 0) (arity i) (N i).cells (N i).internal).words j<2^W := by
    have:=childCache i 0 (by decide);have:=c4 i;have:=C.demand i;have:=dim.2.2 i
    fin_cases j <;> change _<2^W <;> simp [Info.words] <;> omega
  have fitLink (i : Fin n) (j : Fin 4) : (groupLink A m group node i.val).words j<2^W := by
    have:=childCache i 1 (by decide);have:=childCache i 3 (by decide);have:=i.isLt
    fin_cases j
    · change src i 1<2^W;omega
    · change src i 3<2^W;omega
    · change (if group then 10 else 11)<2^W;split <;> omega
    · change seed+64+7+4*lim+3*i.val<2^W;omega
  have L : LayoutRoom A group node m N (h:=h) (p:=p) := by
    refine ⟨by rw [shape];omega,fitInfo,fitLink,?_,?_,?_,?_⟩
    · intro x hx;exact Or.inl ((childLow hx).trans_le (by omega))
    · intro x hx;change x<seed ∨ seed+9≤x
      rcases hx with h|h
      · right;omega
      · exact Or.inl (childLow h)
    · intro x hx;exact Or.inl (headerLow hx)
    · intro x hx;exact Or.inl ((headerLow hx).trans_le (by omega : cmd≤arg))
  have G : Bounds A group node m N (h:=h) (p:=p) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro i b j;apply highProtect;change seed+7<cmd+_;omega
    · intro i j;apply highProtect;change seed+7<seed+64+7+4*lim+3*i.val+j.val;omega
    · intro i j;apply highProtect;change seed+7<arg+_;omega
    · intro i r j;apply lowProtect
      exact ⟨i,Or.inl ⟨by omega,by have:=r.isLt;have:=j.isLt;omega⟩⟩
    · intro i g j;apply lowProtect
      exact ⟨i,Or.inr (Or.inr ⟨g,by omega,by have:=j.isLt;omega⟩)⟩
    · intro i;change seed+64+7+4*lim+3*i.val+4<2^W;have:=i.isLt;omega
  have S : SourceBounds A group node m N wire id := by
    refine ⟨by omega,by omega,by change seed+9<2^W;omega,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact ⟨by change seed+9≤cmd;omega,cmdEnd⟩
    · change cmd+14*n<2^W;omega
    · exact argEnd
    · change seed+64+7+4*n≤2^W;omega
    · intro i;have:=childCache i 1 (by decide);omega
    · omega
    · intro x hx
      rcases hx with hdr|ch
      · right;omega
      · obtain ⟨i,b,lo,hi⟩:=childClass ch
        have ap : src i b.val+V₀≤dest 1 ∨ dest 1+V₀≤ src i b.val := rootSeparate i b 1
        omega
    · constructor <;> intro j hj <;> left
      · exact (jobEnd hj).trans cache
      · exact (jobEnd hj).trans (by change cacheEnd≤cmd;omega)
    · intro j hj;have:=jobEnd hj;omega
  refine ⟨L,G,C,S,protectedHeader,cursor,ports,free,active,dense,ncap,maskRoom,?_,?_,?_⟩
  · intro i;have:=childCache i 1 (by decide);omega
  · intro j;obtain ⟨pr,hr,_⟩:=dim
    fin_cases j
    · change dest 0<2^W;omega
    · exact pr
    · change (if group then h else 0)<2^W;split <;> omega
    · change n<2^W;omega
    · change seed+64+7<2^W;omega
    · change arg<2^W;omega
  · intro x hx;have z:=allProtect hx
    exact ⟨z.1,fun _ hj=>inJob z hj⟩

end ChartWindows

end

end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
