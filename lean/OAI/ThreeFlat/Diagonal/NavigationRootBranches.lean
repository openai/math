import OAI.ThreeFlat.Diagonal.NavigationRootOwners
import OAI.ThreeFlat.Diagonal.HistoryBucketRows
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # Reading terminal charges and publishing root-group and ancestor directories -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open HistoryContraction RAM.PhysicalPinsExpr RAM.DescriptorExpr
open scoped BigOperators Fin.CommRing

variable {W : ℕ}

/-- The preceding native chronological stage writes only work/pair counts and parent
addresses needed for root publication. Initial lane ids are the first chronological ids. -/
structure Nodes (a : RootArchive) where
  chronology : HistoryNodeDirectory.Chronology (a.firstFinal+a.rootCount)
  first : chronology.firstFinal=a.firstFinal
  work : Fin a.rootCount→ℕ
  pairs : Fin a.rootCount→ℕ

def Nodes.Stored {a : RootArchive} (N : Nodes a) (m : Memory W) :=
  (∀ i : Fin a.rootCount,m (a.nodeBank.charges+2*(a.firstFinal+i.val))=(N.work i : Word W) ∧
    m (a.nodeBank.charges+2*(a.firstFinal+i.val)+1)=(N.pairs i : Word W)) ∧
  (∀ i : Fin (a.firstFinal+a.rootCount),i.val<a.firstFinal →
    m (a.nodeBank.nodes+8*i.val+1)=((N.chronology.parent i).val:Word W))

def clipped (a : RootArchive) (i : ℕ) := min (i*a.pairsPerLane) a.totalPairs

def lane (a : RootArchive) (i : Fin a.initialLanes) : Bucket (Fin a.initialLanes) :=
  ⟨i,clipped a i.val,clipped a (i.val+1)⟩

def countWord {a : RootArchive} (N : Nodes a) (i : ℕ) (j : Fin 2) :=
  if h : i<a.rootCount then (![N.work ⟨i,h⟩,N.pairs ⟨i,h⟩] : Fin 2→ℕ) j else 0

def workBefore {a : RootArchive} (N : Nodes a) (i : ℕ) :=
  ∑ j ∈ Finset.range i,countWord N j 0

theorem countWord_work {a : RootArchive} (N : Nodes a) (i : Fin a.rootCount) :
    countWord N i.val 0=N.work i := by simp [countWord,i.isLt]

@[simp] theorem workBefore_succ {a : RootArchive} (N : Nodes a) (i : ℕ) :
    workBefore N (i+1)=workBefore N i+countWord N i 0 := Finset.sum_range_succ _ _

def summaryHeader (a : RootArchive) (N : Nodes a) : NavigationHeader :=
  ⟨a.initialLanes,a.rootCount,workBefore N a.rootCount,a.stageCount⟩

def rootWords (a : RootArchive) : Fin 3→ℕ := ![a.firstFinal,a.nodeBank.nodes,a.childArena]

/-- The natural work rows in directory 0 come from the terminal segment of S43. -/
theorem charge_value (a : RootArchive) (N : Nodes a) (m : Memory W) (input : N.Stored m)
    (i : Fin a.rootCount) (j : Fin 2)
    (large : directory a.age 0+2*a.rootCount<2^W)
    (room : a.nodeBank.charges+2*(a.firstFinal+a.rootCount)≤2^W) :
    let x := directory a.age 0+2*i.val+j.val
    (HeaderScan.closed a.rootCharges : Term W 0 1).eval Fin.elim0 m (fun _=>(x:Word W))=
      (countWord N i.val j:Word W) := by
  dsimp only
  let x:=directory a.age 0+2*i.val+j.val
  have hi := i.isLt
  have hj := j.isLt
  have bound : x<2^W := by dsimp [x]; omega
  let f := a.rootCharges
  let d := directory a.age 0
  have loc : x-d=2*i.val+j.val := by dsimp [x,d]; omega
  have fit : f.Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>x) := by
    simp only [f,rootCharges,MotifRows.plus,Formula.Fits,Formula.natural,natOp,opFits]
    repeat' first | constructor | omega
  have val := Formula.value_eq_natural f (fun _=>0) (fun z=>(m z).val) (fun _=>x) fit
  have read : (f.natural W (fun _=>0) (fun z=>(m z).val) (fun _=>x):Word W)=(countWord N i.val j:Word W) := by
    change ((m (a.nodeBank.charges+2*a.firstFinal+(x-d))).val:Word W)=_
    rw [loc,Fin.cast_val_eq_self]
    have both:=input.1 i
    fin_cases j
    · simpa [countWord,i.isLt,Nat.mul_add,Nat.add_assoc] using both.1
    · simpa [countWord,i.isLt,Nat.mul_add,Nat.add_assoc] using both.2
  simpa only [HeaderScan.eval_closed,Fin.cast_val_eq_self,Nat.cast_zero,f] using val.trans read

theorem readNatural (f : Formula 1) (m : Memory W) (z : ℕ)
    (ok : f.Fits W (fun _=>0) (fun i=>(m i).val) (fun _=>z)) :
    (HeaderScan.closed f : Term W 0 1).eval Fin.elim0 m (fun _=>(z:Word W))=
      (f.natural W (fun _=>0) (fun i=>(m i).val) (fun _=>z):Word W) := by
  rw [HeaderScan.eval_closed]
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self] using
    f.value_eq_natural (fun _=>0) (fun i=>(m i).val) (fun _=>z) ok


def outHeader (a : RootArchive) (m : Memory W) :=
  m a.current=(a.header:Word W) ∧ ∀ i : Fin 22,m (a.header+i.val)=(a.word i.val:Word W)


def scanCost (f : Formula 1) (n : ℕ) := 11+n*(2*f.work+4)

theorem scan_spec (a : RootArchive) (f : Formula 1) (off n lo : ℕ)
    (m : Memory W) (word : ℕ→Word W) (base : a.word off=lo) (num : a.word (off+1)=n)
    (ix : off+1<22) (headers : a.outHeader m) (headerFit : a.header+22<2^W)
    (currentFit : a.current<2^W) (bound : lo+n<2^W)
    (effect : ∀ i<n,(HeaderScan.closed f : Term W 0 1).eval Fin.elim0
      (fillSegment lo i word m) (fun _=>((lo+i:ℕ):Word W))=word (lo+i)) :
    (a.scan off f).Spec (·=m) (fun _ out=>out=fillSegment lo n word m) (scanCost f n) := by
  have hdr (j : ℕ) (hj : j<22) : HeaderScan.headerWord m (a.current:Word W) j=(a.word j:Word W) := by
    unfold HeaderScan.headerWord
    rw [Fin.val_cast_of_lt currentFit,headers.1,←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
    exact headers.2 ⟨j,hj⟩
  unfold scan scanCost
  rw [← HeaderScan.binds_closed (w := W) f]
  intro programSize registerSize slotCount machine
  exact HeaderScan.prefix_spec (a.current:Word W) off (off+1) lo n (HeaderScan.closed f) m word
    bound (by rw [hdr off (by omega),base,Fin.val_cast_of_lt (by omega)])
    (by rw [hdr (off+1) ix,num,Fin.val_cast_of_lt (by omega)]) effect machine


def outside (lo n z : ℕ) := z<lo ∨ lo+n≤z

theorem fill_frame (m : Memory W) (f : ℕ→Word W) (lo n z : ℕ) (h : outside lo n z) :
    fillSegment lo n f m z=m z := by
  simp [fillSegment,show ¬ (lo≤z ∧ z<lo+n) by dsimp [outside] at h;omega]

theorem fill_header (a : RootArchive) (m : Memory W) (f : ℕ→Word W)
    (lo n : ℕ) (h : a.outHeader m) (ctrl : outside lo n a.current)
    (hdr : a.header+22≤lo ∨ lo+n≤a.header) : a.outHeader (fillSegment lo n f m) := by
  refine ⟨(fill_frame m f lo n a.current ctrl).trans h.1,fun i=>?_⟩
  rw [fill_frame m f lo n (a.header+i.val) (by dsimp [outside];have:=i.isLt;omega)]
  exact h.2 i



end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open RAM.PhysicalPinsExpr RAM.DescriptorExpr RAM.TickGreedySweep RAM.TickGreedyNat LinearAlgebra.SpectralBooks.VNP
open scoped BigOperators Fin.CommRing Classical

variable {W : ℕ}

inductive StageBank | charges | sums | stats | desc deriving DecidableEq

def lower (a : RootArchive) : StageBank→ℕ
  | .charges=>a.chargeBase | .sums=>a.prefixes | .stats=>a.statsBase | .desc=>a.descBase

def extent (a : RootArchive) : StageBank→ℕ
  | .charges=>2*a.rootCount | .sums=>a.rootCount+1 | .stats=>8 | .desc=>3

def content (a : RootArchive) (N : Nodes a) (b : StageBank) (z : ℕ) : Word W :=
  let t:=z-a.lower b
  match b with
  | .charges=>(countWord N (t/2) ⟨t%2,Nat.mod_lt _ (by decide)⟩:Word W)
  | .sums=>(workBefore N t:Word W)
  | .stats=>((a.summaryHeader N).words a.age (Fin.ofNat 8 t):Word W)
  | .desc=>(a.rootWords (Fin.ofNat 3 t):Word W)

def filled (a : RootArchive) (N : Nodes a) (b : StageBank) (m : Memory W) :=
  fillSegment (a.lower b) (a.extent b) (a.content N b) m

def rootFormula (a : RootArchive) : Formula 1 :=
  pick [.lit a.firstFinal,.lit a.nodeBank.nodes,.lit a.childArena] (.cut (.reg 0) (.lit a.descBase))

def branchImage (a : RootArchive) (N : Nodes a) (m : Memory W) :=
  a.filled N .desc (a.filled N .stats (a.filled N .sums (a.filled N .charges m)))

def branchROM (a : RootArchive) : Procedure W :=
  (a.scan 0 a.rootCharges).seq ((a.scan 2 a.prefix).seq
    ((a.scan 5 a.meta).seq ((a.scan 7 a.rootFormula).seq (a.partition.seq a.ancestors))))

def branchCost (a : RootArchive) :=
  scanCost a.rootCharges (2*a.rootCount)+(scanCost a.prefix (a.rootCount+1)+
    (scanCost a.meta 8+(scanCost a.rootFormula 3+(19+24*a.rootCount+(12+11*(a.firstFinal+a.rootCount))))))

structure BranchRoom (a : RootArchive) (W : ℕ) : Prop where
  bound : ∀ b, a.lower b+a.extent b<2^W
  header : a.header+22<2^W
  current : a.current<2^W
  charges : a.nodeBank.charges+2*(a.firstFinal+a.rootCount)≤2^W
  between : ∀ b c : StageBank,b≠c → a.lower b+a.extent b≤a.lower c ∨ a.lower c+a.extent c≤a.lower b
  cursorFree : ∀ b,outside (a.lower b) (a.extent b) a.current
  headerFree : ∀ b,a.header+22≤a.lower b ∨ a.lower b+a.extent b≤a.header
  archiveFree : ∀ b z, (a.nodeBank.charges+2*a.firstFinal≤z ∧ z<a.nodeBank.charges+2*(a.firstFinal+a.rootCount)) ∨
    (a.nodeBank.nodes≤z ∧ z<a.nodeBank.nodes+8*a.firstFinal) → outside (a.lower b) (a.extent b) z

private theorem typedWord (lo len : ℕ) (f : ℕ→Word W) (m : Memory W) {i : ℕ} (hi : i<len) :
    fillSegment lo len f m (lo+i)=f (lo+i) := by simp [fillSegment,hi]

theorem otherWord (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    {b c : StageBank} (ne : b≠c) (z : ℕ) (lo : a.lower c≤z) (hi : z<a.lower c+a.extent c) :
    a.filled N b m z=m z :=
  fill_frame m (a.content N b) (a.lower b) (a.extent b) z
    (by have := r.between b c ne; dsimp [outside]; omega)

private theorem nodes_preserved (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (b : StageBank) (k : ℕ) (hk : k≤a.extent b) (h : N.Stored m) :
    N.Stored (fillSegment (a.lower b) k (a.content N b) m) := by
  have keep (z : ℕ) (hz : (a.nodeBank.charges+2*a.firstFinal≤z ∧ z<a.nodeBank.charges+2*(a.firstFinal+a.rootCount)) ∨
      (a.nodeBank.nodes≤z ∧ z<a.nodeBank.nodes+8*a.firstFinal)) :
      fillSegment (a.lower b) k (a.content N b) m z=m z := by
    have big := r.archiveFree b z hz
    apply fill_frame
    unfold outside at *
    omega
  refine ⟨?_,?_⟩
  · intro i
    have hi := i.isLt
    exact ⟨(keep _ (Or.inl (by omega))).trans (h.1 i).1,(keep _ (Or.inl (by omega))).trans (h.1 i).2⟩
  · intro i hi
    exact (keep _ (Or.inr (by omega))).trans (h.2 i hi)

private theorem keptHeader (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (b : StageBank)
    (m : Memory W) (head : a.outHeader m) : a.outHeader (a.filled N b m) :=
  fill_header a m (a.content N b) (a.lower b) (a.extent b) head (r.cursorFree b) (r.headerFree b)

private theorem chargeAt (a : RootArchive) (N : Nodes a) (m : Memory W) (i : Fin a.rootCount) (j : Fin 2) :
    a.filled N .charges m (a.chargeBase+2*i.val+j.val)=(countWord N i.val j:Word W) := by
  have hj:=j.isLt
  have hi:=i.isLt
  rw [show a.chargeBase+2*i.val+j.val=a.chargeBase+(2*i.val+j.val) by omega]
  change fillSegment a.chargeBase (2*a.rootCount) (a.content N .charges) m
    (a.chargeBase+(2*i.val+j.val))=_
  rw [typedWord a.chargeBase (2*a.rootCount) (a.content N .charges) m
    (show 2*i.val+j.val<2*a.rootCount by omega)]
  have div : (2*i.val+j.val)/2=i.val := by omega
  have mod : (2*i.val+j.val)%2=j.val := by omega
  simp only [content,lower,Nat.add_sub_cancel_left,div,mod]

theorem charge_scan (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (h : N.Stored m) (header : a.outHeader m) :
    (a.scan 0 a.rootCharges).Spec (·=m) (fun _ out=>out=a.filled N .charges m) (scanCost a.rootCharges (2*a.rootCount)) := by
  apply scan_spec a a.rootCharges 0 (2*a.rootCount) a.chargeBase m
    (a.content N .charges) rfl rfl (by decide) header r.header r.current (r.bound .charges)
  intro k hk
  let i : Fin a.rootCount:=⟨k/2,by omega⟩
  let j : Fin 2:=⟨k%2,Nat.mod_lt _ (by decide)⟩
  have coord : a.chargeBase+k=directory a.age 0+2*i.val+j.val := by dsimp [i,j,chargeBase];omega
  have input:=nodes_preserved a N r m .charges k (by exact hk.le) h
  have val:=charge_value a N _ input i j (r.bound .charges) r.charges
  change _=a.content N .charges (a.chargeBase+k)
  simpa only [←coord,content,lower,Nat.add_sub_cancel_left,i,j] using val

theorem sum_scan (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (header : a.outHeader m)
    (charges : ∀ i : Fin a.rootCount,m (a.chargeBase+2*i.val)=(N.work i:Word W)) :
    (a.scan 2 a.prefix).Spec (·=m) (fun _ out=>out=a.filled N .sums m) (scanCost a.prefix (a.rootCount+1)) := by
  apply scan_spec a a.prefix 2 (a.rootCount+1) a.prefixes m (a.content N .sums) rfl rfl (by decide)
    header r.header r.current (r.bound .sums)
  intro k hk
  let μ:=fillSegment a.prefixes k (a.content N .sums) m
  have pf : a.prefixes+(a.rootCount+1)<2^W:=r.bound .sums
  have cf : a.chargeBase+2*a.rootCount<2^W:=r.bound .charges
  have chargeRoom : directory a.age 0+2*a.rootCount<2^W := cf
  have delta : a.prefixes+k-a.prefixes=k := Nat.add_sub_cancel_left ..
  have valid : a.prefix.Fits W (fun _=>0) (fun z=>(μ z).val) (fun _=>a.prefixes+k) := by
    simp only [RootArchive.prefix,ix,MotifRows.plus,Formula.Fits,Formula.natural,natOp,opFits,natTest,delta,
      decide_eq_true_eq,Nat.add_zero]
    split_ifs <;> repeat' first | constructor | omega
  change (HeaderScan.closed a.prefix : Term W 0 1).eval Fin.elim0 μ (fun _=>((a.prefixes+k:ℕ):Word W)) = a.content N .sums (a.prefixes+k)
  rw [readNatural _ μ _ valid]
  simp only [RootArchive.prefix,Formula.natural,natTest,ix,natOp,MotifRows.plus,delta,decide_eq_true_eq,
    Nat.add_zero,content,lower]
  cases k with
  | zero => simp [workBefore]
  | succ k =>
    have bound : k<a.rootCount:=by omega
    let i : Fin a.rootCount:=⟨k,bound⟩
    have prev : μ (a.prefixes+(k+1)-1)=(workBefore N k:Word W) := by
      have addr : a.prefixes+(k+1)-1=a.prefixes+k := by omega
      rw [addr]
      exact (typedWord a.prefixes (k+1) (a.content N .sums) m (by omega : k<k+1)).trans
        (by simp [content,lower])
    have other:=r.between .charges .sums (by decide)
    change a.chargeBase+2*a.rootCount≤a.prefixes ∨ a.prefixes+(a.rootCount+1)≤a.chargeBase at other
    have width : μ (a.chargeBase+k*2)=(countWord N k 0:Word W) := by
      rw [show a.chargeBase+k*2=a.chargeBase+2*i.val by dsimp [i];omega]
      exact (fill_frame m (a.content N .sums) a.prefixes (k+1) _ (by unfold outside;dsimp [i];omega)).trans
        ((charges i).trans (congrArg (fun z : ℕ=>(z:Word W)) (countWord_work N i).symm))
    have widthAt : μ (directory a.age 0 + k*2) = (countWord N k 0 : Word W) := width
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,Nat.cast_add,Fin.cast_val_eq_self,
      prev,widthAt,workBefore_succ]

private theorem pickNat (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (total : m (a.prefixes+a.rootCount)=(workBefore N a.rootCount:Word W)) (i : Fin 8) :
    (HeaderScan.closed a.meta : Term W 0 1).eval Fin.elim0 m (fun _=>((a.statsBase+i.val:ℕ):Word W))=
      ((a.summaryHeader N).words a.age i:Word W) := by
  have bound : TickWorkspace.base a.age 6+8<2^W:=r.bound .stats
  have pf : a.prefixes+(a.rootCount+1)<2^W:=r.bound .sums
  have fit : a.meta.Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>a.statsBase+i.val) := by
    have hi := i.isLt
    have addrRoom : TickWorkspace.base a.age 6+i.val<2^W := by omega
    have baseRoom : TickWorkspace.base a.age 6<2^W := by omega
    have indexRoom : i.val<2^W := by omega
    have prefixRoom : a.prefixes+a.rootCount<2^W := by omega
    have literalRoom (j : ℕ) (hj : j<8) : j<2^W := by omega
    simp [RootArchive.meta,pick,statsBase,Formula.Fits,Formula.natural,addrRoom,baseRoom,indexRoom,
      prefixRoom,literalRoom 1 (by decide),literalRoom 2 (by decide),literalRoom 3 (by decide),
      literalRoom 4 (by decide),literalRoom 5 (by decide),literalRoom 6 (by decide),literalRoom 7 (by decide)]
  rw [readNatural _ _ _ fit]
  have wrap : ((workBefore N a.rootCount % 2^W : ℕ) : Word W)=(workBefore N a.rootCount : Word W) := by
    apply Fin.ext
    simp
  fin_cases i <;> simp [RootArchive.meta,pick,Formula.natural,natTest,statsBase,summaryHeader,
    NavigationHeader.words,total,wrap]

private theorem descNat (a : RootArchive) (r : BranchRoom a W) (m : Memory W) (i : Fin 3) :
    (HeaderScan.closed a.rootFormula : Term W 0 1).eval Fin.elim0 m (fun _=>((a.descBase+i.val:ℕ):Word W))=
      (a.rootWords i:Word W) := by
  have bound : a.descBase+3<2^W:=r.bound .desc
  have hi:=i.isLt
  have fit : a.rootFormula.Fits W (fun _=>0) (fun z=>(m z).val) (fun _=>a.descBase+i.val) := by
    have addrRoom : a.descBase+i.val<2^W := by omega
    have baseRoom : a.descBase<2^W := by omega
    have indexRoom : i.val<2^W := by omega
    have oneRoom : 1<2^W := by omega
    have twoRoom : 2<2^W := by omega
    simp [rootFormula,pick,Formula.Fits,Formula.natural,addrRoom,baseRoom,indexRoom,
      oneRoom,twoRoom]
  rw [readNatural _ _ _ fit]
  fin_cases i <;> simp [rootFormula,pick,Formula.natural,natTest,rootWords]

theorem stats_scan (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (head : a.outHeader m) (total : m (a.prefixes+a.rootCount)=(workBefore N a.rootCount:Word W)) :
    (a.scan 5 a.meta).Spec (·=m) (fun _ out=>out=a.filled N .stats m) (scanCost a.meta 8) := by
  apply scan_spec a a.meta 5 8 a.statsBase m (a.content N .stats) rfl rfl (by decide) head r.header r.current
    (r.bound .stats)
  intro k hk
  let i : Fin 8:=⟨k,hk⟩
  let μ:=fillSegment a.statsBase k (a.content N .stats) m
  have between:=r.between .stats .sums (by decide)
  change a.statsBase+8≤a.prefixes ∨ a.prefixes+(a.rootCount+1)≤a.statsBase at between
  have rd : μ (a.prefixes+a.rootCount)=(workBefore N a.rootCount:Word W) :=
    (fill_frame _ _ _ _ _ (by unfold outside;omega)).trans total
  exact (pickNat a N r μ rd i).trans (by simp [content,lower,i,Fin.ofNat,Nat.mod_eq_of_lt hk])

theorem desc_scan (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W)
    (head : a.outHeader m) :
    (a.scan 7 a.rootFormula).Spec (·=m) (fun _ out=>out=a.filled N .desc m) (scanCost a.rootFormula 3) := by
  apply scan_spec a a.rootFormula 7 3 a.descBase m (a.content N .desc) rfl rfl
    (by decide) head r.header r.current (r.bound .desc)
  intro k hk
  let i : Fin 3:=⟨k,hk⟩
  exact (descNat a r _ i).trans (by simp [content,lower,i,Fin.ofNat,Nat.mod_eq_of_lt hk])



end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.NavigationNodeRows RAM.TickPhysicalABI
open RAM.TickGreedySweep RAM.TickGreedyNat RAM.PhysicalPinsExpr LinearAlgebra.SpectralBooks.VNP
open scoped BigOperators Fin.CommRing Classical

variable {W : ℕ}

def ids (a : RootArchive) := List.ofFn (fun i : Fin a.rootCount=>i)

theorem ticks_workBefore (a : RootArchive) (N : Nodes a) :
    Team.ticks N.work a.ids=workBefore N a.rootCount := by
  simp only [Team.ticks,ids,List.map_ofFn,List.sum_ofFn,Function.comp_apply,workBefore]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have lt:=Finset.mem_range.mp hj
  simp [countWord,lt]

private theorem persists (a : RootArchive) (r : BranchRoom a W) (N : Nodes a) (m : Memory W)
    {b c : StageBank} (ne : b≠c) (i : ℕ) (h : i<a.extent c) :
    a.filled N b m (a.lower c+i)=m (a.lower c+i) :=
  otherWord a N r m ne _ (by omega) (by omega)

private theorem generated (a : RootArchive) (N : Nodes a) (b : StageBank) (m : Memory W)
    (i : ℕ) (hi : i<a.extent b) : a.filled N b m (a.lower b+i)=a.content N b (a.lower b+i) :=
  typedWord (a.lower b) (a.extent b) (a.content N b) m hi

def rootsReady (a : RootArchive) (N : Nodes a) (m : Memory W) :=
  (a.summaryHeader N).stored a.age m ∧ (∀ j : Fin 3,m (a.descBase+j.val)=(a.rootWords j:Word W)) ∧
    (∀ (i : Fin a.rootCount) (j : Fin 2),m (a.chargeBase+2*i.val+j.val)=(countWord N i.val j:Word W)) ∧
    N.Stored m

theorem branch_ready (a : RootArchive) (N : Nodes a) (r : BranchRoom a W) (m : Memory W) (h : N.Stored m) :
    a.rootsReady N (a.branchImage N m) := by
  let c:=a.filled N .charges m
  let s:=a.filled N .sums c
  let t:=a.filled N .stats s
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    change a.filled N .desc t (a.lower .stats+i.val)=_
    rw [persists a r N t (by decide : StageBank.desc≠.stats) _ i.isLt,
      show t (a.lower .stats+i.val)=_ from generated a N .stats s i.val i.isLt]
    simp [content,lower,Fin.ofNat,Nat.mod_eq_of_lt i.isLt]
  · intro i
    change a.filled N .desc t (a.lower .desc+i.val)=_
    rw [generated a N .desc t i.val i.isLt]
    simp [content,lower,Fin.ofNat,Nat.mod_eq_of_lt i.isLt]
  · intro i j
    let k:=2*i.val+j.val
    have hk : k<a.extent .charges := by change 2*i.val+j.val<2*a.rootCount;have:=i.isLt;have:=j.isLt;omega
    change a.filled N .desc t (a.chargeBase+2*i.val+j.val)=_
    rw [show a.chargeBase+2*i.val+j.val=a.lower .charges+k by dsimp [k,lower];omega,
      persists a r N t (by decide : StageBank.desc≠.charges) k hk,
      show t (a.lower .charges+k)=_ from persists a r N s (by decide : StageBank.stats≠.charges) k hk,
      show s (a.lower .charges+k)=_ from persists a r N c (by decide : StageBank.sums≠.charges) k hk]
    simpa only [lower,k,Nat.add_assoc] using chargeAt a N m i j
  · exact nodes_preserved a N r t .desc _ le_rfl
      (nodes_preserved a N r s .stats _ le_rfl (nodes_preserved a N r c .sums _ le_rfl
        (nodes_preserved a N r m .charges _ le_rfl h)))

private theorem runThen {A B : Procedure W} {s t : Memory W} {P : Memory W→Prop} {ka kb : ℕ}
    (first : A.Spec (·=s) (fun _ o=>o=t) ka) (second : B.Spec (·=t) (fun _ o=>P o) kb) :
    (A.seq B).Spec (·=s) (fun _ o=>P o) (ka+kb) :=
  Procedure.Spec.mono (A := A.seq B)
    (Procedure.Spec.seq (A := A) (B := B) first second (fun _ _ h=>h))
    (fun _ h=>h) (fun _ _ h=>h.choose_spec.2) le_rfl

def branchPost (a : RootArchive) (N : Nodes a) (teams : ℕ) (m o : Memory W) :=
  a.ownersPost N.chronology (a.scheduled teams N.work N.pairs a.ids) (a.branchImage N m) o ∧
  (a.summaryHeader N).stored a.age o ∧ (∀ j : Fin 3,o (a.descBase+j.val)=(a.rootWords j:Word W)) ∧
  (∀ z,(∀ b, outside (a.lower b) (a.extent b) z) →
    outside a.ownerBase (2*a.rootCount) z → outside a.rootCache (a.firstFinal+a.rootCount) z → o z=m z)

/-- Owner and ancestor writes leave the physical S6 summary and S11 root
descriptor available to the later interval-packing and selected-root procedures. -/
def summaryApart (a : RootArchive) :=
  ∀ z, (a.statsBase≤z ∧ z<a.statsBase+8) ∨ (a.descBase≤z ∧ z<a.descBase+3) →
    outside a.ownerBase (2*a.rootCount) z ∧ outside a.rootCache (a.firstFinal+a.rootCount) z

theorem branches_spec (a : RootArchive) (N : Nodes a) (r : BranchRoom a W)
    (pr : PartitionRoom a W) (ar : AncestorRoom a W (a.firstFinal+a.rootCount))
    (frame : OwnerFrame a (a.firstFinal+a.rootCount)) (summary : a.summaryApart)
    (teams : ℕ) (schedule : ScheduleFacts a W teams N.work N.pairs a.ids)
    (m : Memory W) (head : a.outHeader m) (stored : N.Stored m) :
    (a.branchROM (W:=W)).Spec (·=m) (fun _ o=>a.branchPost N teams m o) a.branchCost := by
  let c:=a.filled N .charges m
  let s:=a.filled N .sums c
  let t:=a.filled N .stats s
  let e:=a.branchImage N m
  have cHead:=keptHeader a N r .charges m head
  have sHead:=keptHeader a N r .sums c cHead
  have tHead:=keptHeader a N r .stats s sHead
  have charges (i : Fin a.rootCount) : c (a.chargeBase+2*i.val)=(N.work i : Word W) := by
    have v:=chargeAt a N m i (0:Fin 2)
    simpa only [Fin.val_zero,Nat.add_zero,countWord_work] using v
  have total : s (a.prefixes+a.rootCount)=(workBefore N a.rootCount:Word W) := by
    exact (generated a N .sums c a.rootCount (by change _<a.rootCount+1;omega)).trans (by simp [content,lower])
  obtain ⟨hs,hd,hc,hn⟩ := branch_ready a N r m stored
  have count : a.ids.length=a.rootCount := by simp [ids]
  have amounts : a.partitionInput (Team.ticks N.work a.ids) (a.ids.map (weights (w:=W) N.work N.pairs)) e := by
    refine ⟨hs 1,?_,?_⟩
    · rw [ticks_workBefore]; exact hs 2
    · apply stores_of_rows
      intro j
      let i : Fin a.rootCount:=⟨j.val,by simpa [ids] using j.isLt⟩
      have lo:=hc i (0:Fin 2)
      have hi:=hc i (1:Fin 2)
      simpa [ids,weights,countWord,i,i.isLt] using And.intro lo hi
  have links : a.ancestorInput N.chronology e := by
    refine ⟨?_,hd 1,hs 1,hn.2⟩
    calc e a.descBase = (a.rootWords 0 : Word W) := by
           simpa only [e,Fin.val_zero,Nat.add_zero] using hd 0
         _ = (a.firstFinal : Word W) := rfl
  intro p reg params machine
  refine Procedure.Spec.mono (A := a.branchROM) (pre := fun x=>x=m) (budget := a.branchCost)
    (post := fun _ out=>a.ownersPost N.chronology (a.scheduled teams N.work N.pairs a.ids) e out)
    ?_ (fun _ eq=>eq) ?_ le_rfl machine
  · let owners : Procedure W := a.partition.seq a.ancestors
    let desc := (a.scan 7 a.rootFormula).seq owners
    let stats := (a.scan 5 a.meta).seq desc
    let sums := (a.scan 2 a.prefix).seq stats
    let completed := a.ownersPost N.chronology (a.scheduled teams N.work N.pairs a.ids) e
    unfold branchROM branchCost
    intro p₀ r₀ k₀ M₀
    refine runThen (A:=a.scan 0 a.rootCharges) (B:=sums) (P:=completed) (t:=c)
      (charge_scan a N r m stored head) ?_ M₀
    intro p₁ r₁ k₁ M₁
    refine runThen (A:=a.scan 2 a.prefix) (B:=stats) (P:=completed) (t:=s)
      (sum_scan a N r c cHead charges) ?_ M₁
    intro p₂ r₂ k₂ M₂
    refine runThen (A:=a.scan 5 a.meta) (B:=desc) (P:=completed) (t:=t)
      (stats_scan a N r s sHead total) ?_ M₂
    intro p₃ r₃ k₃ M₃
    refine runThen (A:=a.scan 7 a.rootFormula) (B:=owners) (P:=completed) (t:=e)
      (desc_scan a N r t tHead) ?_ M₃
    exact a.owners_spec N.chronology teams N.work N.pairs a.ids pr ar frame count N.first rfl schedule e amounts links
  intro _ o ok
  obtain ⟨image,owner,root,outside⟩:=ok
  refine ⟨⟨image,owner,root,outside⟩,?_,?_,?_⟩
  · intro i
    obtain ⟨a1,a2⟩:=summary (a.statsBase+i.val) (Or.inl (by have:=i.isLt;omega))
    exact (outside _ a1 a2).trans (hs i)
  · intro i
    obtain ⟨a1,a2⟩:=summary (a.descBase+i.val) (Or.inr (by have:=i.isLt;omega))
    exact (outside _ a1 a2).trans (hd i)
  · intro z pre p q
    exact (outside z p q).trans ((fill_frame t _ _ _ z (pre .desc)).trans
      ((fill_frame s _ _ _ z (pre .stats)).trans ((fill_frame c _ _ _ z (pre .sums)).trans
        (fill_frame m _ _ _ z (pre .charges)))))



end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM RAM.TickGreedySweep RAM.TickGreedyNat TickGreedyReplay LinearAlgebra.SpectralBooks.VNP
open scoped Fin.CommRing
variable {W : ℕ} {α : Type*}

private theorem label_index (slots : List α→List (ℕ×α)) (g : ℕ) (groups : List (List α))
    (x : (ℕ×ℕ)×α) (hx : x∈labelBoth slots g groups) : x.1.1<g+groups.length := by
  induction groups generalizing g with
  | nil => simp [labelBoth] at hx
  | cons b bs ih =>
    rw [labelBoth,List.mem_append] at hx
    rcases hx with found|tail
    · obtain ⟨z,_,rfl⟩:=List.mem_map.mp found
      simp
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (g+1) tail

/-- A physical group word is the exact index of one of the groups enumerated by
the finite outer handoff. Empty scheduler slots emit no index. -/
theorem scheduled_group_lt (a : RootArchive) (teams : ℕ) (work pairs : α→ℕ) (xs : List α)
    (fit : a.groups<2^W) (i : Fin (a.scheduled (W:=W) teams work pairs xs).length) :
    ((a.scheduled (W:=W) teams work pairs xs)[i.val].1).val<a.groups := by
  let groups:=schedule a.groups (Team.ticks work xs) a.totalPairs work pairs xs
  let slots:=fun b=>label 0 (Team.handoff work (a.slotBudget/4) teams b).1
  have member : (a.scheduled (W:=W) teams work pairs xs)[i.val]∈
      (labelBoth slots 0 groups).map (owner (w:=W)) := List.getElem_mem i.isLt
  obtain ⟨x,hx,eq⟩:=List.mem_map.mp member
  have length : groups.length=a.groups := Team.handoff_length ..
  have xi : x.1.1<a.groups := by simpa only [Nat.zero_add,length] using label_index slots 0 groups x hx
  rw [←eq]
  exact (Fin.val_cast_of_lt (xi.trans fit)).le.trans_lt xi

/-- The group attached to the i-th chronological terminal root, read from the
concrete natural schedule that the installed greedy machine writes. -/
def groupOf (a : RootArchive) (N : Nodes a) (teams : ℕ) (h : ScheduleFacts a W teams N.work N.pairs a.ids)
    (fit : a.groups<2^W) (i : Fin a.rootCount) : Fin a.groups :=
  let labels:=a.scheduled (W:=W) teams N.work N.pairs a.ids
  let ix : Fin labels.length := ⟨i.val,by
    rw [show labels.length=a.ids.length from scheduled_length a teams N.work N.pairs a.ids h]
    simpa only [ids,List.length_ofFn] using i.isLt⟩
  ⟨labels[ix.val].1.val,scheduled_group_lt a teams N.work N.pairs a.ids fit ix⟩

theorem branch_group (a : RootArchive) (N : Nodes a) (teams : ℕ) (h : ScheduleFacts a W teams N.work N.pairs a.ids)
    (fit : a.groups<2^W) (m out : Memory W) (post : a.branchPost N teams m out) (i : Fin a.rootCount) :
    out (a.ownerBase+2*i.val)=((a.groupOf N teams h fit i).val:Word W) := by
  let labels:=a.scheduled (W:=W) teams N.work N.pairs a.ids
  let j : Fin labels.length:=⟨i.val,by
    rw [show labels.length=a.ids.length from scheduled_length a teams N.work N.pairs a.ids h]
    simpa only [ids,List.length_ofFn] using i.isLt⟩
  exact (post.1.2.1 j).1.trans (Fin.cast_val_eq_self _).symm



end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
