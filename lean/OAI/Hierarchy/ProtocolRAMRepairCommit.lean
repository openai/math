import OAI.Hierarchy.ProtocolRAMRepairHistogram
import OAI.Hierarchy.ProtocolRAMAttemptGate
import OAI.Hierarchy.ProtocolRAMSignedStock

namespace OAI
/-! # One authoritative commodity bank after a simultaneous repair or acquisition -/

namespace Hierarchy.ProtocolRAM.RepairHistogram
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w goods n : ℕ}

/-- The mode is one global scalar for this whole tick. The other registers use the
common physical commodity ordinal, independent of candidate and signed-stratum counts. -/
structure CommitPlan where
  bank : Bank
  reserve : Bank
  half : Bank
  clip : Bank
  excess : Bank
  mode : Expr
  src : ℕ
  activeOut : ℕ
  limit : ℕ

def retainedTerm (s : CommitPlan) : Expr :=
  let old := Expr.lookup s.bank .row
  .branch .eq s.mode (.lit 2) (.lookup s.clip .row)
    (.branch .eq s.mode (.lit 3) (.lookup s.half old) old)

def reserveTerm (s : CommitPlan) : Expr :=
  let old := Expr.lookup s.bank .row
  .branch .eq s.mode (.lit 3) (.op .sub old (.lookup s.half old)) (.lookup s.reserve .row)

def excessTerm (s : CommitPlan) :=
  Expr.branch .eq s.mode (.lit 2) (.lookup s.excess .row) (.lit 0)

def transfers (s : CommitPlan) (goods : ℕ) : List Pass :=
  [⟨s.activeOut,goods,retainedTerm s⟩,⟨s.activeOut+goods,goods,reserveTerm s⟩,
   ⟨s.activeOut+goods+goods,goods,excessTerm s⟩]

def commit (w n goods : ℕ) (p : Columns) (s : CommitPlan) : Procedure w :=
  (cappedCode w s.src n s.clip.base goods s.limit p s.bank).seq (program w (transfers s goods))

def beforeTransfer (p : Columns) (s : CommitPlan) (n goods : ℕ) (m : Memory w) :=
  capped p s.bank s.src n s.clip.base goods s.limit m

def commitOut (p : Columns) (s : CommitPlan) (n goods : ℕ) (m : Memory w) :=
  ProtocolRAM.result (transfers s goods) (beforeTransfer p s n goods m)

def commitTicks (n goods : ℕ) (p : Columns) (s : CommitPlan) :=
  (ticks n p+clock (StockAccounts.columns s.clip.base goods s.limit (.lookup s.bank .row)))+
    clock (transfers s goods)

theorem transfer_clock (s : CommitPlan) (goods : ℕ) :
    clock (transfers s goods)=16+goods*(8*s.mode.work+150) := by
  simp [transfers,retainedTerm,reserveTerm,excessTerm,clock,Pass.clock,Expr.work]
 ; ring

/-- Linear running time in the actual sparse occurrences and independent commodity
coordinates. Only the fixed expressions for a local packet and a mode test enter the coefficients. -/
theorem commitTicks_eq (n goods : ℕ) (p : Columns) (s : CommitPlan) :
    commitTicks n goods p s=35+n*(4*(pair p).work+20)+goods*(8*s.mode.work+242) := by
  rw [commitTicks,transfer_clock,show clock (StockAccounts.columns s.clip.base goods s.limit
      (.lookup s.bank .row))=12+92*goods from ProtocolRAMSignedStock.clock_cap ..,ticks]
  ring

structure CommitReady (p : Columns) (s : CommitPlan) (w n goods : ℕ) (m : Memory w) : Prop where
  directory : PairDirectory p m n
  pairFits : (pair p).Fits w s.src
  pairRoom : s.src+2*n<2^w
  safe : ∀ e : Fin n,address p m e< s.src
  clipFits : (Expr.lookup s.bank .row).inputEnd≤ s.clip.base
  clipRoom : s.clip.base+goods+goods<2^w
  inputs : ∀ a∈transfers s goods,a.term.Fits w s.activeOut
  room : s.activeOut+goods+goods+goods<2^w

theorem commit_exec (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m) :
    (commit w n goods p s).Exec m (commitOut p s n goods m) (commitTicks n goods p s) := by
  apply Procedure.Exec.then (A:=cappedCode w s.src n s.clip.base goods s.limit p s.bank)
    (B:=program w (transfers s goods)) (capped_exec p s.bank s.src n s.clip.base goods s.limit m
      ready.directory ready.pairFits ready.pairRoom ready.safe ready.clipFits ready.clipRoom)
  apply program_exec
  intro a ha
  have fits := ready.inputs a ha
  have room := ready.room
  simp only [transfers,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨fits,by change s.activeOut+goods<2^w; omega⟩
  · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right s.activeOut goods) fits,
      by change s.activeOut+goods+goods<2^w; omega⟩
  · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (by change s.activeOut ≤ s.activeOut+goods+goods; omega) fits,
      by change s.activeOut+goods+goods+goods<2^w; omega⟩

set_option maxHeartbeats 1500000 in
theorem commit_cheap (w n goods : ℕ) (p : Columns) (s : CommitPlan) : CheapCode (commit w n goods p s) :=
  @cheap_seq w (cappedCode w s.src n s.clip.base goods s.limit p s.bank) (program w (transfers s goods))
    (fun {_P _R _K} pc reg pub exit i=>capped_cheap w s.src n s.clip.base goods s.limit p s.bank pc reg pub exit i)
    (fun {_P _R _K} pc reg pub exit i=>program_cheap w (transfers s goods) pc reg pub exit i)

/-- All three snapshots read the same capped input; none of the two earlier publication
passes can modify the later expression's source words. -/
theorem commit_read (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m)
    (j : Fin goods) :
    let a := beforeTransfer p s n goods m
    let r : Word w := j.val
    let o := commitOut p s n goods m
    o (s.activeOut+j.val)=(retainedTerm s).eval a r ∧
    o (s.activeOut+goods+j.val)=(reserveTerm s).eval a r ∧
    o (s.activeOut+goods+goods+j.val)=(excessTerm s).eval a r := by
  let src := beforeTransfer p s n goods m
  let one := image s.activeOut goods (retainedTerm s) src
  let two := image (s.activeOut+goods) goods (reserveTerm s) one
  let three := image (s.activeOut+goods+goods) goods (excessTerm s) two
  have h := j.isLt
  have before (a : ℕ) (lo : a< s.activeOut) : one a=src a :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl lo)
  have before' (a : ℕ) (lo : a< s.activeOut) : two a=src a :=
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans (before a lo)
  have inputR : (reserveTerm s).Fits w s.activeOut := ready.inputs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have inputE : (excessTerm s).Fits w s.activeOut := ready.inputs _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  change three _=_ ∧ three _=_ ∧ three _=_
  refine ⟨?_,?_,?_⟩
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
      ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
        (ProtocolRAMGeneratedWrite.read_image _ _ _ _ j))
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by omega))).trans
      ((ProtocolRAMGeneratedWrite.read_image _ _ _ _ j).trans (eval_below _ _ src one inputR before))
  · exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ j).trans (eval_below _ _ src two inputE before')

theorem commit_mode (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m)
    (j : Fin goods) (wide : 4≤2^w) :
    let a := beforeTransfer p s n goods m
    let r : Word w := j.val
    let mode := (s.mode.eval a r).val
    let old := s.bank.read a r
    let o := commitOut p s n goods m
    o (s.activeOut+j.val)=(if mode=2 then s.clip.read a r else if mode=3 then s.half.read a old else old) ∧
    o (s.activeOut+goods+j.val)=(if mode=3 then old-s.half.read a old else s.reserve.read a r) ∧
    o (s.activeOut+goods+goods+j.val)=(if mode=2 then s.excess.read a r else 0) := by
  have two (x : Word w) : x=((2:ℕ):Word w) ↔ x.val=2 := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt (show 2<2^w from (by decide : 2<4).trans_le wide)]
  have three (x : Word w) : x=((3:ℕ):Word w) ↔ x.val=3 := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt (show 3<2^w from (by decide : 3<4).trans_le wide)]
  simpa only [retainedTerm,reserveTerm,excessTerm,Expr.eval,Comparison.test,beq_iff_eq,two,three,Nat.cast_zero,
    RowOp.opcode,BinaryOp.eval] using commit_read p s m ready j

theorem transfer_frame (p : Columns) (s : CommitPlan) (src n goods : ℕ) (m : Memory w) (a : ℕ)
    (low : a< s.clip.base) : capped p s.bank src n s.clip.base goods s.limit m a=result p src n m a := by
  apply result_below
  intro t ht
  simp only [StockAccounts.columns,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl
  · exact low
  · change a< s.clip.base+goods
    omega

theorem input_frame (p : Columns) (s : CommitPlan) (m : Memory w) (a : ℕ)
    (tape : a< s.src) (low : a< s.clip.base) (safe : ∀ j : Fin n,address p m j≠a) :
    beforeTransfer p s n goods m a=m a := by
  rw [beforeTransfer,transfer_frame p s _ n goods m a low,result,ProtocolRAMWeightedScatter.frame _ _ _ _ _ safe]
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl tape)

/-- Out-of-range cells survive both histogram source generation and every dense
output. The optional extra destination at `bank.base+goods` absorbs ordinary links. -/
def commit_keeps (s : CommitPlan) (n goods x : ℕ) : Prop :=
  (x< s.src ∨ s.src+2*n≤x) ∧ (x< s.bank.base ∨ s.bank.base+goods+1≤x) ∧
    (x< s.clip.base ∨ s.clip.base+goods+goods≤x) ∧ (x< s.activeOut ∨ s.activeOut+goods+goods+goods≤x)

private theorem pass_frame (ps : List Pass) (m : Memory w) (a : ℕ)
    (free : ∀ p∈ps,a<p.out ∨ p.out+p.rows≤a) : ProtocolRAM.result ps m a=m a := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (p.apply m) (fun t ht => free t (.tail _ ht))).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (free p (.head _)))

theorem commit_frame (p : Columns) (s : CommitPlan) (n goods : ℕ) (m : Memory w) (x : ℕ)
    (targets : ∀ e : Fin n,s.bank.base≤address p m e ∧ address p m e≤ s.bank.base+goods)
    (keep : commit_keeps s n goods x) : commitOut p s n goods m x=m x := by
  obtain ⟨src,stock,clip,done⟩ := keep
  have last : ∀ t∈transfers s goods,x<t.out ∨ t.out+t.rows≤x := by
    intro t ht
    simp only [transfers,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp only <;> omega
  have caps : ∀ t∈StockAccounts.columns s.clip.base goods s.limit (.lookup s.bank .row), x<t.out ∨ t.out+t.rows≤x := by
    intro t ht
    simp only [StockAccounts.columns,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl <;> simp only <;> omega
  rw [commitOut,pass_frame _ _ _ last,beforeTransfer,capped,pass_frame _ _ _ caps,result,
    ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by intro i; have := targets i; omega)]
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ src

theorem raw_idle (p : Columns) (s : CommitPlan) (m : Memory w) (j : Fin goods)
    (noRepairs : ∀ e : Fin n,delta p m e=0) (sep : s.bank.base+goods≤ s.src) :
    raw s.bank p s.src n m j=(m (s.bank.base+j.val)).val := by
  simp only [raw,result,ProtocolRAMWeightedScatter.image,ProtocolRAMWeightedScatter.partialLoad,noRepairs,
    ite_self,Finset.sum_const_zero,Nat.cast_zero,add_zero]
  exact congrArg Fin.val (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by have := j.isLt;omega)))

theorem stock_read_raw (p : Columns) (s : CommitPlan) (m : Memory w) (j : Fin goods)
    (before : s.bank.base+goods≤ s.clip.base) (width : goods≤2^w) (capacity : goods≤ s.bank.size) :
    (s.bank.read (beforeTransfer p s n goods m) (j.val:Word w)).val=raw s.bank p s.src n m j := by
  simp only [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le width),Nat.mod_eq_of_lt (j.isLt.trans_le capacity)]
  exact congrArg Fin.val (transfer_frame p s _ n goods m _ (by have := j.isLt; omega))

/-- In a real failed mode, the active and spill words are the retained and excess
of the merged repair bank, from the actual clipped bank of the same stage. -/
theorem commit_repair (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m)
    (j : Fin goods) (wide : 4≤2^w) (payload cap : ℕ) (limit : s.limit=cap*payload)
    (room : s.limit<2^w) (excess : s.excess.base=s.clip.base+goods)
    (clipCap : goods≤ s.clip.size) (excessCap : goods≤ s.excess.size) (bankCap : goods≤ s.bank.size)
    (mode : (s.mode.eval (beforeTransfer p s n goods m) (j.val:Word w)).val=2) :
    let o := commitOut p s n goods m
    (o (s.activeOut+j.val)).val=min (raw s.bank p s.src n m j) (cap*payload) ∧
    (o (s.activeOut+goods+goods+j.val)).val=spillBits cap payload (raw s.bank p s.src n m) j := by
  obtain ⟨keep,_,pay⟩ := commit_mode p s m ready j wide
  have hsize := ready.clipRoom
  have fit : j.val<2^w := by have := j.isLt;omega
  simp only [mode,ite_true,Bank.read,Fin.val_cast_of_lt fit,Nat.mod_eq_of_lt (j.isLt.trans_le clipCap),
    Nat.mod_eq_of_lt (j.isLt.trans_le excessCap),excess] at keep pay
  obtain ⟨stored,paid⟩ := capped_read p s.bank s.src n s.clip.base cap payload m j ready.clipFits
    ready.clipRoom bankCap (by simpa only [← limit] using room)
  constructor
  · apply (congrArg Fin.val keep).trans
    simpa only [beforeTransfer,limit] using stored
  · apply (congrArg Fin.val pay).trans
    simpa only [beforeTransfer,limit] using paid

/-- One split of each genuine commodity on acquisition, after the zero-delta sweep.
The amount of reserved stock is the integer complement of the retained half. -/
theorem commit_buy (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m)
    (j : Fin goods) (wide : 4≤2^w) (space : s.bank.base+goods≤ s.src) (before : s.bank.base+goods≤ s.clip.base)
    (bankCap : goods≤ s.bank.size) (idle : ∀ e : Fin n,delta p m e=0)
    (mode : (s.mode.eval (beforeTransfer p s n goods m) (j.val:Word w)).val=3)
    (half : let a := beforeTransfer p s n goods m
      let x := s.bank.read a (j.val:Word w)
      (s.half.read a x).val=x.val/2) :
    let o := commitOut p s n goods m
    let old := (m (s.bank.base+j.val)).val
    (o (s.activeOut+j.val)).val=old/2 ∧ (o (s.activeOut+goods+j.val)).val=old-old/2 ∧
      o (s.activeOut+goods+goods+j.val)=0 := by
  let a := beforeTransfer p s n goods m
  let x := s.bank.read a (j.val:Word w)
  have fit := ready.clipRoom
  have real : x.val=(m (s.bank.base+j.val)).val :=
    (stock_read_raw p s m j before (by omega) bankCap).trans (raw_idle p s m j idle space)
  have le : s.half.read a x≤x := Fin.le_def.mpr (half.trans_le (Nat.div_le_self ..))
  obtain ⟨keep,save,pay⟩ := commit_mode p s m ready j wide
  simp [mode] at keep save pay
  refine ⟨(congrArg Fin.val keep).trans (half.trans (by rw [real])),?_,pay⟩
  exact (congrArg Fin.val save).trans (by rw [Fin.sub_val_of_le le,half,real])

/-- On an ordinary stopped/advance step the global commodity bank is copied with
no spill. Its reserve stays at the same indexed physical word. -/
theorem commit_copy (p : Columns) (s : CommitPlan) (m : Memory w) (ready : CommitReady p s w n goods m)
    (j : Fin goods) (wide : 4≤2^w) (space : s.bank.base+goods≤ s.src) (before : s.bank.base+goods≤ s.clip.base)
    (bankCap : goods≤ s.bank.size) (reserveCap : goods≤ s.reserve.size)
    (reserveBefore : s.reserve.base+goods≤ s.src ∧ s.reserve.base+goods≤ s.clip.base)
    (reserveSafe : ∀ e : Fin n,address p m e≠s.reserve.base+j.val)
    (idle : ∀ e : Fin n,delta p m e=0)
    (mode : let a := beforeTransfer p s n goods m
      (s.mode.eval a (j.val:Word w)).val≠2 ∧ (s.mode.eval a (j.val:Word w)).val≠3) :
    let o := commitOut p s n goods m
    o (s.activeOut+j.val)=m (s.bank.base+j.val) ∧ o (s.activeOut+goods+j.val)=m (s.reserve.base+j.val) ∧
      o (s.activeOut+goods+goods+j.val)=0 := by
  have fit := ready.clipRoom
  have h := j.isLt
  obtain ⟨keep,save,pay⟩ := commit_mode p s m ready j wide
  simp only [ite_eq_right mode.1,ite_eq_right mode.2] at keep save pay
  have real := (stock_read_raw p s m j before (by omega) bankCap).trans (raw_idle p s m j idle space)
  refine ⟨keep.trans (Fin.ext real),save.trans ?_,pay⟩
  simp only [Bank.read,Fin.val_cast_of_lt (show j.val<2^w by omega),Nat.mod_eq_of_lt (h.trans_le reserveCap)]
  exact input_frame p s m _ (by omega) (by omega) reserveSafe

end
end Hierarchy.ProtocolRAM.RepairHistogram

end OAI
