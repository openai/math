import OAI.Hierarchy.DescentCandidateMaskRAM
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Sharing the candidate dictionary and gather scratch across the whole public schedule -/
namespace Hierarchy.DescentResetCandidateBatch
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {N H G M field b w : ℕ}

def slab (base stride j : ℕ) := base+j*stride

def endAddress (base stride jobs : ℕ) := base+jobs*stride

def stepCode (w scratch rows : ℕ) (op : ℕ→Expr) (base stride : ℕ) (menu : DescentSIMDLookup.Banks) (j : ℕ) :=
  (scan w scratch rows (op j)).seq (scan w (slab base stride j) rows (lookup menu))

def stepImage (scratch rows : ℕ) (op : ℕ→Expr) (base stride : ℕ) (menu : DescentSIMDLookup.Banks) (j : ℕ) (m : Memory w) :=
  image (slab base stride j) rows (lookup menu) (image scratch rows (op j) m)

def time (rows : ℕ) (op : ℕ→Expr) (j : ℕ) := 4+rows*(2*(op j).work+4)+(4+44*rows)

def program (code : ℕ→Procedure w) (start : ℕ) : ℕ→Procedure w
  | 0=>ProtocolRAM.program w []
  | n+1=>(code start).seq (program code (start+1) n)

def result (one : ℕ→Memory w→Memory w) (start : ℕ) : ℕ→Memory w→Memory w
  | 0,m=>m
  | n+1,m=>result one (start+1) n (one start m)

def clock (ticks : ℕ→ℕ) (start : ℕ) : ℕ→ℕ
  | 0=>4
  | n+1=>ticks start+clock ticks (start+1) n

theorem clock_le (rows limit start n : ℕ) (op : ℕ→Expr)
    (bound : ∀j,start≤j→j<start+n→(op j).work≤limit) :
    clock (time rows op) start n≤4+n*(4+rows*(2*limit+4)+(4+44*rows)) := by
  induction n generalizing start with
  | zero=>simp [clock]
  | succ n ih=>
    have later:=ih (start+1) (fun j lo hi=>bound j (by omega) (by omega))
    have row:=Nat.mul_le_mul_left rows
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (bound start le_rfl (by omega))) 4)
    rw [clock,Nat.succ_mul n (4+rows*(2*limit+4)+(4+44*rows))]
    change 4+rows*(2*(op start).work+4)+(4+44*rows)+clock (time rows op) (start+1) n ≤ _
    omega

theorem cheap (scratch rows base stride : ℕ) (op : ℕ→Expr) (menu : DescentSIMDLookup.Banks)
    (start n : ℕ) : CheapCode (program (stepCode w scratch rows op base stride menu) start n) := by
  induction n generalizing start with
  | zero=>exact program_cheap w []
  | succ n ih=>exact cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)) (ih (start+1))

theorem hardware (scratch rows base stride : ℕ) (op : ℕ→Expr) (menu : DescentSIMDLookup.Banks)
    (start n limit : ℕ) (bound : ∀j,start≤j→j<start+n→(op j).work≤limit) :
    DescentStaticWordColumn.names (program (stepCode w scratch rows op base stride menu) start n)≤15+n*(102+4*limit) := by
  induction n generalizing start with
  | zero=>
    change DescentStaticWordColumn.names (scan w 0 0 (.lit 0))≤_
    rw [DescentStaticWordColumn.names_scan]
    simp [Expr.work]
  | succ n ih=>
    have tail:=ih (start+1) (fun j lo hi=>bound j (by omega) (by omega))
    have first:=bound start le_rfl (by omega)
    rw [program,DescentStaticWordColumn.names_seq,stepCode,DescentStaticWordColumn.names_seq,
      DescentStaticWordColumn.names_scan,DescentStaticWordColumn.names_scan,lookup_work,Nat.succ_mul n (102+4*limit)]
    omega

/-- Every stage reads the true input prefix and reuses the single scratch
slab. Earlier output columns and everything outside both write intervals survive. -/
theorem visit (code : ℕ→Procedure w) (one : ℕ→Memory w→Memory w) (ticks : ℕ→ℕ)
    (scratch rows base stride : ℕ) (source mem : Memory w) (start n : ℕ)
    (value : ℕ→Fin rows→Word w) (low : ∀a<scratch,mem a=source a)
    (sep : scratch+rows≤base) (space : rows≤ stride)
    (step : ∀j,start≤j→j<start+n→∀m : Memory w,(∀a<scratch,m a=source a)→
      (code j).Exec m (one j m) (ticks j) ∧
      (∀i : Fin rows,one j m (slab base stride j+i.val)=value j i) ∧
      ∀a,(a<scratch ∨ scratch+rows≤a)→(a<slab base stride j ∨ slab base stride j+rows≤a) → one j m a=m a) :
    let out:=result one start n mem
    (program code start n).Exec mem out (clock ticks start n) ∧
      (∀j,start≤j→j<start+n→∀i : Fin rows,out (slab base stride j+i.val)=value j i) ∧
      ∀a,(a<scratch ∨ scratch+rows≤a)→(a<slab base stride start ∨ slab base stride (start+n)≤a) → out a=mem a := by
  induction n generalizing start mem with
  | zero=>
    exact ⟨ProtocolRAM.program_exec [] mem (by simp),by intros;omega,by intros;rfl⟩
  | succ n ih=>
    have first:=step start le_rfl (by omega) mem low
    have low' (a : ℕ) (ha : a<scratch) : one start mem a=source a :=
      (first.2.2 a (.inl ha) (.inl (by unfold slab;omega))).trans (low a ha)
    have rest:=ih (one start mem) (start+1) low' (fun j lo hi=>step j (by omega) (by omega))
    have next : slab base stride (start+1)=slab base stride start+stride := by simp [slab,Nat.add_mul,Nat.add_assoc]
    have far : slab base stride (start+1+n)=slab base stride (start+(n+1)) := by congr 1;omega
    refine ⟨Procedure.Exec.then first.1 rest.1,?_,?_⟩
    · intro j lo hi word_
      by_cases eqn : j=start
      · subst j
        apply (rest.2.2 _ (.inr (by unfold slab;omega)) (.inl (by rw [next];have h:=word_.isLt;omega))).trans
        exact first.2.1 word_
      · exact rest.2.1 j (by omega) (by omega) word_
    · intro a safe away
      have tail : a<slab base stride (start+1) ∨ slab base stride (start+1+n)≤a:=by rw [next,far];omega
      have stretch:=Nat.mul_le_mul_right stride (show start+1≤ start+(n+1) by omega)
      have upper : slab base stride (start+1)≤ slab base stride (start+(n+1)):=Nat.add_le_add_left stretch base
      exact (rest.2.2 a safe tail).trans (first.2.2 a safe (by rw [next] at upper;omega))

/-- All public instructions also execute on arbitrary incoming words. -/
theorem any (scratch rows base stride start n : ℕ) (op : ℕ→Expr) (menu : DescentSIMDLookup.Banks)
    (m : Memory w) (_sep : scratch+rows≤base) (space : rows≤ stride) (scratchRoom : scratch+rows<2^w)
    (early : ∀j,start≤j→j<start+n→(op j).Fits w scratch)
    (lookupFits : ∀j,start≤j→j<start+n→(lookup menu).Fits w (slab base stride j))
    (top : slab base stride (start+n)<2^w) :
    let code:=stepCode w scratch rows op base stride menu
    let one:=stepImage (w:=w) scratch rows op base stride menu
    let out:=result one start n m
    (program code start n).Exec m out (clock (time rows op) start n) ∧
    ∀a,(a<scratch ∨ scratch+rows≤a)→(a<slab base stride start ∨ slab base stride (start+n)≤a) → out a=m a := by
  induction n generalizing start m with
  | zero=>exact ⟨ProtocolRAM.program_exec [] m (by simp),by intros;rfl⟩
  | succ n ih=>
    let lo:=slab base stride start
    let one:=stepImage (w:=w) scratch rows op base stride menu
    have next : slab base stride (start+1)=lo+stride:=by simp [lo,slab,Nat.add_mul,Nat.add_assoc]
    have endEq : start+1+n=start+(n+1):=by omega
    have grow : slab base stride (start+1)≤ slab base stride (start+(n+1)):=
      Nat.add_le_add_left (Nat.mul_le_mul_right stride (by omega)) base
    have writeOK : lo+rows<2^w:=by rw [next] at grow;omega
    have run : (stepCode w scratch rows op base stride menu start).Exec m (one start m) (time rows op start) := by
      have price : 4+rows*(2*(lookup menu).work+4)=4+44*rows :=by rw [lookup_work]; ring
      unfold time
      rw [←price]
      intro P R K machine pc reg pub exit installed data cfg mem enter same
      exact Procedure.Exec.then (scan_exec scratch rows (op start) m (early _ le_rfl (by omega)) scratchRoom)
        (scan_exec lo rows (lookup menu) (image scratch rows (op start) m) (lookupFits _ le_rfl (by omega)) writeOK)
        machine pc reg pub exit installed data cfg mem enter same
    have tail:=ih (start+1) (one start m) (fun j lo hi=>early j (by omega) (by omega))
      (fun j lo hi=>lookupFits j (by omega) (by omega)) (by rwa [endEq])
    refine ⟨Procedure.Exec.then run tail.1,?_⟩
    intro a safe away
    have fence : a<slab base stride (start+1) ∨ slab base stride (start+1+n)≤a := by rw [next,endEq];omega
    apply (tail.2 a safe fence).trans
    have outside : a<lo ∨ lo+rows≤a:=by rw [next] at grow;omega
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ outside).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ safe)

theorem issue (emit : (Fin N→Cell field)→Cell b) (jobs scratch base stride : ℕ)
    (tables : Fin N→Tables) (reads : ℕ→Fin N→Expr) (menu : DescentSIMDLookup.Banks)
    (values : ℕ→Fin H→Fin G→Fin N→Cell field) (pos : 0<M) (mem : Memory w)
    (bounds : ∀j<jobs,Bounds (w:=w) (d:=field) (M:=M) tables (reads j) scratch)
    (constants : ∀i,Static (tables i) (setField (d:=field) i) M mem)
    (inputs : ∀j<jobs,∀i,Source (reads j i) (fun v g=>values j v g i) M mem)
    (scratchFit : scratch+H*chunks G M<2^w) (sep : scratch+H*chunks G M≤base) (parts : H*chunks G M≤ stride)
    (geometry : ∀j<jobs,DescentSIMDLookup.Fits menu (field*N) b M H G w (slab base stride j))
    (rom : resident (emit ∘ (encode field N).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*N)*M)≤ scratch) (maskLow : menu.mask.base+H*chunks G M≤ scratch)
    (wire : menu.source.base=scratch) :
    let rows:=H*chunks G M
    let op:=fun j=>assembly tables (reads j)
    let code:=stepCode w scratch rows op base stride menu
    let one:=stepImage (w:=w) scratch rows op base stride menu
    let out:=result one 0 jobs mem
    (program code 0 jobs).Exec mem out (clock (time rows op) 0 jobs) ∧
    (∀j<jobs,∀q : Row H G M,out (slab base stride j+(row H G M q).val)=
      ((data (fun v g=>emit (values j v g)) q).val:Word w)) ∧
    ∀a,(a<scratch ∨ scratch+rows≤a)→(a<base ∨ endAddress base stride jobs≤a) → out a=mem a := by
  intro rows op code one out
  let value (j : ℕ) (r : Fin rows) : Word w:=((data (fun v g=>emit (values j v g)) ((row H G M).symm r)).val:ℕ)
  have step (j : ℕ) (_ : 0≤j) (hj : j<0+jobs) (m : Memory w) (low : ∀a<scratch,m a=mem a) :
      (code j).Exec m (one j m) (time rows op j) ∧
      (∀r : Fin rows,one j m (slab base stride j+r.val)=value j r) ∧
      ∀a,(a<scratch ∨ scratch+rows≤a)→(a<slab base stride j ∨ slab base stride j+rows≤a) → one j m a=m a := by
    have h : j<jobs:=by omega
    have libs (i : Fin N) : Static (tables i) (setField (d:=field) i) M m := by
      obtain ⟨_,sh,app,shBits,appBits⟩:=bounds j h i
      constructor
      · intro k
        have small : k.val<(tables i).shift.size:=by simpa only [Bank.size,shBits] using k.isLt
        rw [low _ (by have:=sh.2.2;omega)]
        exact (constants i).1 k
      · intro k
        have small : k.val<(tables i).apply.size:=by simpa only [Bank.size,appBits] using k.isLt
        rw [low _ (by have:=app.2.2;omega)]
        exact (constants i).2 k
    have seen (i : Fin N) : Source (reads j i) (fun v g=>values j v g i) M m := by
      intro p
      exact (eval_below _ _ mem m (bounds j h i).1 low).trans (inputs j h i p)
    have shared : resident (emit ∘ (encode field N).symm) menu H G M m := by
      constructor
      · intro i;rw [low _ (by have:=i.isLt;omega)];exact rom.1 i
      · intro i;rw [low _ (by have:=i.isLt;omega)];exact rom.2 i
    obtain ⟨run,read,_,frame⟩:=gathered_words emit tables (reads j) menu scratch (slab base stride j)
      (values j) pos m (bounds j h) libs seen scratchFit (geometry j h) shared dictLow maskLow wire
    refine ⟨run,?_,frame⟩
    intro r
    change imageBank H G M (slab base stride j) menu
      (image scratch (H*chunks G M) (assembly tables (reads j)) m) _ = _
    simpa only [value,Equiv.apply_symm_apply] using read ((row H G M).symm r)
  obtain ⟨exec,read,frame⟩:=visit code one (time rows op) scratch rows base stride mem mem 0 jobs value
    (fun _ _=>rfl) sep parts step
  refine ⟨exec,?_,?_⟩
  · intro j hj q
    simpa only [value,Equiv.symm_apply_apply] using read j (Nat.zero_le _) (by omega) (row H G M q)
  · intro a safe away
    exact frame a safe (by simpa [slab,endAddress] using away)

/-- An emitted column can be used directly as an incoming expression
by the canonical candidate sheet or another relative-rank stage. -/
theorem source {jobs base bits ceiling : ℕ} (m : Memory w) (values : ℕ→Fin H→Fin G→Cell b)
    (j : Fin jobs) (room : H*chunks G M≤2^bits)
    (dest : (⟨slab base (2^bits) j.val,bits⟩ : Bank).Fits w ceiling)
    (read : ∀q : Row H G M,m (slab base (2^bits) j.val+(row H G M q).val)=((data (values j.val) q).val:Word w)) :
    Source (.lookup ⟨slab base (2^bits) j.val,bits⟩ .row) (values j.val) M m :=
  source_column _ _ dest _ _ room read

end
end Hierarchy.DescentResetCandidateBatch

end OAI
