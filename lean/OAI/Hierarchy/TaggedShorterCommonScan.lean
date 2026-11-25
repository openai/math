import OAI.ThreeFlat.RAM.HistoryBucketPack
import OAI.ThreeFlat.Diagonal.BucketFamilies
import OAI.ThreeFlat.RAM.BucketScanROM
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.TaggedShorterCheapCPU
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Linear native prefix ranks for all weighted rows in the same shorter class -/

namespace Hierarchy.TaggedShorterCommonScan
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat RAM RAM.PhysicalProcedure RAM.ContinuationLink
open RAM.HistoryRowLoop Diagonal.HistoryContraction
open scoped BigOperators Fin.CommRing
variable {n d W : ℕ}

def earlier (key : Fin n → Fin d) (width : Fin n → ℕ) (t : ℕ) (g : Fin d) :=
  ∑ j ∈ Finset.range t, if h : j<n then (if key ⟨j,h⟩=g then width ⟨j,h⟩ else 0) else 0

private def row (key : Fin n → Fin d) (width : Fin n → ℕ) (i : Fin n) : BucketRow (Fin d) :=
  ⟨key i,0,width i,earlier key width i.val (key i)⟩

private def head {P R K : ℕ} (pc : Fin 5→Fin P) (reg : Fin 12 ↪ Fin R)
    (pub : Fin 5→Fin K) (next : Fin P) : Fin 5 → Instr W P R K :=
  ![.publicWord (reg 0) (pub 0) (pc 1),.publicWord (reg 1) (pub 1) (pc 2),
    .publicWord (reg 2) (pub 2) (pc 3),.publicWord (reg 3) (pub 3) (pc 4),
    .publicWord (reg 5) (pub 4) next]

def block (W : ℕ) : Block W 28 12 5 where
  first := (0 : Fin 5).castAdd 23
  emit pc reg pub exit := Fin.addCases (m:=5) (n:=23)
    (head (pc ∘ Fin.castAdd 23) reg pub (pc (Fin.natAdd 5 (Fin.last 22))))
    (BucketScanROM.emit reg (pc ∘ Fin.natAdd 5) exit exit)

def procedure (W src groups counters dst count : ℕ) : Procedure W :=
  ⟨28,12,5,block W,fun i => ((![src,groups,counters,dst,src+3*count] i : ℕ):Word W)⟩

/-- Each input triple selects the key of the original row, and carries its true number
of transport units. Sorting before this pass can change that row's index. -/
def Input (src groups counters : ℕ) (order : Fin n → Fin n) (key : Fin n → Fin d)
    (width : Fin n → ℕ) (m : Memory W) : Prop :=
  (∀i : Fin n, m (src+3*i.val)=((4*(order i).val : ℕ):Word W) ∧
    m (src+3*i.val+1)=0 ∧ m (src+3*i.val+2)=(width (order i):Word W)) ∧
  (∀i : Fin n,m (groups+4*i.val)=((key i).val:Word W)) ∧
  ∀g : Fin d,m (counters+g.val)=0

def image (src groups counters dst n : ℕ) (m : Memory W) : Memory W :=
  walk BucketRegisters.next BucketRegisters.update n
    (⟨src,groups,counters,dst,(src+3*n:ℕ)⟩ : BucketRegisters W) m

/-- The output is one specified memory image for every installation of the physical block. -/
theorem run (src groups counters dst n : ℕ) (m : Memory W) (fits : src+3*n<2^W) :
    (procedure W src groups counters dst n).Exec m (image src groups counters dst n m) (6+23*n) := by
  intro P R K M pc reg pub exit installed data c input entry eqn
  subst input
  change Fin 28 ↪ Fin P at pc
  change Fin 12 ↪ Fin R at reg
  change Fin 5 → Fin K at pub
  change (block W).Installed M pc reg pub exit at installed
  let boot : Fin 5 → Fin P := pc ∘ Fin.castAdd 23
  let body : Fin 23 → Fin P := pc ∘ Fin.natAdd 5
  have hb (i : Fin 5) : M.code (boot i)=head boot reg pub (body (Fin.last 22)) i := by
    simpa [procedure,block,boot,body] using installed (i.castAdd 23)
  have hl (i : Fin 23) : M.code (body i)=BucketScanROM.emit reg body exit exit i := by
    simpa [procedure,block,body] using installed (Fin.natAdd 5 i)
  have hp (i : Fin 5) : M.publicData (pub i)=((![src,groups,counters,dst,src+3*n] i : ℕ):Word W) :=
    data i
  let init := ((((c.put (boot 1) (reg 0) (src:Word W)).put (boot 2) (reg 1) (groups:Word W)).put
    (boot 3) (reg 2) (counters:Word W)).put (boot 4) (reg 3) (dst:Word W)).put
    (body (Fin.last 22)) (reg 5) ((src+3*n:ℕ):Word W)
  change c.pc=boot 0 at entry
  have start : advance M.program 5 c m=some (init,m) := by
    simp [advance,Machine.program,entry,hb,head,Instr.run,hp,init,Config.put]
  have ready : BucketRegisters.view reg init.reg=
      (⟨src,groups,counters,dst,init.reg (reg 5)⟩ : BucketRegisters W) := by
    simp (config := {decide:=true}) [BucketRegisters.view,init,Config.put,Function.update,reg.injective.eq_iff]
  have stopWord : init.reg (reg 5)=((src+3*n:ℕ):Word W) := by simp [init,Config.put]
  have limit : (init.reg (reg 5)).val=src+3*n := by
    rw [stopWord,Fin.val_cast_of_lt fits]
  have srcReg : init.reg (reg 0)=(src:Word W) := congrArg BucketRegisters.source ready
  have size : (init.reg (reg 0)).val+n*3=(init.reg (reg 5)).val := by
    rw [srcReg,Fin.val_cast_of_lt (show src<2^W by omega),limit]
    omega
  obtain ⟨last,step⟩ := BucketScanROM.advance_scan M reg body exit exit hl n c.persistent init.reg c.privateMem m size
  rw [ready,stopWord] at step
  exact ⟨5+(1+n*23),by omega,_,_,advance_trans start step,rfl,rfl⟩

theorem read_frame (src groups counters dst : ℕ) (order : Fin n → Fin n)
    (key : Fin n → Fin d) (width : Fin n → ℕ) (m : Memory W)
    (sC : src+3*n≤counters) (gC : groups+4*n≤counters) (cD : counters+d≤dst)
    (fits : dst+4*n<2^W) (good : Input src groups counters order key width m) :
    let o := image src groups counters dst n m
    (∀ i : Fin n, o (dst+4*i.val+3)=
       (earlier (key ∘ order) (width ∘ order) i.val (key (order i)) : Word W)) ∧
      ∀ a, (a<counters ∨ counters+d≤a) → (a<dst ∨ dst+4*n≤a) → o a=m a := by
  intro o
  let b (i : Fin n) : Bucket (Fin n) := ⟨order i,0,width (order i)⟩
  let target := row (key ∘ order) (width ∘ order)
  have pack : BucketRows.pack key (fun _=>0) (List.ofFn b)=List.ofFn target := by
    have step (i : Fin n) : BucketRows.bump key (earlier (key ∘ order) (width ∘ order) i.val) (b i) =
        earlier (key ∘ order) (width ∘ order) (i.val+1) := by
      funext g
      by_cases same : key (order i)=g
      · subst g
        simp [earlier,Finset.sum_range_succ,BucketRows.bump,b,Bucket.size,i.isLt]
      · simp [earlier,Finset.sum_range_succ,BucketRows.bump,b,Bucket.size,i.isLt,same,
          Ne.symm same]
    have start : earlier (key ∘ order) (width ∘ order) 0=fun _=>0 := by
      funext g
      simp [earlier]
    rw [←start]
    exact BucketRows.pack_ofFn key b (earlier (key ∘ order) (width ∘ order)) step
  obtain ⟨words,frame⟩ := BucketRegisters.walk_rows m src groups counters dst ((src+3*n:ℕ):Word W)
    key (fun _=>0) b target pack fits sC gC cD (fun i=>Nat.zero_le _) good.1 good.2.1 good.2.2
  exact ⟨fun i=>words i 3,frame⟩

/-- The bucket pass retains the total of all visits, including repeated visits
to a single edge, in its physical counter words. -/
theorem totals (src groups counters dst : ℕ) (order : Fin n→Fin n)
    (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory W)
    (sC : src+3*n≤counters) (gC : groups+4*n≤counters) (cD : counters+d≤dst)
    (fits : dst+4*n<2^W) (good : Input src groups counters order key width m) (g : Fin d) :
    image src groups counters dst n m (counters+g.val)=
      ((∑i : Fin n, if key (order i)=g then width (order i) else 0 : ℕ):Word W) := by
  let b (i : Fin n) : Bucket (Fin n) := ⟨order i,0,width (order i)⟩
  have stored := BucketRegisters.walk_counts_separated m src groups counters dst ((src+3*n:ℕ):Word W)
    key (fun _=>0) b fits (by omega) (by omega) (by omega) (.inl sC) (.inl (by omega)) (.inl gC)
    (.inl (by omega)) (.inl cD) (fun _=>Nat.zero_le _) good.1 good.2.1 good.2.2 g
  simpa [image,BucketRows.count,List.map_ofFn,List.sum_ofFn,b,Bucket.size] using stored

/-- Five startup instructions followed by the actual 23-instruction weighted bucket pass. -/
theorem prefix_spec (src groups counters dst : ℕ) (order : Fin n → Fin n)
    (key : Fin n → Fin d) (width : Fin n → ℕ)
    (sC : src+3*n≤counters) (gC : groups+4*n≤counters) (cD : counters+d≤dst)
    (fits : dst+4*n<2^W) :
    (procedure W src groups counters dst n).Spec (Input src groups counters order key width)
      (fun m o => (∀ i : Fin n, o (dst+4*i.val+3)=
        (earlier (key ∘ order) (width ∘ order) i.val (key (order i)) : Word W)) ∧
        ∀ a, (a<counters ∨ counters+d≤a) → (a<dst ∨ dst+4*n≤a) → o a=m a)
      (6+23*n) := by
  intro P R K M pc reg pub exit installed data c m entry good
  obtain ⟨t,ht,last,out,ran,done,eqn⟩ := run src groups counters dst n m (by omega) M
    pc reg pub exit installed data c m entry rfl
  subst out
  exact ⟨t,ht,last,_,ran,done,read_frame src groups counters dst order key width m sC gC cD fits good⟩

set_option maxRecDepth 8192 in
theorem cheap (W src groups counters dst count : ℕ) {P R K : ℕ}
    (pc : Fin 28 ↪ Fin P) (reg : Fin 12 ↪ Fin R) (pub : Fin 5→Fin K)
    (exit : Fin P) (i : Fin 28) :
    TaggedShorterCheapCPU.Cheap ((procedure W src groups counters dst count).block.emit pc reg pub exit i) := by
  fin_cases i <;> trivial

end Hierarchy.TaggedShorterCommonScan

end OAI
