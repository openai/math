import OAI.Hierarchy.ProtocolRAMEndpointSort
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentTerminalOrder
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Native, stable radix sort of complete terminal-row references -/

namespace Hierarchy.DescentTerminalSortRAM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.BorderVNP.FragmentBucket
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Fin.CommRing

variable {w N A E O S : ℕ}

/-- Each pass stores N gathered keys, K counts, K+1 exclusive starts, and two
power-of-two banks of local and original row IDs. All are flat arrays. -/
def sortLayout (start N K : ℕ) : ProtocolRAMEndpointSort.Layout :=
  ⟨start,start+N,start+N+K,start+N+K+(K+1)⟩

def localBank (start N K bits : ℕ) : Bank := ⟨(sortLayout start N K).sorted,bits⟩
def outBank (start N K bits : ℕ) : Bank := ⟨(localBank start N K bits).base+2^bits,bits⟩
def limit (start N K bits : ℕ) := (outBank start N K bits).base+2^bits

theorem limit_eq (start N K bits : ℕ) :
    limit start N K bits=start+(N+2*K+1+2*(2^bits)) := by
  change start+N+K+(K+1)+2^bits+2^bits = start+(N+2*K+1+2*(2^bits))
  omega

/-- A first pass takes the identity array without materializing it. Every later pass
looks up the original ID by the preceding pass's dense reference column. -/
def original (previous : Option Bank) (i : Expr) : Expr :=
  match previous with
  | none => i
  | some b => .lookup b i

private theorem original_eval (previous : Option Bank) (i : Expr) (m : Memory w) (r : Word w) :
    (original previous i).eval m r=(original previous .row).eval m (i.eval m r) := by
  cases previous <;> rfl

def column (keyBank : Bank) (previous : Option Bank) := Expr.lookup keyBank (original previous .row)
def restore (start N K bits : ℕ) (previous : Option Bank) :=
  original previous (.lookup (localBank start N K bits) .row)

def step (w start N K bits : ℕ) (keyBank : Bank) (previous : Option Bank) :=
  ((scan w start N (column keyBank previous)).seq (ProtocolRAMEndpointSort.program (sortLayout start N K) w N K)).seq
    (scan w (outBank start N K bits).base N (restore start N K bits previous))

def cost (N K : ℕ) := 31+81*N+18*K

def staged (start N : ℕ) (keyBank : Bank) (previous : Option Bank) (m : Memory w) :=
  ProtocolRAM.image start N (column keyBank previous) m

def sorted (start : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) :=
  ProtocolRAMEndpointSort.image (sortLayout start N A) (fun i=>key (old i)) (staged start N keyBank previous m)

def stepImage (start bits : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) :=
  ProtocolRAM.image (outBank start N A bits).base N (restore start N A bits previous)
    (sorted start keyBank previous old key m)

private theorem bounds {start bits : ℕ} (nFits : N≤2^bits) (room : limit start N A bits<2^w) :
    (sortLayout start N A).Fits w N A := by
  simp only [limit,outBank,localBank,sortLayout] at room
  constructor <;> dsimp [sortLayout] <;> omega

private theorem prevFit {start : ℕ} (previous : Option Bank) (fits : ∀ b∈previous,b.Fits w start) :
    (original previous .row).Fits w start := by
  cases previous with
  | none => trivial
  | some b => exact ⟨fits b rfl,trivial⟩

private theorem before_sorted (start bits : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) (nFits : N≤2^bits) (room : limit start N A bits<2^w)
    (i : ℕ) (lo : i < start) : sorted start keyBank previous old key m i=m i := by
  have sortFit := bounds (A:=A) nFits room
  have fixed := ProtocolRAMEndpointSort.frame (sortLayout start N A) sortFit (fun i=>key (old i))
    (staged start N keyBank previous m) i (Or.inl (by change i < start+N;omega))
    (Or.inl (by change i < start+N+A;omega)) (Or.inl (by change i < start+N+A+(A+1);omega))
  exact fixed.trans (frame_image start N _ _ _ (Or.inl lo))

theorem step_frame (start bits : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) (nFits : N≤2^bits) (room : limit start N A bits<2^w)
    (i : ℕ) (lo : i < start) : stepImage start bits keyBank previous old key m i=m i := by
  have before : i<(outBank start N A bits).base := by simp only [outBank,localBank,sortLayout];omega
  exact (frame_image _ N _ _ i (Or.inl before)).trans
    (before_sorted start bits keyBank previous old key m nFits room i lo)

theorem bank_frame {w : ℕ} (a b : Memory w) (before : ℕ) (fixed : ∀ p < before,b p=a p)
    (bank : Bank) (low : bank.Fits w before) (i : Word w) : bank.read b i=bank.read a i := by
  apply fixed
  have bound := low.2.2
  have small := Nat.mod_lt i.val low.1
  omega

theorem step_read (start bits : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) (nFits : N≤2^bits) (room : limit start N A bits<2^w)
    (safe : ∀ b∈previous,b.Fits w start) (indices : ∀ i : Fin N,
      (original previous .row).eval m (i.val:Word w)=((old i).val:Word w)) (j : Fin N) :
    (outBank start N A bits).read (stepImage start bits keyBank previous old key m) (j.val:Word w)=
      (((perm old key) j).val:Word w) := by
  let t := sorted start keyBank previous old key m
  let s := (dest (fun i=>key (old i))).symm j
  have bj : j.val<2^bits := j.isLt.trans_le nFits
  have small : 2^bits<2^w := by simp only [limit,outBank,localBank,sortLayout] at room;omega
  have rb : (localBank start N A bits).read t (j.val:Word w)=(s.val:Word w) := by
    change t ((sortLayout start N A).sorted+(j.val:Word w).val%(2^bits))=_
    rw [Fin.val_cast_of_lt (bj.trans small),Nat.mod_eq_of_lt bj]
    exact ProtocolRAMEndpointSort.read _ (bounds nFits room) _ _ j
  change stepImage start bits keyBank previous old key m
    ((outBank start N A bits).base+(j.val:Word w).val%(2^bits))=_
  rw [Fin.val_cast_of_lt (bj.trans small),Nat.mod_eq_of_lt bj,
    show stepImage _ _ _ _ _ _ m ((outBank _ _ _ _).base+j.val)=(restore start N A bits previous).eval t (j.val:Word w)
      from read_image ..]
  rw [restore,original_eval]
  change (original previous .row).eval t ((localBank start N A bits).read t (j.val:Word w))=_
  rw [rb,eval_below _ _ m t (prevFit previous safe) (before_sorted start bits keyBank previous old key m nFits room)]
  exact indices s

theorem step_run (start bits : ℕ) (keyBank : Bank) (previous : Option Bank) (old : Fin N≃Fin N)
    (key : Fin N→Fin A) (m : Memory w) (nFits : N≤2^bits) (room : limit start N A bits<2^w)
    (keys : keyBank.Fits w start) (safe : ∀ b∈previous,b.Fits w start)
    (keyData : ∀ i : Fin N,keyBank.read m (i.val:Word w)=((key i).val:Word w))
    (indices : ∀ i : Fin N,(original previous .row).eval m (i.val:Word w)=((old i).val:Word w)) :
    (step w start N A bits keyBank previous).Exec m (stepImage start bits keyBank previous old key m)
      (cost N A) := by
  let a := staged start N keyBank previous m
  let t := sorted start keyBank previous old key m
  let L := sortLayout start N A
  let out := (outBank start N A bits).base
  have fitSort := bounds (A:=A) nFits room
  have ro : out+N<2^w := by change out+2^bits<2^w at room;omega
  have floor : start ≤ out := by dsimp [out,outBank,localBank,sortLayout];omega
  have ka : (column keyBank previous).Fits w start := ⟨keys,prevFit _ safe⟩
  have get : (scan w start N (column keyBank previous)).Exec m a (4+N*(2*(column keyBank previous).work+4)) :=
    scan_exec _ _ _ _ ka (by omega)
  have core : (ProtocolRAMEndpointSort.program L w N A).Exec a t (ProtocolRAMEndpointSort.cost N A) := by
    apply ProtocolRAMEndpointSort.run _ fitSort
    intro i
    rw [show a (L.src+i.val)=(column keyBank previous).eval m (i.val:Word w) from read_image ..]
    change keyBank.read m ((original previous .row).eval m (i.val:Word w))=_
    rw [indices i,keyData]
  have localFits : (localBank start N A bits).Fits w out := by
    change 0<2^bits ∧ 2^bits<2^w ∧ _+2^bits ≤ out
    have endLt : out+2^bits<2^w := room
    exact ⟨Nat.two_pow_pos _,by omega,le_rfl⟩
  have lift (b : Bank) (ok : b.Fits w start) : b.Fits w out :=
    ⟨ok.1,ok.2.1,ok.2.2.trans floor⟩
  have restoreFits : (restore start N A bits previous).Fits w out := by
    cases previous with
    | none => exact ⟨localFits,trivial⟩
    | some b => exact ⟨lift b (safe b rfl),localFits,trivial⟩
  have put : (scan w out N (restore start N A bits previous)).Exec t (stepImage start bits keyBank previous old key m)
      (4+N*(2*(restore start N A bits previous).work+4)) := scan_exec _ _ _ _ restoreFits ro
  have keyWork : (column keyBank previous).work≤12 := by
    cases previous <;> norm_num [column, original, Expr.work]
  have refWork : (restore start N A bits previous).work≤12 := by
    cases previous <;> norm_num [restore, original, Expr.work]
  have kBudget := Nat.mul_le_mul_left N (show 2*(column keyBank previous).work+4≤28 by omega)
  have rBudget := Nat.mul_le_mul_left N (show 2*(restore start N A bits previous).work+4≤28 by omega)
  have two : ((scan w start N (column keyBank previous)).seq (ProtocolRAMEndpointSort.program L w N A)).Exec m t
      ((4+N*(2*(column keyBank previous).work+4))+ProtocolRAMEndpointSort.cost N A) :=
    Procedure.Exec.then get core
  intro P R K mach pc reg pub exit inst data cfg raw entry eq
  obtain ⟨ticks,tickFit,c',m',adv,stop,value⟩ := Procedure.Exec.then two put
    mach pc reg pub exit inst data cfg raw entry eq
  rw [ProtocolRAMEndpointSort.cost_eq] at tickFit
  exact ⟨ticks,by unfold cost;omega,c',m',adv,stop,value⟩

def stage2 (start N side bits : ℕ) := limit start N side bits
def stage3 (start N side ordinal bits : ℕ) := limit (stage2 start N side bits) N ordinal bits
def output (start N side ordinal edge bits : ℕ) := outBank (stage3 start N side ordinal bits) N edge bits
def endAddress (start N side ordinal edge bits : ℕ) := limit (stage3 start N side ordinal bits) N edge bits

theorem end_eq (start N side ordinal edge bits : ℕ) :
    endAddress start N side ordinal edge bits=start+3*N+2*(side+ordinal+edge)+3+6*2^bits := by
  simp only [endAddress,stage3,stage2,limit_eq]
  omega

/-- Automatic pointer-bank width costs at most two words per source row and two extra
words for the empty case. -/
def mapBits (N : ℕ) := Nat.log 2 (N+1)+1

theorem mapBits_fits (N : ℕ) : N≤2^mapBits N :=
  (Nat.le_succ N).trans (Nat.lt_pow_succ_log_self (by decide) (N+1)).le

theorem workspace (start N side ordinal edge : ℕ) :
    endAddress start N side ordinal edge (mapBits N) ≤ start+15*N+2*(side+ordinal+edge)+15 := by
  have bound := Nat.pow_log_le_self 2 (show N+1≠0 by omega)
  rw [end_eq,mapBits,pow_succ]
  omega

def program (w start N side ordinal edge bits : ℕ) (edgeBank ordinalBank sideBank : Bank) :=
  let a := stage2 start N side bits
  let b := stage3 start N side ordinal bits
  ((step w start N side bits sideBank none).seq
    (step w a N ordinal bits ordinalBank (some (outBank start N side bits)))).seq
    (step w b N edge bits edgeBank (some (outBank a N ordinal bits)))

def time (N side ordinal edge : ℕ) := (cost N side+cost N ordinal)+cost N edge

theorem time_eq (N side ordinal edge : ℕ) : time N side ordinal edge=93+243*N+18*(side+ordinal+edge) := by
  unfold time cost
  omega

def state (start bits : ℕ) (e o s : Bank) (edge : Fin N→Fin E) (ordinal : Fin N→Fin O) (side : Fin N→Fin S)
    (m : Memory w) :=
  let a := stage2 start N S bits
  let b := stage3 start N S O bits
  let id := Equiv.refl (Fin N)
  let p := perm id side
  let q := perm p ordinal
  let one := stepImage start bits s none id side m
  let two := stepImage a bits o (some (outBank start N S bits)) p ordinal one
  stepImage b bits e (some (outBank a N O bits)) q edge two

/-- Three actual sequential bucket-sort programs, including their input-key gathers and
the three pointer compositions. The exposed final array is sorted-position to original row. -/
theorem run (start bits : ℕ) (e o s : Bank) (edge : Fin N→Fin E) (ordinal : Fin N→Fin O) (side : Fin N→Fin S)
    (m : Memory w) (nFits : N≤2^bits) (room : endAddress start N S O E bits<2^w)
    (ef : e.Fits w start) (ofit : o.Fits w start) (sf : s.Fits w start)
    (eData : ∀ i : Fin N,e.read m (i.val:Word w)=((edge i).val:Word w))
    (oData : ∀ i : Fin N,o.read m (i.val:Word w)=((ordinal i).val:Word w))
    (sData : ∀ i : Fin N,s.read m (i.val:Word w)=((side i).val:Word w)) :
    let after := state start bits e o s edge ordinal side m
    (program w start N S O E bits e o s).Exec m after (time N S O E) ∧
      (∀ j : Fin N,(output start N S O E bits).read after (j.val:Word w)=(((order edge ordinal side) j).val:Word w)) ∧
      ∀ x < start,after x=m x := by
  intro after
  let a := stage2 start N S bits
  let b := stage3 start N S O bits
  let i0 := Equiv.refl (Fin N)
  let i1 := perm i0 side
  let i2 := perm i1 ordinal
  let m1 := stepImage start bits s none i0 side m
  let b1 := outBank start N S bits
  let m2 := stepImage a bits o (some b1) i1 ordinal m1
  let b2 := outBank a N O bits
  have lo1 : start ≤ a := by unfold a stage2; rw [limit_eq];omega
  have lo2 : a ≤ b := by change a ≤ limit a N O bits;rw [limit_eq];omega
  have fin : limit b N E bits<2^w := room
  have w2 : b<2^w := by rw [limit_eq] at fin;omega
  have w1 : a<2^w := by omega
  have rng : 2^bits<2^w := by rw [limit_eq] at fin;omega
  have noneSafe : ∀ bank∈(none : Option Bank),bank.Fits w start := by simp
  have ids (j : Fin N) : (original none .row).eval m (j.val:Word w)=((i0 j).val:Word w) := rfl
  have p1 : (step w start N S bits s none).Exec m m1 (cost N S) :=
    step_run start bits s none i0 side m nFits w1 sf noneSafe sData ids
  have keep1 : ∀ x < start,m1 x=m x := step_frame start bits s none i0 side m nFits w1
  have id1 : ∀ j : Fin N,b1.read m1 (j.val:Word w)=((i1 j).val:Word w) :=
    step_read start bits s none i0 side m nFits w1 noneSafe ids
  have b1fit : b1.Fits w a := ⟨Nat.two_pow_pos _,rng,le_rfl⟩
  have b1safe : ∀ bank∈some b1,bank.Fits w a := by intro bank eq; cases eq;exact b1fit
  have lift (bank : Bank) (ok : bank.Fits w start) {high : ℕ} (le : start ≤ high) : bank.Fits w high :=
    ⟨ok.1,ok.2.1,ok.2.2.trans le⟩
  have p2 : (step w a N O bits o (some b1)).Exec m1 m2 (cost N O) :=
    step_run a bits o (some b1) i1 ordinal m1 nFits w2 (lift o ofit lo1) b1safe
      (fun j=>(bank_frame m m1 start keep1 o ofit _).trans (oData j)) id1
  have keep2 : ∀ x < a,m2 x=m1 x := step_frame a bits o (some b1) i1 ordinal m1 nFits w2
  have id2 : ∀ j : Fin N,b2.read m2 (j.val:Word w)=((i2 j).val:Word w) :=
    step_read a bits o (some b1) i1 ordinal m1 nFits w2 b1safe id1
  have b2fit : b2.Fits w b := ⟨Nat.two_pow_pos _,rng,le_rfl⟩
  have b2safe : ∀ bank∈some b2,bank.Fits w b := by intro bank eq; cases eq;exact b2fit
  have originals : ∀ x < start,m2 x=m x := fun x lo=>(keep2 x (lo.trans_le lo1)).trans (keep1 x lo)
  have p3 : (step w b N E bits e (some b2)).Exec m2 after (cost N E) :=
    step_run b bits e (some b2) i2 edge m2 nFits fin (lift e ef (lo1.trans lo2)) b2safe
      (fun j=>(bank_frame m m2 start originals e ef _).trans (eData j)) id2
  refine ⟨?_,step_read b bits e (some b2) i2 edge m2 nFits fin b2safe id2,?_⟩
  · have two : ((step w start N S bits s none).seq (step w a N O bits o (some b1))).Exec m m2
        (cost N S+cost N O) := Procedure.Exec.then p1 p2
    intro P R K mach pc reg pub exit inst data cfg raw entry eq
    exact Procedure.Exec.then two p3 mach pc reg pub exit inst data cfg raw entry eq
  · intro x lo
    exact (step_frame b bits e (some b2) i2 edge m2 nFits fin x (lo.trans_le (lo1.trans lo2))).trans (originals x lo)


end Hierarchy.DescentTerminalSortRAM

end OAI
