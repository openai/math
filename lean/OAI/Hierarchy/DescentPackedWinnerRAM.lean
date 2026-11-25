import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedWinnerKey
import OAI.Hierarchy.DescentColonyCandidateHardware
import OAI.Hierarchy.DescentGLPermutationRAM
import OAI.Hierarchy.ProtocolRAMRowChoiceFits

namespace OAI
/-! # Publishing compact matching names and paints from the two selected RAM words -/

namespace Hierarchy.DescentColonies.PackedWinnerRAM
open PackedWinnerKey DescentGL DescentBinaryField DescentAffineColors DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {k w G H M : ℕ}

local notation "width" => (1+k*2^k)
abbrev Seed (k : ℕ) := Fin (2^k-1)
abbrev Slots (k : ℕ) := Block k × (Seed k × Candidate k)

def names (k : ℕ) : Slots k≃Fin (2^k*((2^k-1)*2^(k+1))) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def bank (lo M : ℕ) (x : Block k) (i : Seed k) (j : Candidate k) : Bank :=
  ⟨lo+(names k (x,(i,j))).val*2^(width*M),width*M⟩

def tableWords (k M : ℕ) := (2^k*((2^k-1)*2^(k+1)))*2^((1+k*2^k)*M)

def literal (hk : 0<k) (w M z : ℕ) : Word w :=
  let size := 2^(width*M)
  if h:z/size<2^k*((2^k-1)*2^(k+1)) then
    let s:Slots k := (names k).symm ⟨z/size,h⟩
    ((table (M:=M) (PackedWinnerKey.value hk s.2.1 s.2.2 s.1) ((z%size : ℕ) : Cell (width*M))).val : Word w)
  else 0

def mount (hk : 0<k) (lo w M : ℕ) (prior : Memory w) : Memory w :=
  initialMemory (lo+tableWords k M) (fun z=>if z<lo then prior z else literal hk w M (z-lo))

theorem mounted (hk : 0<k) (lo w M : ℕ) (prior : Memory w) (x : Block k) (i : Seed k) (j : Candidate k)
    (entry : Cell (width*M)) :
    mount hk lo w M prior ((bank lo M x i j).base+entry.val)=
      ((table (M:=M) (PackedWinnerKey.value hk i j x) entry).val : Word w) := by
  let s := 2^(width*M)
  let ix := names k (x,(i,j))
  have key : entry.val<s := entry.isLt
  have bound : ix.val*s+entry.val<tableWords k M :=
    (Nat.add_lt_add_left key _).trans_le (by simpa [tableWords,s,Nat.succ_mul] using Nat.mul_le_mul_right s ix.isLt)
  have quo : (ix.val*s+entry.val)/s=ix.val := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt key,Nat.zero_add]
  have remn : (ix.val*s+entry.val)%s=entry.val := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt key]
  change (if lo+ix.val*s+entry.val<lo+tableWords k M then
    if lo+ix.val*s+entry.val<lo then prior _ else literal hk w M (lo+ix.val*s+entry.val-lo) else _) = _
  rw [ite_eq_left (by omega),ite_eq_right (by omega),show lo+ix.val*s+entry.val-lo=ix.val*s+entry.val by omega]
  simp only [literal,←show s=2^(width*M) from rfl,quo,dite_eq_left ix.isLt,remn]
  simp [ix]

theorem mount_below (hk : 0<k) (lo w M : ℕ) (prior : Memory w) {z : ℕ} (low : z<lo) :
    mount hk lo w M prior z=prior z := by simp [mount,initialMemory,low,show z<lo+tableWords k M by omega]

def pointer (address : ℕ) : Expr := .lookup ⟨address,0⟩ (.lit 0)

/-- Both ordinal reads use the physical winner of the relevant first-minimum program. -/
def term (lo M seed paint : ℕ) (source : Seed k→Bank) (x : Block k) : Expr :=
  chooseField (2^k-1) 0 (fun i=>chooseField (2^(k+1)) 0 (fun j=>
    .lookup (bank lo M x i j) (.lookup (source i) .row)) (pointer paint)) (pointer seed)

theorem term_work (lo M seed paint : ℕ) (source : Seed k→Bank) (x : Block k) :
    (term lo M seed paint source x).work=work k := by
  exact DescentGLPermutationRAM.work_choose _ _ _ _ _ fun i=>
    DescentGLPermutationRAM.work_choose _ _ _ _ _ fun _=>rfl

def slot (out count : ℕ) (x : Block k) := out+x.val*count
def step (w lo out count M seed paint : ℕ) (source : Seed k→Bank) (x : Block k) : NativeBatch.Code w :=
  let f := term lo M seed paint source x
  let base := slot out count x
  ⟨scan w base count f,ProtocolRAM.image base count f,4+count*(2*f.work+4)⟩

def program (k w lo out H G M seed paint : ℕ) (source : Seed k→Bank) :=
  NativeBatch.Code.seq (step (k:=k) w lo out (H*chunks G M) M seed paint source) (2^k) le_rfl

structure Fits (k w lo out H G M seed paint : ℕ) (source : Seed k→Bank) : Prop where
  src : ∀i,(source i).Fits w out
  rows : ∀i,H*chunks G M≤(source i).size
  dictionaries : lo+tableWords k M≤out
  key : 2^((1+k*2^k)*M)<2^w
  codes : 2^(k+1)≤2^w
  seed : seed<out
  paint : paint<out
  finish : out+2^k*(H*chunks G M)<2^w
  wide : 1<2^w

private theorem bank_bound (lo M : ℕ) (x : Block k) (i : Seed k) (j : Candidate k) :
    (bank lo M x i j).base+(bank lo M x i j).size≤lo+tableWords k M := by
  change lo+(names k (x,(i,j))).val*2^(width*M)+2^(width*M)≤lo+(2^k*((2^k-1)*2^(k+1)))*2^(width*M)
  have bound:=Nat.mul_le_mul_right (2^(width*M)) (names k (x,(i,j))).isLt
  rw [Nat.succ_mul] at bound
  omega

theorem entry_low {lo «until» : ℕ} (room : lo+tableWords k M≤«until») (x : Block k) (i : Seed k) (j : Candidate k)
    (key : Cell ((1+k*2^k)*M)) : (bank lo M x i j).base+key.val<«until» :=
  (Nat.add_lt_add_left (show key.val<(bank lo M x i j).size from key.isLt) _).trans_le ((bank_bound ..).trans room)

private theorem weaken {x : Bank} {lo dest : ℕ} (f : x.Fits w lo) (h : lo≤dest) : x.Fits w dest :=
  ⟨f.1,f.2.1,f.2.2.trans h⟩

section
variable {lo out seed paint : ℕ} {source : Seed k→Bank} (fit : Fits k w lo out H G M seed paint source)
local notation "count" => H*chunks G M
local notation "run" => program k w lo out H G M seed paint source

include fit in
private theorem step_exec (x : Block k) : (step w lo out count M seed paint source x).exec := by
  intro m
  let dest := slot out count x
  have lower : out≤dest := Nat.le_add_right ..
  have bankFit (i : Seed k) (j : Candidate k) : (bank lo M x i j).Fits w dest :=
    ⟨Nat.two_pow_pos _,fit.key,(bank_bound ..).trans (fit.dictionaries.trans lower)⟩
  have control (z : ℕ) (hz : z<out) : (pointer z).Fits w dest := by
    refine ⟨⟨Nat.two_pow_pos 0,fit.wide,?_⟩,trivial⟩
    change z+1≤dest
    omega
  have safe : (term lo M seed paint source x).Fits w dest := by
    apply ProtocolRAM.BoughtSockets.choose_fits_bound
    · intro i
      apply ProtocolRAM.BoughtSockets.choose_fits_bound
      · intro j; exact ⟨bankFit i j,weaken (fit.src i) lower,trivial⟩
      · exact control paint fit.paint
    · exact control seed fit.seed
  have upper : dest+count≤out+2^k*count := by
    have bound := Nat.mul_le_mul_right count x.isLt
    dsimp [dest,slot]
    rw [Nat.succ_mul] at bound
    omega
  intro labels registers slots machine
  exact scan_exec dest count _ m safe (upper.trans_lt fit.finish) machine

include fit in
theorem exec : (run).exec := NativeBatch.Code.exec_seqAll _ (step_exec fit) _ _

theorem frame (m : Memory w) (z : ℕ) (hz : z<out) : (run).after m z=m z :=
  NativeBatch.Code.frame_seq (step w lo out count M seed paint source) z (fun x m=>
    ProtocolRAMGeneratedWrite.frame_image (slot out count x) count (term lo M seed paint source x) m z
      (Or.inl (hz.trans_le (Nat.le_add_right ..)))) m _ _

theorem frame_above (m : Memory w) (z : ℕ) (hz : out+2^k*count≤z) : (run).after m z=m z := by
  apply NativeBatch.Code.frame_seq
  intro x old
  have lim:=Nat.mul_le_mul_right count x.isLt
  rw [Nat.succ_mul] at lim
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inr (by dsimp [slot];omega))

variable (hk : 0<k) (i : Seed k) (j : Candidate k)
variable (panels : Fin H→Fin G→Cell (1+k*2^k))

/-- All input arrays are below the first written output. Each later block
therefore sees the same two selected ordinals and the same panel records. -/
structure Ready (m : Memory w) : Prop where
  multiplier : m seed=(i.val:Word w)
  affine : m paint=(j.val:Word w)
  source : ∀p:Row H G M,m ((source i).base+(row H G M p).val)=((data panels p).val:Word w)
  table : ∀(x : Block k) (i' : Seed k) (j' : Candidate k) (key : Cell ((1+k*2^k)*M)),
    m ((bank lo M x i' j').base+key.val)=((DescentSIMDLookup.table (M:=M) (PackedWinnerKey.value hk i' j' x) key).val:Word w)

private theorem typed_table {a b : ℕ} (f : Cell a→Cell b) (zero : f 0=0)
    (pnl : Fin H→Fin G→Cell a) (p : Row H G M) :
    table f (data pnl p)=data (fun v g=>f (pnl v g)) p := by
  unfold table data
  rw [Equiv.symm_apply_apply]
  apply congrArg (encode _ _)
  funext c
  simp only [Function.comp_apply]
  split <;> simp_all

include fit in
private theorem evaluate (m : Memory w) (ready : Ready (lo:=lo) (seed:=seed) (paint:=paint) (source:=source) (M:=M) hk i j panels m)
    (x : Block k) (p : Row H G M) :
    (term lo M seed paint source x).eval m ((row H G M p).val:Word w)=
      ((data (fun v g=>PackedWinnerKey.value hk i j x (panels v g)) p).val:Word w) := by
  let v:=((row H G M p).val:Word w)
  have ctl (pos : ℕ) (n : ℕ) (read : m pos=(n:Word w)) (room : n<2^w) :
      ((pointer pos).eval m v).val=0+n := by simp [pointer,Expr.eval,Bank.read,Bank.size,read,Fin.val_cast_of_lt room]
  have r1 : 2^k-1≤2^w := (Nat.sub_le _ _).trans ((Nat.pow_le_pow_right (by decide) (Nat.le_succ k)).trans fit.codes)
  rw [term,eval_chooseField _ _ _ _ _ _ i (by simpa using r1) (ctl _ _ ready.multiplier (i.isLt.trans_le r1))]
  rw [eval_chooseField _ _ _ _ _ _ j (by simpa using fit.codes) (ctl _ _ ready.affine (j.isLt.trans_le fit.codes))]
  have srcRoom := (row H G M p).isLt.trans_le (fit.rows i)
  have size : (bank lo M x i j).size=2^(width*M) := rfl
  change (bank lo M x i j).read m ((source i).read m v)=_
  rw [show (source i).read m v=m ((source i).base+(row H G M p).val) by simp [Bank.read,v,
    Fin.val_cast_of_lt (srcRoom.trans (fit.src i).2.1),Nat.mod_eq_of_lt srcRoom],ready.source]
  rw [show (bank lo M x i j).read m ((data panels p).val:Word w)=m ((bank lo M x i j).base+(data panels p).val) by
    simp [Bank.read,size,Fin.val_cast_of_lt ((data panels p).isLt.trans fit.key),Nat.mod_eq_of_lt (data panels p).isLt]]
  rw [ready.table,typed_table _ (PackedWinnerKey.value_zero hk i j x)]

include fit in
/-- Simultaneous local cell/side words for all genuine old block rows. -/
theorem published (m : Memory w) (ready : Ready (lo:=lo) (seed:=seed) (paint:=paint) (source:=source) (M:=M) hk i j panels m) :
    ∀(x : Block k) (p : Row H G M),
     (run).after m (slot out count x+(row H G M p).val)=
       ((data (fun v g=>PackedWinnerKey.value hk i j x (panels v g)) p).val:Word w) := by
  let tasks := step (k:=k) w lo out count M seed paint source
  let persistent (m' : Memory w) := ∀z<out,m' z=m z
  let outputs (x : Block k) (m' : Memory w) := ∀p : Row H G M,m' (slot out count x+(row H G M p).val)=
    ((data (fun v g=>PackedWinnerKey.value hk i j x (panels v g)) p).val:Word w)
  have unchanged (x : Block k) (m' : Memory w) (z : ℕ) (hz : z<out) : (tasks x).after m' z=m' z :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (hz.trans_le (Nat.le_add_right ..)))
  have still (m' : Memory w) (eqn : persistent m') : Ready (lo:=lo) (seed:=seed) (paint:=paint) (source:=source) (M:=M) hk i j panels m' :=
    ⟨(eqn _ fit.seed).trans ready.multiplier,(eqn _ fit.paint).trans ready.affine,
      fun p=>(eqn _ (by have b:=(row H G M p).isLt.trans_le (fit.rows i);have h:=(fit.src i).2.2;omega)).trans (ready.source p),
      fun x i' j' key=>(eqn _ (by have bound:=(bank_bound lo M x i' j').trans fit.dictionaries
                                  have sz : key.val<(bank lo M x i' j').size:=key.isLt
                                  omega)).trans (ready.table x i' j' key)⟩
  have all := NativeBatch.Code.read_seq tasks persistent
    (fun x m' low z hz=>(unchanged x m' z hz).trans (low z hz)) outputs (fun x m' low p=>
      (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M p)).trans (evaluate fit hk i j panels m' (still m' low) x p))
    (fun x y lt m' prior p=>by
      have next := Nat.mul_le_mul_right count lt
      rw [Nat.succ_mul] at next
      have less := (row H G M p).isLt
      have early : slot out count x+(row H G M p).val<slot out count y := by dsimp [slot];omega
      exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl early)).trans (prior p))
    m (fun _ _=>rfl) (2^k) le_rfl
  exact fun x=>all.2 x x.isLt

include fit in
theorem digit_read (m : Memory w) (ready : Ready (lo:=lo) (seed:=seed) (paint:=paint) (source:=source) (M:=M) hk i j panels m)
    (widthFit : (k+3)*M≤w) (hp : 0<M) (x : Block k) (v : Fin H) (g : Fin G) :
    digit (k+3) (lane g hp).val
      ((run).after m (slot out count x+(row H G M (position v g hp)).val)).val=
        (PackedWinnerKey.value hk i j x (panels v g)).val := by
  let p := position v g hp
  let lane' := lane g hp
  let localData := fun v g=>PackedWinnerKey.value hk i j x (panels v g)
  have coord : p.2.val*M+lane'.val=g.val := Nat.div_add_mod' ..
  have fitsWord : (data localData p).val<2^w := (data localData p).isLt.trans_le (Nat.pow_le_pow_right (by decide) widthFit)
  rw [published fit hk i j panels m ready x p,Fin.val_cast_of_lt fitsWord]
  change digit (k+3) lane'.val (data localData p).val=_
  unfold data
  rw [digit_encode]
  simp only [dite_eq_left (coord.trans_lt g.isLt)]
  apply congrArg (fun id => (localData v id).val)
  exact Fin.ext coord

end

theorem output_lanes (k w : ℕ) (hk : 0<k) : (k+3)*lanes w (1+k*2^k)≤w := by
  have one : 1≤2^k := Nat.two_pow_pos _
  have many : k≤k*2^k := by simpa using Nat.mul_le_mul_left k one
  have coarse : k+3≤2*(1+k*2^k) := by omega
  have step:=Nat.mul_le_mul_right (lanes w (1+k*2^k)) coarse
  calc
    _ ≤ _ := step
    _ = 2*(lanes w (1+k*2^k)*(1+k*2^k)) := by ring
    _ ≤ 2*(w/2) := Nat.mul_le_mul_left 2 (lanes_fit ..)
    _ ≤ _ := by omega

theorem bit_price_at (k w lo out H G seed paint a : ℕ) (source : Seed k→Bank) (positive : 0<a) (wide : 2*a≤w) :
    (program k w lo out H G (lanes w a) seed paint source).ticks*w ≤
      (4+2^k*(8+2*work k))*(w+H*w+4*H*G*a) := by
  let M := lanes w a
  let n := H*chunks G M
  have c := NativeBatch.Code.clock_seq (step (k:=k) w lo out n M seed paint source)
    (4+n*(2*work k+4)) (fun x=>by change 4+n*(2*(term lo M seed paint source x).work+4)≤_;rw [term_work]) (2^k) le_rfl
  have space := volume H G w a positive wide
  let upper := w+H*w+4*H*G*a
  have wn : n*w≤upper := space.trans (by dsimp [upper];omega)
  have wu : w≤upper := by dsimp [upper];omega
  apply (Nat.mul_le_mul_right w c).trans
  calc
    _ = 4*w+2^k*(4*w+(n*w)*(2*work k+4)) := by ring
    _ ≤ 4*upper+2^k*(4*upper+upper*(2*work k+4)) := by gcongr
    _ = _ := by dsimp [upper];ring

theorem bit_price (k w lo out H G seed paint : ℕ) (source : Seed k→Bank) (wide : 2*(1+k*2^k)≤w) :
    let a := 1+k*2^k
    (program k w lo out H G (lanes w a) seed paint source).ticks*w ≤
      (4+2^k*(8+2*work k))*(w+H*w+4*H*G*a) :=
  bit_price_at k w lo out H G seed paint (1+k*2^k) source (by omega) wide

theorem storage (k w lo out H G M seed paint : ℕ) (source : Seed k→Bank) (live : 0<H*chunks G M) :
    let P := program k w lo out H G M seed paint source
    CandidateRAM.Bounded P.text P.ticks :=
  CandidateRAM.batch_bound _ (fun _x=>CandidateRAM.scan_bound _ _ _ _ live) _ _

theorem table_words_le (k w : ℕ) :
    tableWords k (lanes w (1+k*2^k)) ≤ (2^k*((2^k-1)*2^(k+1)))*2^(w/2) := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
    (by simpa [Nat.mul_comm] using lanes_fit w (1+k*2^k)))

end
end Hierarchy.DescentColonies.PackedWinnerRAM

end OAI
