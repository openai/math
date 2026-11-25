import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Routing.CallBatches
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # One native public lookup on a packed row of local occurrence states -/
namespace Hierarchy.DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open ThreeFlat.Routing
open scoped Classical BigOperators Fin.CommRing
noncomputable section

abbrev Cell (a : ℕ) := Fin (2^a)
def encode (a M : ℕ) : (Fin M→Cell a) ≃ Cell (a*M) :=
  finFunctionFinEquiv.trans (finCongr (pow_mul 2 a M).symm)

def digit (b i n : ℕ) := n%2^(b*(i+1))/2^(b*i)
theorem digit_encode {b M : ℕ} (x : Fin M→Cell b) (i : Fin M) :
    digit b i.val ((encode b M x).val)=(x i).val := by
  have inv:=congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply x) i)
  change (finFunctionFinEquiv x).val/(2^b)^i.val%(2^b)=(x i).val at inv
  simpa only [digit,Nat.mul_add,Nat.mul_one,pow_add,Nat.mod_mul_right_div_self,
    pow_mul] using (show (encode b M x).val/(2^b)^i.val%(2^b)=(x i).val from inv)

variable {a b M H r w : ℕ}
def table (f : Cell a→Cell b) (key : Cell (a*M)) : Cell (b*M) :=
  encode b M (f ∘ (encode a M).symm key)

def chunks (r M : ℕ) := poolBatchCount r M
abbrev Row (H r M : ℕ) := Fin H × Fin (chunks r M)
def row (H r M : ℕ) : Row H r M ≃ Fin (H*chunks r M) := finProdFinEquiv
def used (r M c : ℕ) := min M (r-c*M)
theorem active {c : ℕ} (i : Fin M) (hi : c*M+i.val<r) : i.val<used r M c :=
  lt_min i.isLt (by omega)

def data (x : Fin H→Fin r→Cell a) (p : Row H r M) : Cell (a*M) :=
  encode a M (fun i=>if hi : p.2.val*M+i.val<r then x p.1 ⟨_,hi⟩ else 0)

/-- A source pin reads one bit of one live occurrence, with false padding in
both the high part of the physical word and the incomplete final chunk. -/
private theorem width_pos {v a M : ℕ} (h : v<a*M) : 0<a := by
  cases a with
  | zero => simp at h
  | succ a => omega

def sourcePin (x : Fin H→Fin r→Cell a) (p : Row H r M) (s : Fin w) : Bool :=
  if h : s.val<a*M then
    if live : p.2.val*M+s.val/a<r then
      wordBits a (x p.1 ⟨_,live⟩) ⟨s.val%a,Nat.mod_lt _ (width_pos h)⟩
    else false
  else false

private theorem digit_bit (n a t j : ℕ) (lo : j<a) :
    (digit a t n).testBit j=n.testBit (j+a*t) := by
  have inside : j+a*t<a*(t+1) := by rw [Nat.mul_add,Nat.mul_one];omega
  simp [digit,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,inside]

theorem source_pin (x : Fin H→Fin r→Cell a) (p : Row H r M) (s : Fin w) (fit : a*M≤w) :
    wordBits w (((data x p).val : ℕ) : Word w) s=sourcePin x p s := by
  have bound : (data x p).val<2^w := (data x p).isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)
  rw [←Computability.VPVNP.LiveHeader.testBit_wordBits,Fin.val_cast_of_lt bound]
  by_cases hs : s.val<a*M
  · have ha : 0<a := width_pos hs
    let i : Fin M:=⟨s.val/a,(Nat.div_lt_iff_lt_mul ha).2 (by simpa [Nat.mul_comm] using hs)⟩
    have addr : s.val%a+a*i.val=s.val := Nat.mod_add_div ..
    have bits:=digit_bit (data x p).val a i.val (s.val%a) (Nat.mod_lt _ ha)
    rw [addr] at bits
    rw [←bits]
    have stored:=digit_encode (b:=a) (fun j : Fin M=>if h : p.2.val*M+j.val<r then x p.1 ⟨_,h⟩ else 0) i
    change digit a i.val (data x p).val=_ at stored
    rw [stored]
    by_cases live : p.2.val*M+s.val/a<r
    · simp [sourcePin,hs,i,live,←Computability.VPVNP.LiveHeader.testBit_wordBits]
    · simp [sourcePin,hs,i,live]
  · have high : (data x p).val<2^s.val :=
      (data x p).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [sourcePin,hs,Nat.testBit_lt_two_pow high]

def masked (f : Cell a→Cell b) (x : Fin H→Fin r→Cell a) (p : Row H r M) :=
  (table (M:=M) f (data x p)).val % 2^(b*used r M p.2.val)

theorem active_read (f : Cell a→Cell b) (x : Fin H→Fin r→Cell a) (p : Row H r M)
    (i : Fin M) (hi : p.2.val*M+i.val<r) :
    digit b i.val (masked f x p)=(f (x p.1 ⟨_,hi⟩)).val := by
  have part : 2^(b*(i.val+1)) ∣ 2^(b*used r M p.2.val) :=
    pow_dvd_pow _ (Nat.mul_le_mul_left _ (active i hi))
  unfold masked digit
  rw [Nat.mod_mod_of_dvd _ part]
  change digit b i.val ((encode b M _).val)=_
  rw [digit_encode]
  simp [Function.comp_apply,data,hi]

theorem padding_zero (f : Cell a→Cell b) (x : Fin H→Fin r→Cell a) (p : Row H r M) (i : Fin M)
    (pad : used r M p.2.val ≤ i.val) : digit b i.val (masked f x p)=0 := by
  have lt : masked f x p<2^(b*i.val) :=
    (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b pad))
  exact Nat.div_eq_of_lt ((Nat.mod_le _ _).trans_lt lt)

structure Banks where
  source : Bank
  dictionary : Bank
  mask : Bank

def lookup (g : Banks) : Expr :=
  .op .mask (.lookup g.dictionary (.lookup g.source .row)) (.lookup g.mask .row)

def program (g : Banks) (out H r M w : ℕ) := scan w out (H*chunks r M) (lookup g)

structure Fits (g : Banks) (a b M H r w out : ℕ) : Prop where
  source : g.source.Fits w out
  dictionary : g.dictionary.Fits w out
  mask : g.mask.Fits w out
  srcSize : H*chunks r M≤g.source.size
  dictBits : g.dictionary.bits=a*M
  maskSize : H*chunks r M≤g.mask.size
  output : out+H*chunks r M<2^w
  packed : M*max a b≤w/2

def maskWord (b M r c : ℕ) := 2^(b*used r M c)-1
def fixedWord (f : Cell a→Cell b) : Cell (a*M) ⊕ Fin (H*chunks r M) → Word w
  | .inl key=>((table f key).val : ℕ)
  | .inr j=>(maskWord b M r ((row H r M).symm j).2.val : ℕ)
def fixedAddr (g : Banks) : Cell (a*M) ⊕ Fin (H*chunks r M) → ℕ
  | .inl key=>g.dictionary.base+key.val
  | .inr j=>g.mask.base+j.val

def PinFrame (g : Banks) (f : Cell a→Cell b) (x : Fin H→Fin r→Cell a) (mem : Memory w) : Prop :=
  (∀ j : Cell (a*M) ⊕ Fin (H*chunks r M),∀i : Fin w,
    wordBits w (mem (fixedAddr g j)) i=wordBits w (fixedWord f j) i) ∧
  ∀ p : Row H r M,mem (g.source.base+(row H r M p).val)=((data x p).val : ℕ)

theorem pinFrame (g : Banks) (f : Cell a→Cell b) (x : Fin H→Fin r→Cell a) (m : Memory w)
    (fit : a*M≤w)
    (rom : ∀ j : Cell (a*M) ⊕ Fin (H*chunks r M),∀i : Fin w,
      wordBits w (m (fixedAddr g j)) i=wordBits w (fixedWord f j) i)
    (pins : ∀ p : Row H r M,∀ i : Fin w,
      wordBits w (m (g.source.base+(row H r M p).val)) i=sourcePin x p i) : PinFrame (M:=M) g f x m := by
  refine ⟨rom,fun p=>(wordBits w).injective (funext (fun i=>(pins p i).trans (source_pin x p i fit).symm))⟩

private theorem bank_read (g : Bank) (mem : Memory w) (i out : ℕ)
    (hi : i<g.size) (fit : g.Fits w out) : g.read mem (i : Word w)=mem (g.base+i) := by
  simp [Bank.read,Fin.val_cast_of_lt (hi.trans fit.2.1),Nat.mod_eq_of_lt hi]

theorem lookup_read (g : Banks) (out : ℕ) (fit : Fits g a b M H r w out) (f : Cell a→Cell b)
    (x : Fin H→Fin r→Cell a) (mem : Memory w) (frame : PinFrame (M:=M) g f x mem) (p : Row H r M) :
    (lookup g).eval mem ((row H r M p).val : Word w)=((masked f x p : ℕ) : Word w) := by
  have word (key : Cell (a*M) ⊕ Fin (H*chunks r M)) :
      mem (fixedAddr g key)=fixedWord f key := (wordBits w).injective (funext (frame.1 key))
  have dict : (data x p).val<g.dictionary.size := by simp [Bank.size,fit.dictBits]
  have outBits : b*M≤w := by
    have := (Nat.mul_le_mul_left M (le_max_right a b)).trans fit.packed
    rw [Nat.mul_comm] at this
    omega
  have wordFit : (table f (data x p)).val<2^w :=
    (table f (data x p)).isLt.trans_le (Nat.pow_le_pow_right (by decide) outBits)
  have keptFit : b*used r M p.2.val≤w :=
    (Nat.mul_le_mul_left _ (min_le_left ..)).trans outBits
  have maskFit : maskWord b M r p.2.val<2^w := by
    have upper : 2^(b*used r M p.2.val)≤2^w := Nat.pow_le_pow_right (by decide) keptFit
    have pos : 0<2^(b*used r M p.2.val) := by positivity
    unfold maskWord
    omega
  have rom : mem (g.dictionary.base+(data x p).val)=((table f (data x p)).val : ℕ) := word (.inl (data x p))
  have mask : mem (g.mask.base+(row H r M p).val)=(maskWord b M r p.2.val : ℕ) := by
    simpa [fixedAddr,fixedWord] using word (.inr (row H r M p))
  have andEq : (table f (data x p)).val &&& (((maskWord b M r p.2.val:ℕ):Word w)).val=masked f x p := by
    rw [Fin.val_cast_of_lt maskFit]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  simp only [lookup,Expr.eval,bank_read g.source _ _ out ((row H r M p).isLt.trans_le fit.srcSize) fit.source,
    frame.2,bank_read g.dictionary _ _ out dict fit.dictionary,rom,
    bank_read g.mask _ _ out ((row H r M p).isLt.trans_le fit.maskSize) fit.mask,mask,RowOp.opcode,
    Computability.VPVNP.BurstRAM.PrivateRAM.BinaryOp.eval,Fin.val_cast_of_lt wordFit,andEq]; rfl

theorem spec (g : Banks) (out : ℕ) (fit : Fits g a b M H r w out) (f : Cell a→Cell b)
    (x : Fin H→Fin r→Cell a) :
    (program g out H r M w).Spec (PinFrame (M:=M) g f x)
      (fun src after=>after=image out (H*chunks r M) (lookup g) src ∧
        ∀ p : Row H r M,after (out+(row H r M p).val)=((masked f x p : ℕ) : Word w))
      (4+(H*chunks r M)*(2*(lookup g).work+4)) ∧ CheapCode (program g out H r M w) := by
  refine ⟨?_,scan_cheap w out (H*chunks r M) (lookup g)⟩
  have fits : (lookup g).Fits w out := by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]
  intro P N K machine pc reg pub exit rom pubRegs cfg mem start input
  obtain ⟨time,clock,done,after,run,ended,hmem⟩:=scan_exec out (H*chunks r M) (lookup g) mem
    fits fit.output machine pc reg pub exit rom pubRegs cfg mem start rfl
  refine ⟨time,clock,done,after,run,ended,hmem,?_⟩
  intro p
  rw [hmem]
  have hi:=(row H r M p).isLt
  simpa [image,fillSegment,show out≤out+(row H r M p).val ∧
    out+(row H r M p).val<out+H*chunks r M by omega,Nat.cast_add] using lookup_read g out fit f x mem input p

/-- Every actual state occurrence has a physical row and a live lane, including
the incomplete final chunk at every host. -/
def position (v : Fin H) (j : Fin r) (pos : 0<M) : Row H r M :=
  (v,⟨j.val/M,(Nat.div_lt_iff_lt_mul pos).2 (by
    simpa [chunks,Nat.mul_comm] using j.isLt.trans_le (CallPool.count_le_batches_mul r M pos))⟩)

def lane (j : Fin r) (pos : 0<M) : Fin M := ⟨j.val%M,Nat.mod_lt _ pos⟩

theorem physical_read (g : Banks) (out : ℕ) (fit : Fits g a b M H r w out) (f : Cell a→Cell b)
    (x : Fin H→Fin r→Cell a) (after : Memory w)
    (stored : ∀ p : Row H r M,after (out+(row H r M p).val)=((masked f x p : ℕ) : Word w))
    (v : Fin H) (j : Fin r) (pos : 0<M) :
    digit b (lane j pos).val (after (out+(row H r M (position v j pos)).val)).val=(f (x v j)).val := by
  let p:=position v j pos
  let i:=lane j pos
  have coord : p.2.val*M+i.val=j.val := Nat.div_add_mod' ..
  have same := active_read f x p i (coord.trans_lt j.isLt)
  have bound : masked f x p<2^w := by
    have bits := (Nat.mul_le_mul_left M (le_max_right a b)).trans fit.packed
    rw [Nat.mul_comm] at bits
    have le : b*M≤w := by omega
    have stop : used r M p.2.val≤M := min_le_left ..
    exact (Nat.mod_lt _ (by positivity)).trans_le
      (Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_left b stop).trans le))
  change digit b i.val (after (out+(row H r M p).val)).val=_
  rw [stored,Fin.val_cast_of_lt bound]
  have slot : (⟨p.2.val*M+i.val,coord.trans_lt j.isLt⟩ : Fin r)=j := Fin.ext coord
  exact same.trans (congrArg (fun q=> (f (x v q)).val) slot)

/-- Use the maximum number of lanes occupying at most half of the native word. -/
def lanes (w unit : ℕ) := w/(2*unit)
theorem lanes_fit (w unit : ℕ) : lanes w unit*unit≤w/2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).2
  simpa [lanes,Nat.mul_assoc,Nat.mul_comm unit 2] using Nat.div_mul_le_self w (2*unit)

theorem occupancy (w unit : ℕ) (pos : 0<unit) (wide : 2*unit≤w) :
    0<lanes w unit ∧ w≤4*(lanes w unit)*unit := by
  have q : 0<lanes w unit := Nat.div_pos wide (by omega)
  refine ⟨q,?_⟩
  have rem:=Nat.mod_lt w (show 0<2*unit by omega)
  have eq:=Nat.div_add_mod w (2*unit)
  change w≤4*(w/(2*unit))*unit
  have basic : unit≤(w/(2*unit))*unit := by simpa only [lanes,Nat.one_mul] using Nat.mul_le_mul_right unit q
  nlinarith only [rem,eq,basic]

theorem volume (H r w unit : ℕ) (pos : 0<unit) (wide : 2*unit≤w) :
    (H*chunks r (lanes w unit))*w ≤ H*w+4*H*r*unit := by
  obtain ⟨hp,fill⟩:=occupancy w unit pos wide
  let M:=lanes w unit
  have bound := Nat.div_mul_le_self (r+M-1) M
  change chunks r M*M≤r+M-1 at bound
  cases count : chunks r M with
  | zero => simp
  | succ z =>
    have usedLanes : z*M≤r := by rw [count,Nat.succ_mul] at bound;omega
    have invoice:= (Nat.mul_le_mul_left z fill).trans (by
      calc z*(4*(lanes w unit)*unit)=4*(z*M)*unit := by dsimp [M];ring
           _ ≤ 4*r*unit := Nat.mul_le_mul_right unit (Nat.mul_le_mul_left _ usedLanes))
    rw [Nat.mul_succ]
    nlinarith only [Nat.mul_le_mul_left H invoice]

theorem rom_entries (a b w : ℕ) : 2^(a*lanes w (max a b))≤2^(w/2) := by
  apply Nat.pow_le_pow_right (by decide)
  rw [Nat.mul_comm]
  exact (Nat.mul_le_mul_left _ (le_max_left a b)).trans (lanes_fit ..)

@[simp] theorem lookup_work (g : Banks) : (lookup g).work=20 := rfl

/-- The mutable tape has one input, one mask and one output word per packed
chunk. The fixed dictionary is mounted once and shared by all host positions. -/
theorem invoice (g : Banks) (H r a b w : ℕ) (nonzero : 0 < max a b) (wide : 2*max a b≤w) :
    let M:=lanes w (max a b)
    (4+(H*chunks r M)*(2*(lookup g).work+4))*w ≤
      4*w+44*(H*w+4*H*r*(max a b)) ∧
    (2^(a*M)+3*(H*chunks r M))*w ≤
      2^(w/2)*w+3*(H*w+4*H*r*(max a b)) := by
  dsimp only
  have charged:=volume H r w (max a b) nonzero wide
  have dict:=Nat.mul_le_mul_right w (rom_entries a b w)
  rw [lookup_work]
  constructor <;> nlinarith only [charged,dict]

end
end Hierarchy.DescentSIMDLookup

end OAI
