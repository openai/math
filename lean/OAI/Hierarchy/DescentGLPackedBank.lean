import OAI.Hierarchy.DescentGLPackedSequence
import OAI.Hierarchy.DescentGLControlCode
import OAI.Hierarchy.DescentGLPackedScale

namespace OAI
/-! # The fixed route tables and the measured per-step control share one real native image -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentSIMDLookup DescentGL DescentColonies DescentGLNielsen
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l H b w : ℕ}

structure Chart where
  start : ℕ
  bits : ℕ
  input : Bank
  flags : ℕ

def Chart.page (C : Chart) := 2^C.bits
def Chart.base (C : Chart) (j : ℕ) := C.start+j*C.page
def Chart.pageAt (C : Chart) (j : ℕ) : Bank := ⟨C.base j,C.bits⟩
def Chart.board (C : Chart) (s : ℕ) : Board :=
  ⟨C.pageAt (6*s),C.pageAt (6*s+1),C.pageAt (6*s+2),C.pageAt (6*s+3),
    fun f=>C.pageAt (6*s+(if f then 5 else 4))⟩
def Chart.heap (C : Chart) (d : ℕ) := C.base (6*(schedule d).length)
def Chart.chosen (C : Chart) (d : ℕ) : DescentGLPacked.Layout where
  board:=C.board
  flag:=fun i=>⟨C.flags+i,0⟩
  fresh:=C.heap d
  bank:=fun | 0=>C.input | s+1=>⟨C.heap d+s*C.page,C.bits⟩

abbrev Slot (d : ℕ) := Fin (schedule d).length × Fin 6
def addr (C : Chart) {d : ℕ} (slot : Slot d × Fin C.page) : ℕ :=
  C.base (finProdFinEquiv slot.1).val+slot.2.val

theorem addr_slot (C : Chart) {d : ℕ} (s : Fin (schedule d).length) (t : Fin 6) (z : Fin C.page) :
    addr C ((s,t),z)=C.base (6*s.val+t.val)+z.val := by
  change C.base (t.val+6*s.val)+z.val=_
  rw [Nat.add_comm t.val]

theorem addr_injective (C : Chart) (d : ℕ) :
    Function.Injective (addr C : Slot d×Fin C.page→ℕ) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ eq
  change C.start+(finProdFinEquiv p).val*C.page+i.val=C.start+(finProdFinEquiv q).val*C.page+j.val at eq
  have ij : i=j := by
    apply Fin.ext
    have rhs:=congrArg (·%C.page) (show (finProdFinEquiv p).val*C.page+i.val=(finProdFinEquiv q).val*C.page+j.val by omega)
    simpa [Nat.add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using rhs
  subst j
  have mult : (finProdFinEquiv p).val*C.page=(finProdFinEquiv q).val*C.page:=by omega
  have ne : C.page≠0:=Nat.ne_of_gt (Nat.two_pow_pos _)
  exact congrArg (fun x=>(x,i)) (finProdFinEquiv.injective (Fin.ext ((Nat.mul_left_inj ne).mp mult)))

def donor (name : Bits h≃Fin (2^h)) (R : Route (Bits h) (Bits l)) (r : Fin (H*2^h)) (right : Bool) : ℕ :=
  let q:=finProdFinEquiv.symm r
  (ordinal name q.1 ((if right then R.right else R.left) (name.symm q.2))).val

theorem donor_ordinal (name : Bits h≃Fin (2^h)) (R : Route (Bits h) (Bits l)) (v : Fin H) (x : Bits h) (f : Bool) :
    donor name R (ordinal name v x) f=(ordinal name v ((if f then R.right else R.left) x)).val := by
  simp [donor,ordinal]

def literal (H h l b w : ℕ) (cell : Slot (h+l)) (z : ℕ) : Word w :=
  let R:=routeGate (h:=h) (l:=l) ((schedule (h+l))[cell.1.val]'cell.1.isLt)
  match cell.2.val with
  | 0=>if ok:z<H*2^h then (donor (address h) R ⟨z,ok⟩ false:ℕ) else 0
  | 1=>if ok:z<H*2^h then (donor (address h) R ⟨z,ok⟩ true:ℕ) else 0
  | 2=>if ok:z<H*2^h then ((R.family ((address h).symm ((finProdFinEquiv.symm (⟨z,ok⟩:Fin (H*2^h))).2))).toNat:ℕ) else 0
  | 3=>(2^(b*2^l)*z:ℕ)
  | j+4=>if ok:z<2^((b+b)*2^l) then ((codec R (address l) (decide (0<j)) (⟨z,ok⟩:Cell ((b+b)*2^l))).val:ℕ) else 0

def Chart.install (C : Chart) (H h l b : ℕ) (m : Memory w) (z : ℕ) : Word w :=
  if e : ∃u : Slot (h+l)×Fin C.page,addr C u=z then literal H h l b w e.choose.1 e.choose.2.val else m z

theorem at_slot (C : Chart) (H h l b : ℕ) (m : Memory w) (s : Slot (h+l)) (i : Fin C.page) :
    C.install H h l b m (addr C (s,i))=literal H h l b w s i.val := by
  let hit : ∃u:Slot (h+l)×Fin C.page,addr C u=addr C (s,i):=⟨(s,i),rfl⟩
  rw [Chart.install,dite_eq_left hit,addr_injective C _ hit.choose_spec]

theorem stamped (C : Chart) (H h l b : ℕ) (mem : Memory w) (resident : ∀s : Slot (h+l),∀i : Fin C.page,
    mem (addr C (s,i))=literal H h l b w s i.val) : C.install H h l b mem=mem := by
  funext z
  unfold Chart.install
  split_ifs with found
  · exact (resident found.choose.1 found.choose.2).symm.trans (congrArg mem found.choose_spec)
  · rfl

theorem install_idem (C : Chart) (H h l b : ℕ) (mem : Memory w) :
    C.install H h l b (C.install H h l b mem)=C.install H h l b mem :=
  stamped C H h l b _ (at_slot C H h l b mem)

theorem low_frame (C : Chart) (H h l b : ℕ) (m : Memory w) {z : ℕ} (low : z<C.start) :
    C.install H h l b m z=m z := by
  rw [Chart.install,dite_eq_right]
  rintro ⟨u,eq⟩;unfold addr Chart.base at eq;omega

theorem high_frame (C : Chart) (H h l b : ℕ) (m : Memory w) {z : ℕ} (high : C.heap (h+l)≤z) :
    C.install H h l b m z=m z := by
  rw [Chart.install,dite_eq_right]
  rintro ⟨⟨q,i⟩,eq⟩
  have cap:=Nat.mul_le_mul_right C.page (finProdFinEquiv q).isLt
  change ((finProdFinEquiv q).val+1)*C.page≤((schedule (h+l)).length*6)*C.page at cap
  rw [Nat.succ_mul] at cap
  change C.start+(finProdFinEquiv q).val*C.page+i.val=z at eq
  change C.start+6*(schedule (h+l)).length*C.page≤z at high
  rw [Nat.mul_comm 6 (schedule (h+l)).length] at high
  have e:=i.isLt;omega

structure Size (C : Chart) (H h l b w : ℕ) : Prop where
  rows : H*2^h≤C.page
  shift : 2^(b*2^l)≤C.page
  combined : 2^((b+b)*2^l)≤C.page
  input : C.input.Fits w C.start
  inputSize : H*2^h≤C.input.size
  controls : C.flags+(schedule (h+l)).length≤C.start
  top : C.heap (h+l)+((schedule (h+l)).length+1)*C.page<2^w

theorem true_tables (C : Chart) (r : Size C H h l b w) (mem : Memory w) (i : Fin (schedule (h+l)).length) :
    Static (C.board i.val) (routeGate ((schedule (h+l))[i.val])) (address h) (address l) b H (C.install H h l b mem) := by
  let R:=routeGate (h:=h) (l:=l) ((schedule (h+l))[i.val])
  have read (j : Fin 6) (u : ℕ) (fits : u<C.page) :=
    at_slot C H h l b mem (i,j) ⟨u,fits⟩
  constructor
  · intro v x
    have e:=(ordinal (address h) v x).isLt
    simpa [Chart.board,Chart.pageAt,addr_slot,literal,e,donor_ordinal] using read 0 _ (e.trans_le r.rows)
  · intro v x
    have e:=(ordinal (address h) v x).isLt
    simpa [Chart.board,Chart.pageAt,addr_slot,literal,e,donor_ordinal] using read 1 _ (e.trans_le r.rows)
  · intro v x
    let row := ordinal (address h) v x
    have familyAt : literal H h l b w (i,2) row.val=((R.family x).toNat : Word w) := by
      change (if ok : row.val < H*2^h then
        ((R.family ((address h).symm (finProdFinEquiv.symm (⟨row.val,ok⟩ : Fin (H*2^h))).2)).toNat : Word w)
        else 0) = _
      rw [dite_eq_left row.isLt]
      change ((R.family ((address h).symm (finProdFinEquiv.symm (ordinal (address h) v x)).2)).toNat : Word w) = _
      simp only [ordinal,Equiv.symm_apply_apply]
    change C.install H h l b mem (C.base (6*i.val+2)+row.val) = ((R.family x).toNat : Word w)
    have familySlot : (2 : Fin 6).val = 2 := by decide
    simpa only [addr_slot,familySlot] using
      (read 2 row.val (row.isLt.trans_le r.rows)).trans familyAt
  · intro x
    simpa [Chart.board,Chart.pageAt,addr_slot,literal] using read 3 x.val (x.isLt.trans_le r.shift)
  · intro f x
    cases f <;> first
    | simpa [Chart.board,Chart.pageAt,addr_slot,literal,x.isLt] using read 4 x.val (x.isLt.trans_le r.combined)
    | simpa [Chart.board,Chart.pageAt,addr_slot,literal,x.isLt] using read 5 x.val (x.isLt.trans_le r.combined)

theorem hardware (C : Chart) (r : Size C H h l b w) :
    Hardware (C.chosen (h+l)) H h l b w (schedule (h+l)).length := by
  let n:=(schedule (h+l)).length
  have whole : C.start≤C.heap (h+l):=Nat.le_add_right ..
  have pageBound : C.page<2^w := by have:=r.top;rw [Nat.succ_mul] at this;omega
  have one : 1<2^w := (Nat.one_le_of_lt (Nat.two_pow_pos _)).trans_lt pageBound
  have endAt (s : ℕ) (hs:s<n) (t : ℕ) (small : t<6) : (C.pageAt (6*s+t)).base+C.page≤C.heap (h+l) := by
    have e : 6*s+t+1≤6*n:=by omega
    have last:=Nat.mul_le_mul_right C.page e
    rw [Nat.succ_mul] at last
    change C.start+(6*s+t)*C.page+C.page≤C.start+6*n*C.page
    omega
  have safe (s : ℕ) (hs:s<n) (j : ℕ) (small : j<6) :
      (C.pageAt (6*s+j)).Fits w (C.heap (h+l)+s*C.page) :=
    ⟨Nat.two_pow_pos _,pageBound,(endAt s hs j small).trans (Nat.le_add_right ..)⟩
  have table (s : ℕ) (hs:s<n) (f : Bool) : ((C.board s).table f).base+2^((b+b)*2^l)≤C.heap (h+l) := by
    cases f <;> exact (Nat.add_le_add_left r.combined _).trans (endAt s hs _ (by decide))
  constructor
  · intro s hs
    have z : s<n:=hs
    have stored : ((C.chosen (h+l)).bank s).Fits w (C.heap (h+l)+s*C.page) := by
      cases s with
      | zero=>exact ⟨r.input.1,r.input.2.1,r.input.2.2.trans (whole.trans (Nat.le_add_right ..))⟩
      | succ t=>exact ⟨Nat.two_pow_pos _,pageBound,by change C.heap (h+l)+t*C.page+C.page≤C.heap (h+l)+(t+1)*C.page;rw [Nat.succ_mul,Nat.add_assoc]⟩
    have src : H*2^h≤((C.chosen (h+l)).bank s).size := by cases s <;> first | exact r.inputSize | exact r.rows
    have flag : C.flags+s+1≤C.start:=by have:=r.controls;omega
    have endOut: C.heap (h+l)+s*C.page+H*2^h<2^w := by
      have next:s*C.page+C.page≤(n+1)*C.page:=by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right C.page (by omega : s+1≤n+1)
      calc
        _ ≤ C.heap (h+l)+s*C.page+C.page := Nat.add_le_add_left r.rows _
        _ = C.heap (h+l)+(s*C.page+C.page) := Nat.add_assoc ..
        _ ≤ C.heap (h+l)+(n+1)*C.page := Nat.add_le_add_left next _
        _ < 2^w := r.top
    refine ⟨stored,⟨Nat.zero_lt_one,one,flag.trans (whole.trans (Nat.le_add_right ..))⟩,
      ?_,safe s z 1 (by decide),safe s z 2 (by decide),safe s z 3 (by decide),?_,src,
      r.rows,r.rows,r.rows,r.shift,fun _=>r.combined,endOut⟩
    · change (C.pageAt (6*s)).Fits w (C.heap (h+l)+s*C.page)
      exact safe s z 0 (by decide)
    · intro f;cases f <;> exact safe s z _ (by decide)
  · intro s _;exact Nat.le_add_right ..
  · intro i hi;have:=r.controls;change C.flags+i<C.heap (h+l);omega
  · intro s hs
    change (C.pageAt (6*s)).base+H*2^h≤C.heap (h+l)
    exact (Nat.add_le_add_left r.rows _).trans (endAt s hs 0 (by decide))
  · intro s hs;exact (Nat.add_le_add_left r.rows _).trans (endAt s hs 1 (by decide))
  · intro s hs;exact (Nat.add_le_add_left r.rows _).trans (endAt s hs 2 (by decide))
  · intro s hs;exact (Nat.add_le_add_left r.shift _).trans (endAt s hs 3 (by decide))
  · exact table

theorem setup_of_read (A : DescentGLPacked.Layout) (L : DescentGL.Layout (h+l)) (mem : Memory w)
    (tables : ∀i : Fin (schedule (h+l)).length,
      Static (A.board i.val) (routeGate ((schedule (h+l))[i.val])) (address h) (address l) b H mem)
    (control : ∀i : Fin (schedule (h+l)).length,mem (A.flag i.val).base=((DescentGLControlCode.liveFlag L i).toNat:Word w)) :
    Setup A b H 0 ((schedule (h+l)).zip (controls L)) mem := by
  intro j op hit
  obtain ⟨inside,eq⟩:=List.getElem?_eq_some_iff.mp hit
  have js : j<(schedule (h+l)).length:=by have:=inside;simp [List.length_zip] at this;omega
  have jc : j<(controls L).length:=by have:=inside;simp [List.length_zip] at this;omega
  have pair : op=((schedule (h+l))[j],(controls L)[j]) := by simpa [List.getElem_zip] using eq.symm
  subst op
  refine ⟨by simpa using tables ⟨j,js⟩,?_⟩
  simpa [DescentGLControlCode.liveFlag,List.getElem?_eq_getElem jc] using control ⟨j,js⟩

theorem setup (C : Chart) (r : Size C H h l b w) (L : DescentGL.Layout (h+l)) (mem : Memory w)
    (control : ∀i : Fin (schedule (h+l)).length,mem (C.flags+i.val)=((DescentGLControlCode.liveFlag L i).toNat:Word w)) :
    Setup (C.chosen (h+l)) b H 0 ((schedule (h+l)).zip (controls L)) (C.install H h l b mem) := by
  apply setup_of_read _ L _ (true_tables C r mem)
  intro i
  have lower:C.flags+i.val<C.start:=by have:=r.controls;have:=i.isLt;omega
  simpa [Chart.chosen,low_frame C H h l b mem lower] using control i

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
