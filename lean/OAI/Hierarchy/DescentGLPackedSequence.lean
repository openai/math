import OAI.Hierarchy.DescentGLPackedShuffle
import OAI.Hierarchy.DescentGLNielsen
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # The full native passive inverse of the measured GL coordinate change -/
namespace Hierarchy.DescentGLPacked
open DescentSIMDLookup DescentGL DescentColonies DescentGLNielsen Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l b H w : ℕ}

def routeGate (g : Gate (h+l)) : Route (Bits h) (Bits l) :=
  xorRoute (finSumFinEquiv.symm g.target) (finSumFinEquiv.symm g.source)

theorem selected (g : Gate (h+l)) (go : Bool) (X : Fin H→Bits (h+l)→Cell b) (v : Fin H) (u : Bits h) (z : Bits l) :
    step (routeGate g) go (fun n a i=>X n (Fin.append a i)) v u z=X v (applyGate g go (Fin.append u z)) := by
  cases go with
  | false=>
    apply congrArg (X v)
    funext i
    simp [applyGate]
  | true=>
    apply congrArg (X v)
    change Fin.append _ _=applyGate g true (Fin.append u z)
    rw [show Fin.append ((routeGate g).pull (u,z)).1 ((routeGate g).pull (u,z)).2=
      bump (Fin.append u z) g.target ((Fin.append u z) g.source) from by
        simpa [routeGate] using append_xor (finSumFinEquiv.symm g.target) (finSumFinEquiv.symm g.source) (u,z)]
    funext i
    by_cases hit : i=g.target <;> simp [bump,applyGate,hit,Function.update]

structure Layout where
  bank : ℕ→Bank
  board : ℕ→Board
  flag : ℕ→Bank
  fresh : ℕ

def single (A : Layout) (H P s : ℕ) : Pass :=
  ⟨(A.bank (s+1)).base,H*P,lookup (A.board s) (A.bank s) (A.flag s)⟩

def steps (A : Layout) (H P : ℕ) (start : ℕ) : ℕ→List Pass
  | 0=>[]
  | n+1=>single A H P start::steps A H P (start+1) n

structure Hardware (A : Layout) (H h l b w n : ℕ) : Prop where
  room (j : ℕ) (hj : j<n) : Room (A.board j) (A.bank j) (A.flag j) b (2^l) H (2^h) w (A.bank (j+1)).base
  floor (j : ℕ) (hj : j<n) : A.fresh≤(A.bank (j+1)).base
  flag (j : ℕ) (hj : j<n) : (A.flag j).base<A.fresh
  left (j : ℕ) (hj : j<n) : (A.board j).left.base+H*2^h≤A.fresh
  right (j : ℕ) (hj : j<n) : (A.board j).right.base+H*2^h≤A.fresh
  variant (j : ℕ) (hj : j<n) : (A.board j).variant.base+H*2^h≤A.fresh
  shift (j : ℕ) (hj : j<n) : (A.board j).shift.base+2^(b*2^l)≤A.fresh
  table (j : ℕ) (hj : j<n) (f : Bool) : ((A.board j).table f).base+2^((b+b)*2^l)≤A.fresh

theorem static_frame (A : Layout) {n i : ℕ} (S : Hardware A H h l b w n) (ok : i<n)
    (g : Gate (h+l)) (m0 m : Memory w) (frame : ∀j,j<A.fresh→m j=m0 j)
    (real : Static (A.board i) (routeGate g) (address h) (address l) b H m0) :
    Static (A.board i) (routeGate g) (address h) (address l) b H m := by
  constructor
  · intro v x;exact (frame _ ((Nat.add_lt_add_left (ordinal (address h) v x).isLt _).trans_le (S.left i ok))).trans (real.left v x)
  · intro v x;exact (frame _ ((Nat.add_lt_add_left (ordinal (address h) v x).isLt _).trans_le (S.right i ok))).trans (real.right v x)
  · intro v x;exact (frame _ ((Nat.add_lt_add_left (ordinal (address h) v x).isLt _).trans_le (S.variant i ok))).trans (real.family v x)
  · intro x;exact (frame _ ((Nat.add_lt_add_left x.isLt _).trans_le (S.shift i ok))).trans (real.shift x)
  · intro f x;exact (frame _ ((Nat.add_lt_add_left x.isLt _).trans_le (S.table i ok f))).trans (real.tables f x)

def Setup (A : Layout) (b H start : ℕ) (items : List (Instruction (h+l))) (mem : Memory w) : Prop :=
  ∀i op,items[i]?=some op→Static (A.board (start+i)) (routeGate op.1) (address h) (address l) b H mem ∧
    mem (A.flag (start+i)).base=(op.2.toNat:Word w)

theorem execution (A : Layout) {n : ℕ} (S : Hardware A H h l b w n) (mem : Memory w)
    (start r : ℕ) (room : start+r≤n) :
    (program w (steps A H (2^h) start r)).Exec mem (result (steps A H (2^h) start r) mem) (clock (steps A H (2^h) start r)) ∧
    CheapCode (program w (steps A H (2^h) start r)) := by
  refine ⟨program_exec _ _ ?_,@ProtocolRAM.program_cheap _ _⟩
  intro p hp
  induction r generalizing start with
  | zero=>simp [steps] at hp
  | succ r ih=>
    simp only [steps,List.mem_cons] at hp
    rcases hp with rfl|rest
    · have z:=S.room start (by omega)
      exact ⟨eval_fits _ _ _ _ z,z.endFits⟩
    · exact ih (start+1) (by omega) rest

theorem run_read (A : Layout) {n : ℕ} (S : Hardware A H h l b w n) (orig : Memory w)
    (items : List (Instruction (h+l))) (start : ℕ) (m : Memory w) (within : start+items.length≤n)
    (X : Fin H→Bits (h+l)→Cell b) (old : Reads (A.bank start) (address h) (address l) (fun v u z=>X v (Fin.append u z)) m)
    (real : Setup A b H start items orig) (frame : ∀i,i<A.fresh→m i=orig i) :
    Reads (A.bank (start+items.length)) (address h) (address l)
      (fun v u z=>X v (applyList items.reverse (Fin.append u z)))
      (result (steps A H (2^h) start items.length) m) := by
  induction items generalizing start m X with
  | nil=>exact old
  | cons a rest ih=>
    let p:=single A H (2^h) start
    let next:=p.apply m
    have j : start<n:=by simp at within;omega
    have oracle:=real 0 a (by simp)
    simp only [Nat.add_zero] at oracle
    have f:=static_frame A S j a.1 orig m frame oracle.1
    have flag: m (A.flag start).base=(a.2.toNat:Word w):=(frame _ (S.flag _ j)).trans oracle.2
    have nextFrame (i : ℕ) (low : i<A.fresh) : next i=orig i := by
      have no:¬(A.bank (start+1)).base≤ i:=Nat.not_le.mpr (low.trans_le (S.floor _ j))
      simpa [next,p,single,Pass.apply,ProtocolRAM.image,fillSegment,no] using frame i low
    have updated : Reads (A.bank (start+1)) (address h) (address l)
        (fun v u z=>X v (applyGate a.1 a.2 (Fin.append u z))) next := by
      intro v u
      let id:=ordinal (address h) v u
      have inRange : (A.bank (start+1)).base≤(A.bank (start+1)).base+id.val ∧
          (A.bank (start+1)).base+id.val<(A.bank (start+1)).base+H*2^h:=by have:=id.isLt;omega
      have val:=read (A.board start) (A.bank start) (A.flag start) (A.bank (start+1)).base (S.room _ j)
        (routeGate a.1) (address h) (address l) (fun v u z=>X v (Fin.append u z)) a.2 m old f flag v u
      change next ((A.bank (start+1)).base+id.val)=_
      have row : step (routeGate a.1) a.2 (fun n hi lo => X n (Fin.append hi lo)) v u =
          (fun z => X v (applyGate a.1 a.2 (Fin.append u z))) :=
        funext (selected a.1 a.2 X v u)
      rw [row] at val
      simpa only [next,p,single,Pass.apply,ProtocolRAM.image,fillSegment,ite_eq_left inRange,
        Nat.cast_add,add_sub_cancel_left,id] using val
    have tail : Setup A b H (start+1) rest orig := by
      intro i op got
      simpa [Nat.add_assoc,Nat.add_comm 1 i] using real (i+1) op (by simpa using got)
    have full:=ih (start+1) next (by simp at within;omega) (fun v x=>X v (applyGate a.1 a.2 x)) updated tail nextFrame
    simpa [steps,ProtocolRAM.result,List.reverse_cons,DescentGLNielsen.apply_append,applyList,p,next,Nat.add_assoc,
      Nat.add_comm 1 rest.length] using full

theorem gl_read (A : Layout) (L : DescentGL.Layout (h+l)) (X : Fin H→Block (h+l)→Cell b)
    (m : Memory w) (S : Hardware A H h l b w (schedule (h+l)).length)
    (old : Reads (A.bank 0) (address h) (address l) (fun v u z=>X v (address (h+l) (Fin.append u z))) m)
    (real : Setup A b H 0 ((schedule (h+l)).zip (controls L)) m) :
    let n:=(schedule (h+l)).length
    Reads (A.bank n) (address h) (address l)
      (fun v u z=>X v ((rearrange L).symm (address (h+l) (Fin.append u z)))) (result (steps A H (2^h) 0 n) m) := by
  have len : ((schedule (h+l)).zip (controls L)).length=(schedule (h+l)).length := by
    rw [actual,←gates (h+l) L,List.length_map]
  have pub:=run_read A S m ((schedule (h+l)).zip (controls L)) 0 m (by rw [len];omega)
    (fun v z=>X v (address (h+l) z)) old real (fun _ _=>rfl)
  simp only [Nat.zero_add,len,realizes_inverse] at pub
  simpa [rearrange] using pub

theorem tariff (A : Layout) (H h start n : ℕ) :
    clock (steps A H (2^h) start n)≤4+n*(4+(H*2^h)*(2*110+4)) := by
  induction n generalizing start with
  | zero=>simp [steps,clock]
  | succ n ih=>
    have old:=ih (start+1)
    have term:=work (A.board start) (A.bank start) (A.flag start)
    let fee := 4 + H*2^h*(2*110+4)
    have one : (single A H (2^h) start).clock ≤ fee :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (H*2^h)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 term) 4)) 4
    calc
      _ ≤ fee + (4 + n*fee) := Nat.add_le_add one old
      _ = 4 + (n+1)*fee := by ring

end
end Hierarchy.DescentGLPacked

end OAI
