import OAI.Hierarchy.DescentTerminalBookCompaction
import OAI.Hierarchy.DescentTerminalBookPublish
import OAI.Hierarchy.DescentTerminalPointerGather
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # Six physical bounded lookups from the reached signed, frozen and venue shelves -/
namespace Hierarchy.DescentTerminalLocalPortBook.Print
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalRecipeRows ProtocolRAM ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout (L:ℕ) where
  start:ℕ
  homes:ℕ
  bits:ℕ
  source:Fin L→Expr

namespace Layout
variable {L G V A:ℕ} (P:Layout L)
def padH:=2^Nat.clog 2 P.homes
def band:=L*P.homes+P.padH+DescentTerminalPointerFrame.size L P.bits+P.padH
def origin (i:ℕ):=P.start+i*P.band
def rom (i:ℕ):=Gather.rom (P.origin i) L P.homes
def bank (i:ℕ):Bank:=⟨P.rom i+DescentTerminalPointerFrame.size L P.bits,Nat.clog 2 P.homes⟩
def stop:=P.origin 6
def passes (i:ℕ):=Gather.reads (P.origin i) P.homes P.source

variable (decode : (Fin L→Cell P.bits)→Directory G V A) (M:ℕ)
def field (j:Fin 6) (z:Fin L→Cell P.bits) : Cell (Nat.clog 2 (Book.capacities G V M A (nameBits G M) j)) :=
  let a:=Book.slot ((decode z).book M) j
  ⟨a.val,a.isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩
def one (w:ℕ) (i:Fin 6) := (ProtocolRAM.program w (P.passes i.val)).seq
  (DescentTerminalPointerFrame.program w (P.rom i.val) (Gather.banks (L:=L) (P.origin i.val) P.homes)
    P.homes (P.field decode M i))
def oneMem {w:ℕ} (i:Fin 6) (m:Memory w) :=
  DescentTerminalPointerFrame.result (P.rom i.val) (Gather.banks (L:=L) (P.origin i.val) P.homes)
    P.homes (P.field decode M i) (result (P.passes i.val) m)
def oneTime (i:Fin 6):=clock (P.passes i.val)+(4+10*DescentTerminalPointerFrame.size L P.bits)+
  (4+P.homes*(16+26*L))
def «prefix» (P : Layout L) (decode : (Fin L→Cell P.bits)→Directory G V A) (M w:ℕ) :
    (n:ℕ)→n≤6→Procedure w
  | 0,_=>ProtocolRAM.program w []
  | n+1,h=>(«prefix» P decode M w n (by omega)).seq (P.one decode M w ⟨n,by omega⟩)
def memory (P : Layout L) (decode : (Fin L→Cell P.bits)→Directory G V A) (M:ℕ)
    {w:ℕ} (m:Memory w) : (n:ℕ)→n≤6→Memory w
  | 0,_=>m
  | n+1,h=>P.oneMem decode M ⟨n,by omega⟩ (memory P decode M m n (by omega))
def time (P : Layout L) : (n:ℕ)→n≤6→ℕ
  | 0,_=>4
  | n+1,h=>time P n (by omega)+P.oneTime ⟨n,by omega⟩

theorem end_bank (i:ℕ):(P.bank i).base+P.padH=P.origin (i+1):=by
  simp only [bank,rom,Gather.rom,DescentOperandStateBanks.guard,origin,band,padH,Nat.add_mul,Nat.one_mul]
  omega

theorem native {w:ℕ} (m:Memory w) (fits:∀j,(P.source j).Fits w P.start)
    (offset:2^P.bits<2^w) (space:P.stop<2^w) (n:ℕ) (hn:n≤6) :
    let mem:=P.memory decode M m n hn
    (P.prefix decode M w n hn).Exec m mem (P.time n hn) ∧ CheapCode (P.prefix decode M w n hn) ∧
    (∀a,a<P.start→mem a=m a) ∧
    ∀(i:Fin 6),i.val<n→∀h:Fin P.homes,mem ((P.bank i.val).base+h.val)=
      ((Book.columns ((decode (Gather.values P.source m h)).book M) i):Word w) := by
  induction n with
  | zero=>
    exact ⟨ProtocolRAM.program_exec [] m (by simp),@ProtocolRAM.program_cheap _ _,fun _ _=>rfl,by simp⟩
  | succ n ih=>
    let id:Fin 6:=⟨n,by omega⟩
    let before:=P.memory decode M m n (by omega)
    obtain ⟨old,cheap,keep,fields⟩:=ih (by omega)
    have chain {i j:ℕ} (h:i≤j):P.origin i≤P.origin j:=by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
    have low:P.start≤P.origin n:=Nat.le_add_right ..
    have pad:P.homes≤P.padH:=Nat.le_pow_clog (by decide) _
    have next:=P.end_bank n
    have fit: (P.bank n).base+P.homes<2^w:=by
      have last:=chain hn
      change P.origin 6<2^w at space
      omega
    obtain ⟨run,fee,out,frame⟩:=Gather.execute (P.origin n) P.homes P.source (P.field decode M id) before
      (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ low (fits j)) offset fit
    refine ⟨?_,cheap_seq cheap fee,fun a ha=>(frame a (.inl (ha.trans_le low))).trans (keep _ ha),?_⟩
    · have stepTime : P.oneTime id = clock (P.passes n) +
          ((4+10*DescentTerminalPointerFrame.size L P.bits)+(4+P.homes*(16+26*L))) :=
        Nat.add_assoc _ _ _
      change ((P.prefix decode M w n (by omega)).seq (P.one decode M w id)).Exec m
        (P.oneMem decode M id before) (P.time n (by omega) + P.oneTime id)
      rw [stepTime]
      exact old.then run
    · intro i hi h
      by_cases last:i.val=n
      · have eqn:i=id:=Fin.ext last
        subst i
        have read:Gather.values (d:=P.bits) P.source before h=Gather.values P.source m h:=by
          funext j
          have keepExpr:=(show Below P.start before m from keep).expr (P.source j) (h.val:Word w) (fits j) le_rfl
          exact congrArg (fun x : Word w => (x.val : Cell P.bits)) keepExpr
        exact (out h).trans (congrArg (fun z => (Book.columns ((decode z).book M) id : Word w)) read)
      · have earlier:=chain (show i.val+1≤n by omega)
        have lane:=P.end_bank i.val
        have below:(P.bank i.val).base+h.val<P.origin n:=by have hlt:=h.isLt;omega
        exact (frame _ (.inl below)).trans (fields i (by omega) h)

def parts (weights:Fin 6→Bank) : Book.Parts:=fun i=>⟨P.bank i.val,weights i⟩

theorem issued {w:ℕ} (m:Memory w) (fits:∀j,(P.source j).Fits w P.start)
    (offset:2^P.bits<2^w) (space:P.stop<2^w)
    (t : Fin P.homes→Site) (room:∀i,Room (t i) G V M A)
    (geometry:∀i,Aligned (t i) (decode (Gather.values P.source m i)))
    (weights : Fin 6→Bank) (old:∀j,(weights j).base+(weights j).size≤P.start)
    (values:∀j (k:Fin (Book.capacities G V M A (nameBits G M) j)),
      (weights j).read m (k.val:Word w)=((k.val*Book.strides G V M A (nameBits G M) j:ℕ):Word w)) :
    Book.Issued (P.parts weights) (fun i=>issue (t i) (room i) (rowName (t i) (room i)) (refName (t i) (room i)))
      (P.memory decode M m 6 le_rfl) := by
  obtain ⟨_,_,keep,fields⟩:=P.native decode M m fits offset space 6 le_rfl
  constructor
  · intro h j
    have addr:=P.end_bank j.val
    have last:P.origin (j.val+1)≤P.stop:=by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
    have byte:P.homes≤P.padH:=Nat.le_pow_clog (by decide) _
    have inner:h.val<(P.bank j.val).size:=h.isLt.trans_le byte
    have narrow:h.val<2^w:=by omega
    have read:=fields j j.isLt h
    change (P.bank j.val).read _ _=_
    rw [Bank.read,Fin.val_cast_of_lt narrow,Nat.mod_eq_of_lt inner]
    exact read.trans (congrArg (fun book=>((Book.columns book j):Word w)) ((geometry h).authentic (room h)))
  · intro j u
    exact ((show Below P.start (P.memory decode M m 6 le_rfl) m from keep).bank (weights j) _ (old j)).trans (values j u)

end Layout
end
end Hierarchy.DescentTerminalLocalPortBook.Print

end OAI
