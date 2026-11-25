import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # Gathering fixed many measured digits and applying either of two literal laws -/
namespace Hierarchy.DescentOperandPairBook
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {n b field H G M w : ℕ}
abbrev Laws (n field b : ℕ) := Bool→(Fin n→Cell field)→Cell b

def kernel (f : Laws n field b) (s : Bool) (pack : Cell (field*n)) (_ : Cell 0) :=
  f s ((encode field n).symm pack)

private theorem kernel_zero (f : Laws n field b) (dead : ∀s,f s (fun _=>0)=0) (s : Bool) :
    kernel f s 0 0=0 := by
  have blank : encode field n (fun _=>0)=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell field))).val=0
    simp []
  exact (congrArg (f s) ((encode field n).symm_apply_eq.mpr blank.symm)).trans
    (dead s)

def gates (f : Laws n field b) : Fin (n+2)→Book.Gate :=
  Fin.cases ⟨field*n,0,b,kernel f false⟩
    (Fin.cases ⟨field*n,0,b,kernel f true⟩
      (fun i=>⟨field*n,field,field*n,Gather.setField i⟩))

def unit (n field : ℕ) := field*n+field
def words (n field M : ℕ) := (n+2)*(2*2^(unit n field*M))
def gather (f : Laws n field b) (M base : ℕ) (i : Fin n) :=
  Book.tables (gates f) (unit n field) M base i.succ.succ
def sideId (n : ℕ) : Bool→Fin (n+2)
  | false => 0
  | true => (0 : Fin (n+1)).succ
def finish (f : Laws n field b) (M base : ℕ) (s : Bool) :=
  Book.tables (gates f) (unit n field) M base (sideId n s)
def expr (f : Laws n field b) (M base : ℕ) (s : Bool) (src : Fin n→Expr) :=
  (finish f M base s).read (Gather.assembly (gather f M base) src) (.lit 0)
def program (f : Laws n field b) (M w base : ℕ) := Book.install (gates f) (unit n field) M w base
def memory (f : Laws n field b) (M base : ℕ) (m : Memory w) := Book.image (gates f) (unit n field) M base m

private theorem capacity (f : Laws n field b) (j : Fin (n+2)) :
    (gates f j).left+(gates f j).right≤unit n field := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun k=>?_) i) j
  · exact Nat.add_le_add_left (Nat.zero_le field) _
  · exact Nat.add_le_add_left (Nat.zero_le field) _
  · exact le_rfl

theorem mounted (f : Laws n field b) (M base : ℕ) (m : Memory w) (room : base+words n field M<2^w) :
    let mid:=memory f M base m
    (program f M w base).Exec m mid (4+10*words n field M) ∧
    (∀i,Static (gather f M base i) (Gather.setField (d:=field) i) M mid) ∧
    (∀s,Static (finish f M base s) (kernel f s) M mid) ∧
    (∀x,x<base ∨ base+words n field M≤x→mid x=m x) ∧ CheapCode (program f M w base) := by
  obtain ⟨run,read,keep,cheap⟩:=Book.mount (gates f) (unit n field) M base m (capacity f) room
  refine ⟨run,fun i=>by simpa only [memory,gather,gates,Fin.cases_succ] using read i.succ.succ,?_,keep,cheap⟩
  intro s
  cases s with
  | false => simpa only [memory,finish,sideId,gates,Fin.cases_zero,Fin.cases_succ] using read (sideId n false)
  | true => simpa only [memory,finish,sideId,gates,Fin.cases_zero,Fin.cases_succ] using read (sideId n true)

theorem expr_fits (f : Laws n field b) (s : Bool) (base : ℕ) (src : Fin n→Expr)
    (fit : ∀i,(src i).Fits w base) (room : base+words n field M<2^w) :
    (expr f M base s src).Fits w (base+words n field M) := by
  let top:=base+words n field M
  have shape (id : Fin (n+2)):=Book.geometry (gates f) (unit n field) M base id
    (out:=top) le_rfl room (capacity f id)
  have bounds : Gather.Bounds (w:=w) (d:=field) (M:=M) (gather f M base) src top := by
    intro i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (fit i),
      (shape i.succ.succ).1,(shape i.succ.succ).2,rfl,rfl⟩
  have g:=shape (sideId n s)
  have ok : DescentPackedZip.Fits (finish f M base s) (Gather.assembly (gather f M base) src)
      (.lit 0) (field*n) 0 M top w := by
    refine ⟨Gather.fits _ _ _ bounds _,trivial,g.1,g.2,?_,?_⟩ <;> cases s <;> rfl
  exact ⟨ok.apply,⟨ok.right,⟨ok.shift,ok.left⟩⟩⟩

theorem issued (f : Laws n field b) (dead : ∀s,f s (fun _=>0)=0) (s : Bool) (base : ℕ)
    (src : Fin n→Expr) (m : Memory w) (x : Fin H→Fin G→Fin n→Cell field)
    (fit : ∀i,(src i).Fits w base) (dataAt : ∀i,Source (src i) (fun v g=>x v g i) M m)
    (room : base+words n field M<2^w) :
    let e:=expr f M base s src
    e.Fits w (base+words n field M) ∧ Source e (fun v g=>f s (x v g)) M (memory f M base m) := by
  let top:=base+words n field M
  let mid:=memory f M base m
  have bound:=Nat.le_add_right base (words n field M)
  have install:=mounted f M base m room
  have shape (id : Fin (n+2)):=Book.geometry (gates f) (unit n field) M base id
    (out:=top) le_rfl room (capacity f id)
  have gatherFit : Gather.Bounds (w:=w) (d:=field) (M:=M) (gather f M base) src top := by
    intro i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ bound (fit i),(shape i.succ.succ).1,(shape i.succ.succ).2,rfl,rfl⟩
  have sources (i : Fin n) : Source (src i) (fun v g=>x v g i) M mid := by
    intro p
    exact (eval_below _ _ m mid (fit i) (fun a ha=>install.2.2.2.1 a (.inl ha))).trans (dataAt i p)
  let arg:=Gather.assembly (gather f M base) src
  have val : Source arg (fun v g=>encode field n (x v g)) M mid := by
    simpa only [arg,Gather.assembly,List.mem_finRange,ite_true] using
      Gather.collected (gather f M base) src top gatherFit mid install.2.1 x sources (List.finRange _)
  have zero : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M mid := by
    intro p
    have z : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p=0 := by
      apply Fin.ext
      have h:=(data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).isLt
      change (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).val<2^(0*M) at h
      simp only [Nat.zero_mul,pow_zero] at h
      change (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).val=0
      omega
    rw [z];rfl
  have gs:=shape (sideId n s)
  have ok : DescentPackedZip.Fits (finish f M base s) arg (.lit 0) (field*n) 0 M top w := by
    refine ⟨Gather.fits _ _ _ gatherFit _,trivial,gs.1,gs.2,?_,?_⟩ <;> cases s <;> rfl
  have image:=read_data (finish f M base s) arg (.lit 0) top ok (kernel f s) (kernel_zero f dead s)
    mid (install.2.2.1 s) _ _ val zero
  constructor
  · exact ⟨ok.apply,⟨ok.right,⟨ok.shift,ok.left⟩⟩⟩
  · simpa only [expr,arg,kernel,Equiv.symm_apply_apply] using image

theorem expr_work (f : Laws n field b) (M base : ℕ) (s : Bool) (src : Fin n→Expr)
    (time : ℕ) (cap : ∀i,(src i).work≤time) :
    (expr f M base s src).work ≤ 14+n*(time+11) := by
  have loop (xs : List (Fin n)) :
      (Gather.collect (gather f M base) src xs).work≤1+xs.length*(time+11) := by
    induction xs with
    | nil => simp [Gather.collect,Expr.work]
    | cons i xs ih =>
      have op:=cap i
      simp only [Gather.collect,work,List.length_cons,Nat.succ_mul]
      omega
  have walk:=loop (List.finRange n)
  simp only [List.length_finRange] at walk
  simp only [expr,work,Gather.assembly,Expr.work]
  omega

theorem header_tariff (n field M wordbits : ℕ) (cap : unit n field*M≤wordbits/2) :
    words n field M≤(n+2)*(2*2^(wordbits/2)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) cap))

end
end Hierarchy.DescentOperandPairBook

end OAI
