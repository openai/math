import OAI.Hierarchy.DescentResetStemKeyKernel
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentZipBook
import OAI.Hierarchy.ProbeStageColumnScan

namespace OAI
/-! # One shared public key book for every signed reset slot -/
namespace Hierarchy.DescentResetStemKey
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D field H G M w Q : ℕ}

def kernel (parse : Decoder D field) (s : Bool) (pack : Cell (field*(D+2))) (_ : Cell 0) :=
  word parse s ((encode field (D+2)).symm pack)

private theorem kernel_zero (parse : Decoder D field) (dead : parse 0=none) (s : Bool) :
    kernel parse s 0 0=0 := by
  have blank : encode field (D+2) (fun _=>0)=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin (D+2)=>(0:Cell field))).val=0
    simp []
  exact (congrArg (word parse s) ((encode field (D+2)).symm_apply_eq.mpr blank.symm)).trans
    (word_zero parse dead s)

def gates (parse : Decoder D field) : Fin ((D+2)+2)→Book.Gate :=
  Fin.cases ⟨field*(D+2),0,field+2,kernel parse false⟩
    (Fin.cases ⟨field*(D+2),0,field+2,kernel parse true⟩
      (fun i=>⟨field*(D+2),field,field*(D+2),Gather.setField i⟩))

def unit (D field : ℕ) := field*(D+2)+field
def words (D field M : ℕ) := ((D+2)+2)*(2*2^(unit D field*M))
def gather (parse : Decoder D field) (M base : ℕ) (i : Fin (D+2)) :=
  Book.tables (gates parse) (unit D field) M base i.succ.succ
def sideId (D : ℕ) : Bool→Fin ((D+2)+2)
  | false => 0
  | true => (0 : Fin ((D+2)+1)).succ
def finish (parse : Decoder D field) (M base : ℕ) (s : Bool) :=
  Book.tables (gates parse) (unit D field) M base (sideId D s)
def expr (parse : Decoder D field) (M base : ℕ) (s : Bool) (src : Fin (D+2)→Expr) :=
  (finish parse M base s).read (Gather.assembly (gather parse M base) src) (.lit 0)
def program (parse : Decoder D field) (M w base : ℕ) := Book.install (gates parse) (unit D field) M w base
def memory (parse : Decoder D field) (M base : ℕ) (m : Memory w) := Book.image (gates parse) (unit D field) M base m

private theorem capacity (parse : Decoder D field) (j : Fin ((D+2)+2)) :
    (gates parse j).left+(gates parse j).right≤ unit D field := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun k=>?_) i) j
  · exact Nat.add_le_add_left (Nat.zero_le field) _
  · exact Nat.add_le_add_left (Nat.zero_le field) _
  · exact le_rfl

theorem mounted (parse : Decoder D field) (M base : ℕ) (m : Memory w) (room : base+words D field M<2^w) :
    let mid:=memory parse M base m
    (program parse M w base).Exec m mid (4+10*words D field M) ∧
    (∀i,Static (gather parse M base i) (Gather.setField (d:=field) i) M mid) ∧
    (∀s,Static (finish parse M base s) (kernel parse s) M mid) ∧
    (∀x,x< base ∨ base+words D field M≤ x→mid x=m x) ∧ CheapCode (program parse M w base) := by
  obtain ⟨run,read,keep,cheap⟩:=Book.mount (gates parse) (unit D field) M base m (capacity parse) room
  refine ⟨run,fun i=>by simpa only [memory,gather,gates,Fin.cases_succ] using read i.succ.succ,?_,keep,cheap⟩
  intro s
  cases s with
  | false=>simpa only [memory,finish,sideId,gates,Fin.cases_zero,Fin.cases_succ] using read (sideId D false)
  | true=>simpa only [memory,finish,sideId,gates,Fin.cases_zero,Fin.cases_succ] using read (sideId D true)

/-- Syntactic use of the shape ROMs is valid on every initial tape. -/
theorem expr_fits (parse : Decoder D field) (s : Bool) (M base : ℕ) (src : Fin (D+2)→Expr)
    (fit : ∀i,(src i).Fits w base) (room : base+words D field M<2^w) :
    (expr parse M base s src).Fits w (base+words D field M) := by
  let top:=base+words D field M
  have bound:=Nat.le_add_right base (words D field M)
  have shape (id : Fin ((D+2)+2)):=Book.geometry (gates parse) (unit D field) M base id
    (out:=top) le_rfl room (capacity parse id)
  have inputs : Gather.Bounds (w:=w) (d:=field) (M:=M) (gather parse M base) src top := by
    intro i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ bound (fit i),(shape i.succ.succ).1,(shape i.succ.succ).2,rfl,rfl⟩
  let arg:=Gather.assembly (gather parse M base) src
  let gs:=shape (sideId D s)
  have ok : DescentPackedZip.Fits (finish parse M base s) arg (.lit 0) (field*(D+2)) 0 M top w := by
    refine ⟨Gather.fits _ _ _ inputs _,trivial,gs.1,gs.2,?_,?_⟩ <;> cases s <;> rfl
  exact ⟨ok.apply,⟨ok.right,⟨ok.shift,ok.left⟩⟩⟩

theorem issued (parse : Decoder D field) (dead : parse 0=none) (s : Bool) (base : ℕ)
    (src : Fin (D+2)→Expr) (m : Memory w) (x : Fin H→Fin G→Fin (D+2)→Cell field)
    (fit : ∀i,(src i).Fits w base) (dataAt : ∀i,Source (src i) (fun v g=>x v g i) M m)
    (room : base+words D field M<2^w) :
    let e:=expr parse M base s src
    e.Fits w (base+words D field M) ∧ Source e (fun v g=>word parse s (x v g)) M (memory parse M base m) := by
  let top:=base+words D field M
  let mid:=memory parse M base m
  have bound:=Nat.le_add_right base (words D field M)
  have install:=mounted parse M base m room
  have shape (id : Fin ((D+2)+2)):=Book.geometry (gates parse) (unit D field) M base id
    (out:=top) le_rfl room (capacity parse id)
  have gatherFit : Gather.Bounds (w:=w) (d:=field) (M:=M) (gather parse M base) src top := by
    intro i
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ bound (fit i),(shape i.succ.succ).1,(shape i.succ.succ).2,rfl,rfl⟩
  have sources (i : Fin (D+2)) : Source (src i) (fun v g=>x v g i) M mid := by
    intro p
    exact (eval_below _ _ m mid (fit i) (fun a ha=>install.2.2.2.1 a (.inl ha))).trans (dataAt i p)
  let arg:=Gather.assembly (gather parse M base) src
  have val : Source arg (fun v g=>encode field (D+2) (x v g)) M mid := by
    simpa only [arg,Gather.assembly,List.mem_finRange,ite_true] using
      Gather.collected (gather parse M base) src top gatherFit mid install.2.1 x sources (List.finRange _)
  have zero : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M mid := by
    intro p
    have z : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p=0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      have h:=(data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).isLt
      simp only [Nat.zero_mul,pow_zero] at h
      omega
    rw [z]; rfl
  have gs:=shape (sideId D s)
  have ok : DescentPackedZip.Fits (finish parse M base s) arg (.lit 0) (field*(D+2)) 0 M top w := by
    refine ⟨Gather.fits _ _ _ gatherFit _,trivial,gs.1,gs.2,?_,?_⟩ <;> cases s <;> rfl
  have image:=read_data (finish parse M base s) arg (.lit 0) top ok (kernel parse s) (kernel_zero parse dead s)
    mid (install.2.2.1 s) _ _ val zero
  constructor
  · exact ⟨ok.apply,⟨ok.right,⟨ok.shift,ok.left⟩⟩⟩
  · simpa only [expr,arg,kernel,Equiv.symm_apply_apply] using image

theorem expr_work (parse : Decoder D field) (M base : ℕ) (s : Bool) (src : Fin (D+2)→Expr)
    (time : ℕ) (cap : ∀i,(src i).work≤ time) :
    (expr parse M base s src).work ≤ 14+(D+2)*(time+11) := by
  have loop (xs : List (Fin (D+2))) :
      (Gather.collect (gather parse M base) src xs).work≤1+xs.length*(time+11) := by
    induction xs with
    | nil => simp [Gather.collect,Expr.work]
    | cons i xs ih =>
      have op:=cap i
      simp only [Gather.collect,work,List.length_cons,Nat.succ_mul]
      omega
  have walk:=loop (List.finRange (D+2))
  simp only [List.length_finRange] at walk
  simp only [expr,work,Gather.assembly,Expr.work]
  omega

theorem header_tariff (D field M wordbits : ℕ) (cap : unit D field*M≤ wordbits/2) :
    words D field M≤((D+2)+2)*(2*2^(wordbits/2)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) cap))

end
end Hierarchy.DescentResetStemKey

end OAI
