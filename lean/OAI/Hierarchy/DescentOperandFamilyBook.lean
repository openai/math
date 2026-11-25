import OAI.Hierarchy.DescentOperandPairBook

namespace OAI
/-! # One printed book for a family of finite laws over measured packed operands -/
namespace Hierarchy.DescentOperandFamilyBook
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {K n a b : ℕ} (F : Fin K→(Fin n→Cell a)→Cell b)

def kernel (j : Fin K) (x : Cell (a*n)) (_ : Cell 0) :=F j ((encode a n).symm x)
private theorem empty (dead : ∀j,F j (fun _=>0)=0) (j : Fin K) : kernel F j 0 0=0 := by
  have blank : encode a n (fun _=>0)=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
    simp []
  exact (congrArg (F j) ((encode a n).symm_apply_eq.mpr blank.symm)).trans (dead j)

def gate : Fin n⊕Fin K→Book.Gate :=
  Sum.elim (fun i=>⟨a*n,a,a*n,Gather.setField i⟩)
    (fun j=>⟨a*n,0,b,kernel F j⟩)
def gates (i : Fin (n+K)) := gate F (finSumFinEquiv.symm i)
def unit (n a : ℕ) :=a*n+a
def words (K n a M : ℕ) :=(n+K)*(2*2^(unit n a*M))
def endAddress (K n a M base : ℕ) :=base+words K n a M
def program (M base w : ℕ) :=Book.install (gates F) (unit n a) M w base
def image {w : ℕ} (M base : ℕ) (mem : Memory w) :=Book.image (gates F) (unit n a) M base mem
def tables (M base : ℕ) (i : Fin n⊕Fin K) :=Book.tables (gates F) (unit n a) M base (finSumFinEquiv i)
def expr (M base : ℕ) (j : Fin K) (src : Fin n→Expr) :=
  (tables F M base (.inr j)).read (Gather.assembly (fun i=>tables F M base (.inl i)) src) (.lit 0)

private theorem capacity (i : Fin (n+K)) :
    (gates F i).left+(gates F i).right≤unit n a := by
  obtain ⟨i,rfl⟩:=(finSumFinEquiv (m:=n) (n:=K)).surjective i
  cases i <;> simp [gates,gate,unit]

theorem any {w : ℕ} (M base : ℕ) (mem : Memory w) (room : endAddress K n a M base<2^w) :
    (program F M base w).Exec mem (image F M base mem) (4+10*words K n a M) ∧
    CheapCode (program F M base w) ∧
    (∀t,t<base ∨ endAddress K n a M base≤t→image F M base mem t=mem t) ∧
    ∀i,Static (tables F M base i) (gate F i).eval M (image F M base mem) := by
  obtain ⟨run,fixed,frame,cheap⟩:=Book.mount (gates F) (unit n a) M base mem (capacity F) room
  refine ⟨run,cheap,frame,?_⟩
  intro i
  obtain ⟨j,rfl⟩:=(finSumFinEquiv (m:=n) (n:=K)).symm.surjective i
  unfold tables
  rw [Equiv.apply_symm_apply]
  exact fixed j

theorem expr_work (M base : ℕ) (j : Fin K) (src : Fin n→Expr) (t : ℕ) (price : ∀i,(src i).work≤t) :
    (expr F M base j src).work≤14+n*(t+11) := by
  let tab:=fun i=>tables F M base (.inl i)
  have loop (xs : List (Fin n)) : (Gather.collect tab src xs).work≤1+xs.length*(t+11) := by
    induction xs with
    | nil => simp [Gather.collect,Expr.work]
    | cons i xs ih =>
      have op:=price i
      simp only [Gather.collect,work,List.length_cons,Nat.succ_mul]
      omega
  have walk:=loop (List.finRange n)
  simp only [List.length_finRange] at walk
  change (Tables.read _ (Gather.collect tab src (List.finRange n)) (.lit 0)).work≤_
  simp only [Tables.read,Expr.work]
  omega

theorem expr_fits {w : ℕ} (M base : ℕ) (j : Fin K) (src : Fin n→Expr)
    (held : ∀i,(src i).Fits w base) (room : endAddress K n a M base<2^w) :
    (expr F M base j src).Fits w (endAddress K n a M base) :=by
  let top:=endAddress K n a M base
  let tab:=fun i=>tables F M base (.inl i)
  have shape (i : Fin n⊕Fin K):=Book.geometry (gates F) (unit n a) M base (finSumFinEquiv i)
    (out:=top) le_rfl room (capacity F _)
  have bounds : Gather.Bounds (w:=w) (d:=a) (M:=M) tab src top:=by
    intro i
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (held i),(shape (.inl i)).1,(shape (.inl i)).2,?_,?_⟩ <;>
      simp [tab,tables,Book.tables,gate,gates]
  exact ⟨(shape (.inr j)).2,trivial,(shape (.inr j)).1,Gather.fits _ _ _ bounds _⟩

theorem issued (dead : ∀j,F j (fun _=>0)=0) {H G w : ℕ} (M base : ℕ) (j : Fin K) (src : Fin n→Expr) (mem : Memory w)
    (x : Fin H→Fin G→Fin n→Cell a) (held : ∀i,(src i).Fits w base)
    (prior : ∀i,Source (src i) (fun v g=>x v g i) M mem) (room : endAddress K n a M base<2^w) :
    (expr F M base j src).Fits w (endAddress K n a M base) ∧
    Source (expr F M base j src) (fun v g=>F j (x v g)) M (image F M base mem) := by
  let top:=endAddress K n a M base
  let mid:=image F M base mem
  let tab:=fun (i : Fin n)=>tables F M base (.inl i)
  let term:=tables F M base (.inr j)
  let arg:=Gather.assembly tab src
  have mount:=any F M base mem room
  have shape (i : Fin n⊕Fin K):=Book.geometry (gates F) (unit n a) M base (finSumFinEquiv i)
    (out:=top) le_rfl room (capacity F _)
  have measure (i : Fin n) : Source (src i) (fun v g=>x v g i) M mid :=
    fun p=>(eval_below _ _ mem mid (held i) (fun z hz=>mount.2.2.1 z (.inl hz))).trans (prior i p)
  have bounds : Gather.Bounds (w:=w) (d:=a) (M:=M) tab src top:=by
    intro i
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (held i),(shape (.inl i)).1,(shape (.inl i)).2,?_,?_⟩ <;>
      simp [tab,tables,Book.tables,gate,gates]
  have whole : Source arg (fun v g=>encode a n (x v g)) M mid:=by
    simpa only [arg,Gather.assembly,List.mem_finRange,ite_true] using Gather.collected tab src top bounds mid
      (fun i=>mount.2.2.2 (.inl i)) x measure (List.finRange _)
  have zero : Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) M mid:=by
    intro p
    have dead : data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p=0:=by
      apply Fin.ext
      have h:=(data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).isLt
      change (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).val<2^(0*M) at h
      simp only [Nat.zero_mul,pow_zero] at h
      change (data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell 0)) p).val=0
      omega
    rw [dead];rfl
  have geometry : DescentPackedZip.Fits term arg (.lit 0) (a*n) 0 M top w := by
    refine ⟨Gather.fits _ _ _ bounds _,trivial,(shape (.inr j)).1,(shape (.inr j)).2,?_,?_⟩ <;>
      simp [term,tables,Book.tables,gate,gates]
  have output:=read_data term arg (.lit 0) top geometry (kernel F j) (empty F dead j) mid (mount.2.2.2 (.inr j)) _ _ whole zero
  exact ⟨⟨geometry.apply,geometry.right,geometry.shift,geometry.left⟩,by
    simpa only [expr,arg,kernel,Equiv.symm_apply_apply,term,tab] using output⟩

theorem size_le (K n a M w : ℕ) (limit : unit n a*M≤w/2) :
    words K n a M≤(n+K)*(2*2^(w/2)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) limit))


def ticks (K n a M : ℕ) :=4+10*words K n a M
end
end Hierarchy.DescentOperandFamilyBook

end OAI
