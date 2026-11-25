import OAI.Hierarchy.DescentExteriorKeyRAM
import OAI.Hierarchy.DescentExteriorHeader
import OAI.Hierarchy.ProtocolRAMStackSlice

namespace OAI
/-! # A native zero bin rejects every incorrectly proposed exterior array -/
namespace Hierarchy.DescentExteriorFetch
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w : ℕ}

def mismatch (left right : Bank) : Expr :=
  .branch .eq (.lookup left .row) (.lookup right .row) (.lit 0) (.lit 1)

def flags (w dst n : ℕ) (left right : Bank) := scan w dst n (mismatch left right)

def check (w dst base n : ℕ) (left right : Bank) : Procedure w :=
  (flags w dst n left right).seq ((ProtocolRAMScalarCounts.clear w base 2).seq
    (ProtocolRAMScalarCounts.counting w dst base n))

def bad (left right : Bank) (m : Memory w) (i : ℕ) : ℕ :=
  if m (left.base+i)=m (right.base+i) then 0 else 1

theorem bad_iff {n : ℕ} (left right : Bank) (m : Memory w) :
    (∑i∈Finset.range n,if bad left right m i=1 then 1 else 0 : ℕ)=0 ↔
      ∀i:Fin n,m (left.base+i.val)=m (right.base+i.val) := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)]
  constructor
  · intro h i
    have v:=h i.val (Finset.mem_range.mpr i.isLt)
    by_contra no
    simp [bad,no] at v
  · intro h i hi
    simp [bad,h ⟨i,Finset.mem_range.mp hi⟩]

private theorem bank_check {w out : ℕ} (b : Bank) (m : Memory w) (i : ℕ)
    (fit : b.Fits w out) (pos : i<b.size) : b.read m (i:Word w)=m (b.base+i) := by
  simp [Bank.read,Fin.val_cast_of_lt (pos.trans fit.2.1),Nat.mod_eq_of_lt pos]

theorem row_flag {w n dst : ℕ} (left right : Bank) (m : Memory w) (i : Fin n)
    (hl : left.Fits w dst) (hr : right.Fits w dst) (ls : n≤left.size) (rs : n≤right.size) :
    image dst n (mismatch left right) m (dst+i.val)=(bad left right m i.val:Word w) := by
  have inside : dst≤dst+i.val ∧ dst+i.val<dst+n := by have := i.isLt; omega
  simp only [ProtocolRAM.image, fillSegment, inside, Nat.cast_add, add_sub_cancel_left,
    mismatch, Expr.eval, DescriptorExpr.Comparison.test,
    bank_check left m i.val hl (i.isLt.trans_le ls), bank_check right m i.val hr (i.isLt.trans_le rs),
    beq_iff_eq, bad]
  by_cases same : m (left.base+i.val) = m (right.base+i.val) <;> simp [same]

section
attribute [local irreducible] CheapCode

private theorem check_cheap (w dst base n : ℕ) (left right : Bank) : CheapCode (check w dst base n left right) := by
  unfold check flags
  exact @cheap_seq w (scan w dst n (mismatch left right))
    ((ProtocolRAMScalarCounts.clear w base 2).seq (ProtocolRAMScalarCounts.counting w dst base n))
    (@scan_cheap w dst n (mismatch left right)) (@request_histogram_cheap w dst base 2 n)

set_option maxHeartbeats 600000 in
theorem check_spec {w n : ℕ} (dst base : ℕ) (left right : Bank)
    (hl : left.Fits w dst) (hr : right.Fits w dst) (ls : n≤left.size) (rs : n≤right.size)
    (apart : dst+n≤base) (endFit : base+2<2^w) :
    (check w dst base n left right).Spec (fun _=>True)
      (fun m out=>out (base+1)=0 ↔ ∀i:Fin n,m (left.base+i.val)=m (right.base+i.val))
      ((4+n*(2*(mismatch left right).work+4))+(7+6*2+11*n)) ∧
      CheapCode (check w dst base n left right) := by
  refine ⟨?_, check_cheap w dst base n left right⟩
  let v:=mismatch left right
  have vf : v.Fits w dst := ⟨⟨hl,trivial⟩,⟨hr,trivial⟩,trivial,trivial⟩
  intro P R K M pc reg pub exit rom «public» cfg m start _
  let rows:=image dst n v m
  let f:=bad left right m
  have first : (flags w dst n left right).Spec (fun z=>z=m)
      (fun _ o=>o=rows) (4+n*(2*v.work+4)) := by
    intro P R K M pc reg pub exit rom «public» cfg z entry hz
    subst z
    exact scan_exec dst n v m vf (by omega) M pc reg pub exit rom «public» cfg m entry rfl
  have second : ((ProtocolRAMScalarCounts.clear w base 2).seq (ProtocolRAMScalarCounts.counting w dst base n)).Spec
      (fun z => ∀ i<n, z (dst+i)=(f i:Word w))
      (fun _ o => ∀ b : Fin 2, o (base+b.val)=
        ((∑ j ∈ Finset.range n, if f j=b.val then 1 else 0 : ℕ) : Word w))
      (7+6*2+11*n) :=
    ProtocolRAMScalarCounts.histogram dst base 2 n f apart endFit (by omega) (by
      intro i hi;unfold f bad;split <;> decide)
  obtain ⟨time,ht,z,o,ran,ended,_,_,out⟩:=first.seq second
    (fun _ o h i hi=>by rw [h];exact row_flag left right m ⟨i,hi⟩ hl hr ls rs)
    M pc reg pub exit rom «public» cfg m start rfl
  refine ⟨time,ht,z,o,ran,ended,?_⟩
  have c:=out (1:Fin 2)
  let count:=∑i∈Finset.range n,if f i=1 then 1 else 0
  change o (base+1)=(count:Word w) at c
  have small : count≤n := by
    calc
      _ ≤ ∑_i∈Finset.range n,1 := Finset.sum_le_sum fun i _=>by split <;> decide
      _ = n := by simp
  change o (base+1)=0 ↔ ∀i : Fin n, m (left.base+i.val)=m (right.base+i.val)
  rw [c,Fin.ext_iff,Fin.val_cast_of_lt (show count<2^w by omega),Fin.val_zero]
  exact bad_iff left right m
end

theorem check_time (left right : Bank) (n : ℕ) :
    (4+n*(2*(mismatch left right).work+4))+(7+6*2+11*n)=23+49*n := by
  change 4+n*(2*17+4)+(7+6*2+11*n)=_;omega

end
end Hierarchy.DescentExteriorFetch

end OAI
