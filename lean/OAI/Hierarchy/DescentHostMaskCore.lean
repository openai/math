import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # True host counts and rectangular bank cleanup for every native round -/
namespace Hierarchy.DescentHostCount
open DescentSIMDLookup DescentPackedZip ProtocolRAM DescentIssuedTerminalId
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] {w cap H G M : ℕ}

theorem prefix_live (rank : V↪Fin (Fintype.card V)) (fits : Fintype.card V≤H) (h : Fin H) :
    h.val<Fintype.card V ↔∃v,(rank v).castLE fits=h := by
  have surj:=((Fintype.bijective_iff_injective_and_card rank).mpr ⟨rank.injective,by simp⟩).2
  constructor
  · intro use
    obtain ⟨v,hv⟩:=surj ⟨h.val,use⟩
    exact ⟨v,Fin.ext (congrArg (fun t : Fin (Fintype.card V) => t.val) hv)⟩
  · rintro ⟨v,rfl⟩
    exact (rank v).isLt

/-- A single observed prefix-total cell gates all columns sharing the physical rectangle.
For a signed stencil or a private-record bank the pad is zero; for an adjacency bank it is H. -/
def expression (owners count : Bank) (value : Expr) (pad : ℕ) :=
  Expr.branch .lt (.lookup owners .row) (.lookup count (.lit 0)) value (.lit pad)

theorem eval (owners count : Bank) (value : Expr) (pad length h : ℕ)
    (m : Memory w) (row : Fin cap) (inBank : cap≤owners.size) (ow : owners.size<2^w)
    (cw : count.size<2^w) (owner : m (owners.base+row.val)=(h:Word w)) (hostFits : h<2^w)
    (read : m count.base=(length:Word w)) (sizeFits : length<2^w) :
    (expression owners count value pad).eval m (row.val:Word w)=
      if h<length then value.eval m (row.val:Word w) else (pad:Word w) := by
  have hostEq:=(lookup_nat owners m (row.val:Word w) .row row.val rfl (row.isLt.trans_le inBank) ow).trans owner
  have countEq:=(lookup_nat count m (row.val:Word w) (.lit 0) 0 rfl (Nat.two_pow_pos _) cw).trans
    (by simpa using read)
  change (if DescriptorExpr.Comparison.lt.test
    ((Expr.lookup owners .row).eval m (row.val : Word w))
    ((Expr.lookup count (.lit 0)).eval m (row.val : Word w)) then
    value.eval m (row.val : Word w) else (pad : Word w)) = _
  rw [hostEq,countEq]
  simp only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,
    Fin.val_cast_of_lt hostFits,Fin.val_cast_of_lt sizeFits]

theorem issued (owners count : Bank) (value : Expr) (pad out rowCount length : ℕ)
    (ownerID : Fin rowCount→Fin H) (m : Memory w) (access : (expression owners count value pad).Fits w out)
    (room : out+rowCount<2^w) (inBank : rowCount≤owners.size) (oldRoom : H<2^w)
    (lengthFits : length≤H) (owner : ∀i,m (owners.base+i.val)=((ownerID i).val:Word w))
    (read : m count.base=(length:Word w)) :
    let expr:=expression owners count value pad
    let dest:=image out rowCount expr m
    (scan w out rowCount expr).Exec m dest (4+rowCount*(2*expr.work+4)) ∧
    (∀i : Fin rowCount,dest (out+i.val)=if (ownerID i).val<length then value.eval m (i.val:Word w) else pad) ∧
    ∀a,(a<out ∨ out+rowCount≤a)→dest a=m a := by
  refine ⟨scan_exec out rowCount _ m access room,?_,fun a atPos=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ atPos⟩
  intro i
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
    (eval owners count value pad length (ownerID i).val m i inBank access.1.1.2.1 access.2.1.1.2.1
      (owner i) ((ownerID i).isLt.trans oldRoom) read (lengthFits.trans_lt oldRoom))

@[simp] theorem work (owners count : Bank) (value : Expr) (pad : ℕ) :
    (expression owners count value pad).work=value.work+15 := by simp [expression,Expr.work];omega

theorem cheap (owners count : Bank) (value : Expr) (pad out n : ℕ) :
    CheapCode (scan w out n (expression owners count value pad)) := @scan_cheap _ _ _ _

end
end Hierarchy.DescentHostCount

end OAI
