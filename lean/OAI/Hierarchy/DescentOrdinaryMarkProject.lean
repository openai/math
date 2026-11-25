import OAI.Hierarchy.DescentOrdinaryCompactRack
import OAI.Hierarchy.DescentResetStemProjectExpr
import OAI.Hierarchy.DescentOrdinaryMarkRead
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Regroup the original signed mark and read it at the compact successor host -/
namespace Hierarchy.DescentOrdinaryMarkProject
open DescentSIMDLookup DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section
variable {N H G M a w : ℕ}
local notation "R₀" => DescentOrdinaryCompactPeer.ROM.rack

def rows (H G M : ℕ) := H*chunks G M
def code (N pitch : ℕ) (p : Row H G M) : ℕ :=
  (R₀ N pitch p.1).elim (rows N G M) (fun h=>(row N G M (h,p.2)).val)

def words (N H G M pitch i : ℕ) :=
  if yes : i<rows H G M then code N pitch ((row H G M).symm ⟨i,yes⟩) else 0
def addr (base H G M : ℕ) : Bank := ⟨base,Nat.clog 2 (rows H G M)⟩
def stop (base H G M : ℕ) := base+2^(Nat.clog 2 (rows H G M))
def mask (old : Bank) (base N H G M : ℕ) : Expr :=
  let key:=Expr.lookup (addr base H G M) .row
  .branch .eq key (.lit (rows N G M)) (.lit 0) (.lookup old key)

theorem mask_work (old : Bank) (base N H G M : ℕ) : (mask old base N H G M).work=22 := rfl

theorem projection (base pitch : ℕ) (m : Memory w) (old : Bank)
    (early : old.Fits w base) (narrow : rows N G M<2^w) (fit : stop base H G M<2^w)
    (Y : Fin N→Fin G→Cell a) (read : Source (.lookup old .row) Y M m) :
    let n:=rows H G M
    let installed:=DescentStaticWordColumn.image base (words N H G M pitch) m n
    (mask old base N H G M).Fits w (stop base H G M) ∧
    Source (mask old base N H G M) (fun (h : Fin H) g=>(R₀ N pitch h).elim 0 (fun u=>Y u g)) M installed := by
  intro n installed
  have amount : rows H G M≤(addr base H G M).size := Nat.le_pow_clog (by decide) _
  have before : base≤ stop base H G M := Nat.le_add_right ..
  have ab : (addr base H G M).Fits w (stop base H G M) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt fit,le_rfl⟩
  have eb : old.Fits w (stop base H G M) := ⟨early.1,early.2.1,early.2.2.trans before⟩
  refine ⟨⟨⟨ab,trivial⟩,trivial,trivial,eb,ab,trivial⟩,?_⟩
  intro p
  have key : (addr base H G M).read installed ((row H G M p).val : Word w)=(code N pitch p:Word w) := by
    rw [DescentPackedZip.bank_read _ _ ((row H G M p).isLt.trans_le amount) ab]
    change DescentStaticWordColumn.image base (words N H G M pitch) m (rows H G M)
      (base+(row H G M p).val) = (code N pitch p : Word w)
    rw [DescentStaticWordColumn.read base (rows H G M) (words N H G M pitch) m (row H G M p).isLt]
    have inside : (row H G M p).val < rows H G M := (row H G M p).isLt
    have wordAt : words N H G M pitch (row H G M p).val = code N pitch p := by
      unfold words
      rw [dite_eq_left inside]
      change code N pitch ((row H G M).symm (row H G M p)) = code N pitch p
      rw [Equiv.symm_apply_apply]
    exact congrArg (fun x : ℕ => (x : Word w)) wordAt
  cases h:R₀ N pitch p.1 with
  | none=>
    have zero : data (fun h g=>(R₀ N pitch h).elim (0:Cell a) (fun u=>Y u g)) p=0 := by
      simp [data,h,DescentPacking.PackedMatch.Local.Gather.encode_zero]
    have keyAt : (addr base H G M).read installed ((row H G M p).val : Word w)=(rows N G M:Word w) := by
      simpa only [code,h,Option.elim_none] using key
    simp [mask,Expr.eval,keyAt,DescriptorExpr.Comparison.test,zero]
  | some v=>
    let r:=row N G M (v,p.2)
    have diff : (r.val:Word w)≠(rows N G M:Word w) := by
      apply Fin.ne_of_val_ne
      rw [Fin.val_cast_of_lt (r.isLt.trans narrow),Fin.val_cast_of_lt narrow]
      exact r.isLt.ne
    have bit : data (fun t g=>(R₀ N pitch t).elim (0:Cell a) (fun u=>Y u g)) p=data Y (v,p.2) := by simp only [data,h,Option.elim_some]
    have raw : old.read installed (r.val:Word w)=old.read m (r.val:Word w) := by
      exact DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ early.1) _).trans_le early.2.2))
    have keyAt : (addr base H G M).read installed ((row H G M p).val : Word w)=(r.val:Word w) := by
      simpa only [code,h,Option.elim_some,r] using key
    have different : DescriptorExpr.Comparison.eq.test (r.val:Word w) (rows N G M:Word w)=false := by
      simp [DescriptorExpr.Comparison.test,diff]
    simpa only [mask,Expr.eval,keyAt,different,Bool.false_eq_true,ite_false,bit] using raw.trans (read (v,p.2))

end
end Hierarchy.DescentOrdinaryMarkProject

end OAI
