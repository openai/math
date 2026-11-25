import OAI.Hierarchy.DescentResetStemGroupPlane

namespace OAI
/-! # Native one-copy ranking of the old group digit for every remixed donor -/
namespace Hierarchy.DescentResetStemGroupPlane
open DescentSIMDLookup DescentColonies DescentGL DescentIssuedFallbackPanel DescentResetStemCompactOrder
open DescentFallbackRankRAM DescentFallbackLeafScan DescentSortedRoster DescentPackedColony ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w m c k groups : ℕ}

def donorOffset (radix i : ℕ) : Expr :=
  .op .add (.op .sub .row (.op .mask .row (.lit (radix-1)))) (.lit i)

theorem offset_read (mem : Memory w) (d v : ℕ) (i j : Fin (2^d)) (room : v*2^d+j.val<2^w)
    (mask : 2^d-1<2^w) : (donorOffset (2^d) i.val).eval mem ((v*2^d+j.val:ℕ):Word w)=((v*2^d+i.val:ℕ):Word w) := by
  have low : BinaryOp.bitAnd.eval ((v*2^d+j.val:ℕ):Word w) ((2^d-1:ℕ):Word w)=(j.val:Word w):=by
    change (((((v*2^d+j.val:ℕ):Word w).val &&& ((2^d-1:ℕ):Word w).val):ℕ):Word w)=_
    rw [Fin.val_cast_of_lt room,Fin.val_cast_of_lt mask,Nat.and_two_pow_sub_one_eq_mod,Nat.mul_add_mod_of_lt j.isLt]
  change (((v*2^d+j.val:ℕ):Word w)-BinaryOp.bitAnd.eval ((v*2^d+j.val:ℕ):Word w) ((2^d-1:ℕ):Word w))+(i.val:Word w)=_
  rw [low]
  push_cast
  ring

def high (fit : c≤ m) (z : Block m) : Block c :=
  ⟨z.val/2^(m-c),(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by
    rw [←pow_add,Nat.add_sub_of_le fit];exact z.isLt)⟩
def low (c : ℕ) (z : Block m) : Fin (2^(m-c)) := ⟨z.val%2^(m-c),Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem join_digits (fit : c≤ m) (z : Block m) : join fit (high fit z) (low c z)=z :=
  Fin.ext (Nat.div_add_mod' ..)

/-- The preceding scalar GL plane supplies the observed old group for every
donor in the row's coarse cell. Duplicate group IDs pay once in the rank. -/
theorem shared_ranks (digits : Block m≃Fin groups×Block k) (basis : DescentGL.Layout m) (fit : c≤ m)
    (src out : Bank) (mem : Memory w) (srcRoom : 2^m≤ src.size) (before : src.Fits w out.base)
    (space : out.base+2^m<2^w)
    (stored : ∀z : Block m,mem (src.base+z.val)=((digits ((rearrange basis).symm z)).1.val:Word w)) :
    let cols:=fun i : Fin (2^(m-c))=>Expr.lookup src (donorOffset (2^(m-c)) i.val)
    let op:=calculate cols (.lookup src .row)
    let dst:=image out.base (2^m) op mem
    (scan w out.base (2^m) op).Exec mem dst (4+2^m*(2*op.work+4)) ∧
    (∀z : Block m,dst (out.base+z.val)=(compress (groupDomain digits basis fit () (high fit z))
        (digits ((rearrange basis).symm z)).1.val:Word w)) ∧
    (∀a,a<out.base ∨ out.base+2^m≤a→dst a=mem a) ∧
    DescentStaticWordColumn.names (scan w out.base (2^m) op)=11+4*op.work ∧ CheapCode (scan w out.base (2^m) op) := by
  intro cols op dst
  let tar:=fun z : Block m=>(digits ((rearrange basis).symm z)).1
  let inputs:=fun z : Block m=>groupRows digits basis fit () (high fit z)
  have narrow : 2^m<2^w:=srcRoom.trans_lt before.2.1
  have rad : 2^(m-c)<2^w:=(Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le m c)).trans_lt narrow
  have read (z : Block m) (i : Fin (2^(m-c))) :
      (cols i).eval mem (z.val:Word w)=(target (inputs z i):Word w):=by
    let t:=high fit z;let j:=low c z
    have rep : t.val*2^(m-c)+j.val=z.val:=congrArg Fin.val (join_digits fit z)
    have rowRoom : t.val*2^(m-c)+j.val<2^w:=rep.trans_lt (z.isLt.trans narrow)
    have mask:2^(m-c)-1<2^w:=(Nat.sub_le ..).trans_lt rad
    change src.read mem ((donorOffset (2^(m-c)) i.val).eval mem (z.val:Word w))=_
    rw [←rep,offset_read mem _ _ i j rowRoom mask]
    change src.read mem ((join fit t i).val:Word w)=_
    rw [DescentPackedZip.bank_read src mem ((join fit t i).isLt.trans_le srcRoom) before]
    exact stored _
  have wanted (z : Block m) : (Expr.lookup src .row |>.eval mem (z.val:Word w)).val=(tar z).val:=by
    change (src.read mem (z.val:Word w)).val=_
    rw [DescentPackedZip.bank_read src mem (z.isLt.trans_le srcRoom) before,stored z,Fin.val_cast_of_lt]
    exact (tar z).isLt.trans ((groups_fit digits).trans_lt narrow)
  have fits (i : Fin (2^(m-c))) : (cols i).Fits w out.base:=⟨before,⟨⟨trivial,⟨trivial,trivial⟩⟩,trivial⟩⟩
  obtain ⟨act,seen,keep,bill,cheap⟩:=rankSources inputs cols (.lookup src .row) out mem tar
    ((groups_fit digits).trans_lt narrow) rad fits ⟨before,trivial⟩ space read wanted
  refine ⟨act,?_,keep,bill,cheap⟩
  intro z
  exact (seen z).trans (congrArg (fun n : ℕ=>(n:Word w)) (group_read digits basis fit () (high fit z) (tar z)))

/-- A single shared new-to-old coordinate plane also gives the original fine
block by a mask. It uses the same genuine GL execution with the identity digit. -/
def allDigits (m : ℕ) : Block m≃Fin (2^m)×Block 0 where
  toFun z:=(z,0)
  invFun v:=v.1
  left_inv _:=rfl
  right_inv:=by
    rintro ⟨u,v⟩
    refine Prod.ext rfl (Fin.ext ?_)
    have h := v.isLt
    change v.val < 1 at h
    change 0 = v.val
    omega

theorem fine_read (S : DescentCompiler.AtomSchedule) {tail : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (i : ℕ) (z : Block (S.groupWidth k tail i+k)) :
    ((S.resetInputDigits base radix i z).2).val=(allDigits _ z).1.val%2^k := by rfl

end
end Hierarchy.DescentResetStemGroupPlane

end OAI
