import OAI.Hierarchy.DescentDyadicReductionLayout

namespace OAI
/-! # The physical packed result after a pair of predecessor sites is replaced by its parent -/
namespace Hierarchy.DescentPackedWalshReduction
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def packNat (b lanes : ℕ) (f : ℕ→ℕ) :=
  (encode b lanes (fun j=>(f j.val:Cell b))).val

/-- The second coordinate is the original difference ordinal, independent of
the number of differences currently stored in one word. -/
def Stored {w : ℕ} (base sites chunks lanes bits : ℕ) (x : ℕ→ℕ→ℕ) (m : Memory w) : Prop :=
  ∀v<sites,∀i<chunks,m (base+v*chunks+i)=((packNat bits lanes (fun j=>x v (i*lanes+j)):ℕ):Word w)

theorem packNat_one (b : ℕ) (f : ℕ→ℕ) (h : f 0<2^b) : packNat b 1 f=f 0 := by
  let x (i : Fin 1) : Cell b:=(f i.val:Cell b)
  have head:=digit_encode x (0:Fin 1)
  have room : (encode b 1 x).val<2^b := by simpa only [Nat.mul_one] using (encode b 1 x).isLt
  simpa only [packNat,digit,Fin.val_zero,Nat.zero_add,Nat.mul_one,Nat.mul_zero,pow_zero,
    Nat.div_one,Nat.mod_eq_of_lt room,x,Fin.val_natCast,Nat.mod_eq_of_lt h] using head

private def cells (S : Tile) (x : ℕ→ℕ→ℕ) : Data S.H S.K S.Z S.L S.digits :=
  fun v side i z j=>(x (2*v.val+side.toNat) (i.val*(S.Z*S.L)+z.val*S.L+j.val):Cell S.digits)

private theorem old_row {H K : ℕ} (v : Fin H) (s : Bool) (i : Fin K) :
    (leftRow v s i).val=(2*v.val+s.toNat)*K+i.val := by
  have flag : (finTwoEquiv.symm s).val=s.toNat := by cases s <;> rfl
  simp only [leftRow,finProdFinEquiv_apply_val,flag]
  ring

private theorem new_row {H K Z : ℕ} (v : Fin H) (i : Fin K) (z : Fin Z) :
    (rightRow v i z).val=v.val*(K*Z)+(i.val*Z+z.val) := by
  simp only [rightRow,finProdFinEquiv_apply_val]
  ring

private theorem old_part (S : Tile) (x : ℕ→ℕ→ℕ) (v : Fin S.H) (s : Bool) (i : Fin S.K) :
    (part (cells S x v s i)).val=packNat S.digits (S.Z*S.L)
      (fun j=>x (2*v.val+s.toNat) (i.val*(S.Z*S.L)+j)) := by
  unfold part packNat
  congr 2
  funext a
  obtain ⟨⟨z,j⟩,rfl⟩:=finProdFinEquiv.surjective a
  simp only [cells,Equiv.symm_apply_apply,finProdFinEquiv_apply_val]
  congr 2
  ring

private theorem old_at (S : Tile) {b w : ℕ} {m : Memory w} {x : ℕ→ℕ→ℕ}
    (src : Stored b (S.H*2) S.K (S.Z*S.L) S.digits x m) :
    oldWords b (cells S x) m := by
  intro v s i
  have limit : 2*v.val+s.toNat<S.H*2 := by have hv:=v.isLt;cases s <;> simp <;> omega
  rw [old_row,←Nat.add_assoc,old_part]
  exact src _ limit i.val i.isLt

def addSites (x : ℕ→ℕ→ℕ) (v d : ℕ) := x (2*v) d+x (2*v+1) d

private theorem new_part (S : Tile) (x : ℕ→ℕ→ℕ) (low : ∀v d,x v d<2^S.digits)
    (v : Fin S.H) (i : Fin S.K) (z : Fin S.Z) :
    (encode (S.digits+1) S.L (merged (cells S x) v i z)).val=
      packNat (S.digits+1) S.L (fun j=>addSites x v.val ((i.val*S.Z+z.val)*S.L+j)) := by
  unfold packNat
  congr 2
  funext j
  simp only [merged,cells,addSites,Bool.toNat_false,Bool.toNat_true,Nat.add_zero,
    Fin.val_natCast,Nat.mod_eq_of_lt (low ..)]
  rw [Nat.add_mul,Nat.mul_assoc]

theorem Tile.run_nat (S : Tile) {w rom source out : ℕ} (x : ℕ→ℕ→ℕ) (m : Memory w)
    (small : ∀v d,x v d<2^S.digits) (publicEnd : rom+S.span≤out)
    (prior : source+S.inputRows≤out) (last : out+S.rows<2^w)
    (heads : ∀j<S.span,m (rom+j)=S.word j)
    (initial : Stored source (S.H*2) S.K (S.Z*S.L) S.digits x m) :
    let B:=S.banks rom source
    let after:=image out S.rows B.read m
    (scan w out S.rows B.read).Exec m after (4+90*S.rows) ∧
      Stored out S.H (S.K*S.Z) S.L (S.digits+1) (addSites x) after ∧
      (∀i<out,after i=m i) ∧ ∀i,out+S.rows ≤ i→after i=m i := by
  have ⟨exec,read,lo,hi⟩:=run (S.banks rom source) out (cells S x) m (S.room publicEnd prior last)
    (S.headerAt heads) (old_at S initial)
  refine ⟨exec,?_,lo,hi⟩
  intro v hv j hj
  obtain ⟨⟨i,z⟩,pair⟩:=finProdFinEquiv.surjective (⟨j,hj⟩ : Fin (S.K*S.Z))
  have seq : i.val*S.Z+z.val=j:=by simpa [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using congrArg Fin.val pair
  have got:=read (⟨v,hv⟩:Fin S.H) i z
  rw [new_row,new_part S x small,seq,←Nat.add_assoc] at got
  exact got

end
end Hierarchy.DescentPackedWalshReduction

end OAI
