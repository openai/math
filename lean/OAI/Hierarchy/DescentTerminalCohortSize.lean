import OAI.Hierarchy.DescentTerminalFieldSize
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # The widths of the eight terminal fields and the occupancy bit -/
namespace Hierarchy.DescentTerminalVertexFields
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V groups blocks : ℕ}
local notation "width" => span q t H N A w

def items (H N A : ℕ) : Fin 8→ℕ := ![1,1,1,1,H,N,N,N*A]
def itemBits (q t H N A w : ℕ) : Fin 8→ℕ :=
  ![Nat.clog 2 (q+1),1,Nat.clog 2 (H+1),Nat.clog 2 (N+1),Nat.clog 2 (w+1),Nat.clog 2 (t+1),Nat.clog 2 (A+1),Nat.clog 2 (q+H+1)]

def familySize (f : Fin 8) := items H N A f*itemBits q t H N A w f
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
def widthAt (V : ℕ) (f : Fin 8) := V*sized f
local notation "extent" => widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
theorem volume : (∑ f,extent f)=V*width := by
  simp only [widthAt,←Finset.mul_sum]
  apply congrArg (V*·)
  rw [size]
  simp [familySize,items,itemBits,Fin.sum_univ_succ]
 ; ring

def primitiveSize : Fin 9→ℕ := Fin.cases 1 sized
def channels (blocks : ℕ) := blocks*9
def channelSize (j : Fin (channels blocks)) := primitiveSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (finProdFinEquiv.symm j).2*groups
def cohortSize := ∏j:Fin (channels blocks),2^(channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) j)
theorem cohort_size : cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) (blocks:=blocks)=
    2^(groups*blocks*(width+1)) := by
  unfold cohortSize
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  let size : Fin (blocks*9) → ℕ :=channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) (blocks:=blocks)
  change ∑i,size i=_
  have family : (∑f : Fin 8,sized f)=width := by simpa [widthAt] using (volume (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=1))
  have prim : (∑f:Fin 9,primitiveSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) f)=1+width := by
    rw [Fin.sum_univ_succ]
    exact congrArg (1+·) family
  have one (b : Fin blocks) : (∑f : Fin 9,size (finProdFinEquiv (b,f)))=(1+width)*groups := by
    simp only [size,channelSize,Equiv.symm_apply_apply,←Finset.sum_mul,prim]
  have split := (finProdFinEquiv (m:=blocks) (n:=9)).sum_comp size
  rw [←split,Fintype.sum_prod_type]
  simp only [one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change blocks*((1+width)*groups)=groups*blocks*(width+1)
  ring

end
end Hierarchy.DescentTerminalVertexFields

end OAI
