import OAI.Hierarchy.DescentTerminalPositionPages

namespace OAI
/-! # A fixed one-word page for every common position and one terminal sentinel -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalBinPack DescentTerminalRecipeRows DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W B bits pool S ℓ : ℕ}
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def aligned (page : Fin S→Word B) (r : ℕ) : Word B := if hr : r<S then page ⟨r,hr⟩ else 0

def bitsAt (page : Fin S→Word B) (bp : 0<B) (n : ℕ) :=
  wordBits _ (aligned page (n/B)) ⟨n%B,Nat.mod_lt _ bp⟩

theorem dense_page (page : Fin S→Word B) (bp : 0<B) (r : ℕ) : dense B (bitsAt page bp) r=aligned page r := by
  apply (wordBits _).injective
  funext j
  simp [dense,bitsAt,Nat.mul_comm r B,Nat.mul_add_div bp,Nat.div_eq_of_lt j.isLt,
    Nat.mod_eq_of_lt j.isLt]

theorem fields (page : Fin S→Word B) (bp : 0<B) (z : Fin S→Raw) (small : ∀i,(z i).1.val*ℓ≤B)
    (printed : ∀i,∀v:Fin (z i).1.val,∀j:Fin ℓ,
      (page i).val.testBit (v.val*ℓ+j.val)=(storeRow ((z i).2 v)).val.testBit j.val) (i : Fin S) :
    Texture (z i) (i.val*B) ℓ (bitsAt page bp) := by
  intro v j
  have le:=Nat.mul_le_mul_right ℓ v.isLt
  rw [Nat.succ_mul] at le
  have inside:v.val*ℓ+j.val<B:=by have:=small i;have:=j.isLt;omega
  have row : (i.val*B+(v.val*ℓ+j.val))/B=i.val := by
    rw [Nat.mul_comm i.val B,Nat.mul_add_div bp,Nat.div_eq_of_lt inside,Nat.add_zero]
  have offset : (i.val*B+(v.val*ℓ+j.val))%B=v.val*ℓ+j.val := by
    rw [Nat.mul_comm i.val B,Nat.mul_add_mod,Nat.mod_eq_of_lt inside]
  unfold bitsAt
  rw [row]
  simp only [aligned,i.isLt,dite_eq_left,Fin.eta]
  refine (Computability.VPVNP.LiveHeader.testBit_wordBits (page i) _).symm.trans ?_
  exact (congrArg (page i).val.testBit offset).trans (printed i v j)

theorem issue_budget (sites : Fin S→Site) {q W : ℕ} (wp : 0<W) :
    S≤purchased W (counts (q:=q) sites) := by
  let visit (i : Fin S) : (k : Fin S)×Fin (counts (q:=q) sites k) :=
    ⟨i,⟨0,by change 0<(sites i).rows q;unfold Site.rows;omega⟩⟩
  let code (i : Fin S) := rowIndex wp (counts (q:=q) sites) (visit i)
  have inj : Function.Injective code := fun _ _ eqn=>
    congrArg Sigma.fst ((rowIndex wp (counts (q:=q) sites)).injective eqn)
  simpa using Fintype.card_le_of_injective code inj

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
