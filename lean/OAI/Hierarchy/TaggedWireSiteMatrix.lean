import OAI.LinearAlgebra.SpectralBooks.RawTiledTables

namespace OAI
/-! # Ordinary contractions of specified named-site matrices -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

variable {F : Type*} [Field F] {S : ℕ}
abbrev SiteMatrix (A B : Fin S→Type) (F : Type*) := ∀i,A i→B i→F

namespace SiteMatrix
variable {A B C : Fin S→Type} [∀i,Fintype (B i)] [∀i,Fintype (C i)]

def act (M : SiteMatrix A B F) (f : (∀i,B i)→F) (x : ∀i,A i) :=
  ∑ y,f y*∏i,M i (x i) (y i)

def compose (M : SiteMatrix A B F) (N : SiteMatrix B C F) : SiteMatrix A C F :=
  fun i x z=>∑y,N i y z*M i x y

theorem act_compose (M : SiteMatrix A B F) (N : SiteMatrix B C F) (f : (∀i,C i)→F)
    (x : ∀i,A i) : act M (act N f) x=act (compose M N) f x := by
  simp only [act,compose,Finset.sum_mul,Fintype.prod_sum,Finset.mul_sum,Finset.prod_mul_distrib,mul_assoc]
  exact Finset.sum_comm

theorem act_sum {T : Type*} [Fintype T] (M : SiteMatrix A B F) (f : T→(∀i,B i)→F)
    (x : ∀i,A i) : act M (fun y=>∑t,f t y) x=∑t,act M (f t) x := by
  simp only [act,Finset.sum_mul]
  exact Finset.sum_comm

def identity (A : Fin S→Type) : SiteMatrix A A F := fun _ x y=>if y=x then 1 else 0

theorem act_id (f : (∀i,B i)→F) (x : ∀i,B i) : act (identity B) f x=f x := by
  have point (y : ∀i,B i) : (∀i,y i=x i)↔y=x := funext_iff.symm
  simp [act,identity,Fintype.prod_boole,point,mul_ite]

end SiteMatrix

end Hierarchy.WireTelescope

end
end OAI
