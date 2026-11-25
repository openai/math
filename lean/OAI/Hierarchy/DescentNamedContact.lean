import OAI.Hierarchy.DescentContactDegree
import OAI.Hierarchy.DescentContactCodes
import OAI.Hierarchy.DescentLocalAdapters

namespace OAI
/-! # Real packed contact pins at the leaves of each binary router -/

namespace Hierarchy.DescentNamedContact
open Computability.BorderVNP.Crossing DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {I C : Type} [Fintype I] [Fintype C] (contact : I→C) (wt : I→ℕ)

abbrev Fibre (c : C) := {i : I // contact i=c}
def width (c : C) := ∑i : Fibre contact c,wt i.val

/-- The same ordinal/bit encoding is used at both ends of a contact. -/
def labels : Ports (width contact wt) ≃ Physical.Row wt where
  toFun x i := Physical.concat (fun t : Fibre contact (contact i)=>wt t.val) (x (contact i)) ⟨i,rfl⟩
  invFun y c := (Physical.concat (fun t : Fibre contact c=>wt t.val)).symm (fun t=>y t.val)
  left_inv x := by
    funext c
    apply (Physical.concat (fun t : Fibre contact c=>wt t.val)).injective
    rw [Equiv.apply_symm_apply]
    funext t
    rcases t with ⟨j,rfl⟩
    rfl
  right_inv x := by funext i;simp

abbrev Pin (C : Type) := Unit ⊕ C
def bits : Pin C → ℕ
  | .inl _ => ∑i,wt i
  | .inr c => width contact wt c

def place : Pin C → Physical.Terminal (codeHeight C) := Sum.map id (directory C)
def code (i : I) := contactBit (contact i)

omit [Fintype I] in
private theorem terminalPrefix (i : I) : prefixAt (code contact) (codeHeight C) i=directory C (contact i) :=
  prefix_contactBit (contact i)

def root (p : Ports (bits contact wt)) := Physical.concat wt (p (.inl ()))
def branches (p : Ports (bits contact wt)) := labels contact wt (fun c=>p (.inr c))
def write (x y : Physical.Row wt) : Ports (bits contact wt)
  | .inl _ => (Physical.concat wt).symm x
  | .inr c => (labels contact wt).symm y c

def paddedTree (D : ℕ) := Physical.graph (code contact) wt D (codeHeight C)

def network (D : ℕ) := DescentLocalAdapters.graph (paddedTree contact wt D) (place (C:=C)) (bits contact wt)

private def encode (p : Ports (bits contact wt)) :=
  Physical.exposed (h:=codeHeight C) (code contact) wt (root contact wt p) (branches contact wt p)

private theorem at_terminals (D : ℕ) :
    DescentLocalAdapters.Local (paddedTree contact wt D) (place (C:=C)) (bits contact wt) (encode contact wt) := by
  intro v p q seen oldpin atv
  rcases oldpin with ⟨⟩|leaf
  · have kept := seen (.inl ()) atv
    exact congrArg (fun word => (Physical.concat wt).symm (Physical.concat wt word)) kept
  · change (Physical.childCode (code contact) wt (codeHeight C) leaf).symm _ =
      (Physical.childCode (code contact) wt (codeHeight C) leaf).symm _
    apply congrArg
    funext i
    have eqleaf : directory C (contact i.val)=leaf := (terminalPrefix contact i.val).symm.trans i.property
    have kept := seen (.inr (contact i.val)) (by simpa [place,eqleaf] using atv)
    change Physical.concat _ (p (.inr (contact i.val))) _=Physical.concat _ (q (.inr (contact i.val))) _
    rw [kept]

variable {K : Type*} [CommSemiring K]

def tables (D : ℕ) := DescentLocalAdapters.tables (paddedTree contact wt D) (place (C:=C)) (bits contact wt)
  (Physical.tables (K:=K) (code contact) wt) (encode contact wt)

theorem value (D : ℕ) (p : Ports (bits contact wt)) :
    (network contact wt D).value (tables (K:=K) contact wt D) p =
      if root contact wt p=branches contact wt p then 1 else 0 :=
  (DescentLocalAdapters.value _ _ _ _ _ (at_terminals contact wt D) p).trans
    (Physical.value (code contact) wt _ _)

theorem value_words (D : ℕ) (x y : Physical.Row wt) :
    (network contact wt D).value (tables (K:=K) contact wt D) (write contact wt x y) =
      if x=y then 1 else 0 := by
  rw [value]
  simp [root,branches,write]

theorem degree (D : ℕ) (v : (network contact wt D).Site) : (network contact wt D).bitDegree v≤3 :=
  (DescentLocalAdapters.degree _ _ _ (Sum.map_injective.mpr ⟨Function.injective_id,(directory C).injective⟩) v).trans
    (Physical.degree (code contact) wt v)

theorem wires (D : ℕ) : (∑e,(network contact wt D).width e)=codeHeight C*∑i,wt i :=
  Physical.wire_cost (D:=D) (h:=codeHeight C) (code contact) wt

theorem width_sum : (∑c,width contact wt c)=∑i,wt i := by
  unfold width
  rw [←Fintype.sum_sigma' (fun c (i : {i // contact i=c}) => wt i.val)]
  exact (Equiv.sigmaFiberEquiv contact).sum_comp wt

end
end Hierarchy.DescentNamedContact

end OAI
