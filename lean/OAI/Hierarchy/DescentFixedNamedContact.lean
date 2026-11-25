import OAI.Hierarchy.DescentNamedContact

namespace OAI
/-! # A physical contact tree indexed by a common external directory -/

namespace Hierarchy.DescentFixedNamedContact
open Computability.BorderVNP.Crossing DescentContactTree DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {I C : Type} [Fintype I] [Fintype C] {h : ℕ} (book : C ↪ Node h) (contact : I→C) (wt : I→ℕ)

def place : Pin C→Physical.Terminal h := Sum.map id book

def code (i : I) (n : ℕ) : Bool := if hit : n<h then book (contact i) ⟨n,hit⟩ else false

omit [Fintype I] [Fintype C] in
private theorem prefix_eq (i : I) : prefixAt (code book contact) h i=book (contact i) := by
  funext n
  simp [prefixAt,code,n.isLt]

def paddedTree (D : ℕ) := Physical.graph (code book contact) wt D h

def network (D : ℕ) := DescentLocalAdapters.graph (paddedTree book contact wt D) (place book) (bits contact wt)

private def encode (p : Ports (bits contact wt)) :=
  Physical.exposed (h:=h) (code book contact) wt (root contact wt p) (branches contact wt p)

omit [Fintype C] in
theorem at_terminals (D : ℕ) :
    DescentLocalAdapters.Local (paddedTree book contact wt D) (place book) (bits contact wt) (encode book contact wt) := by
  intro v p q seen oldpin atv
  rcases oldpin with ⟨⟩|leaf
  · have kept := seen (.inl ()) atv
    exact congrArg (fun word => (Physical.concat wt).symm (Physical.concat wt word)) kept
  · change (Physical.childCode (code book contact) wt h leaf).symm _ =
      (Physical.childCode (code book contact) wt h leaf).symm _
    apply congrArg
    funext i
    have eqleaf : book (contact i.val)=leaf := (prefix_eq book contact i.val).symm.trans i.property
    have kept := seen (.inr (contact i.val)) (by simpa [place,eqleaf] using atv)
    change Physical.concat _ (p (.inr (contact i.val))) _=Physical.concat _ (q (.inr (contact i.val))) _
    rw [kept]

variable {K : Type*} [CommSemiring K]

def tables (D : ℕ) := DescentLocalAdapters.tables (paddedTree book contact wt D) (place book) (bits contact wt)
  (Physical.tables (K:=K) (code book contact) wt) (encode book contact wt)

omit [Fintype C] in
theorem value (D : ℕ) (p : Ports (bits contact wt)) :
    (network book contact wt D).value (tables (K:=K) book contact wt D) p =
      if root contact wt p=branches contact wt p then 1 else 0 :=
  (DescentLocalAdapters.value _ _ _ _ _ (at_terminals book contact wt D) p).trans
    (Physical.value (code book contact) wt _ _)

omit [Fintype C] in
theorem value_words (D : ℕ) (x y : Physical.Row wt) :
    (network book contact wt D).value (tables (K:=K) book contact wt D) (write contact wt x y) =
      if x=y then 1 else 0 := by
  rw [value]
  simp [root,branches,write]

theorem degree (D : ℕ) (v : (network book contact wt D).Site) : (network book contact wt D).bitDegree v≤3 :=
  (DescentLocalAdapters.degree _ _ _ (Sum.map_injective.mpr ⟨Function.injective_id,book.injective⟩) v).trans
    (Physical.degree (code book contact) wt v)

omit [Fintype C] in
theorem wires (D : ℕ) : (∑e,(network book contact wt D).width e)=h*∑i,wt i :=
  Physical.wire_cost (D:=D) (h:=h) (code book contact) wt

omit [Fintype C] in
theorem sites (D : ℕ) : Fintype.card (network book contact wt D).Site+1=2^(h+1) :=
  Physical.sites (D:=D) (h:=h) (code book contact) wt

end
end Hierarchy.DescentFixedNamedContact

end OAI
