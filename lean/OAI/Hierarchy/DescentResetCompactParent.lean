import OAI.Hierarchy.DescentHostDirectory
import OAI.Hierarchy.DescentResetDyadicOrder

namespace OAI
/-! # The finite comparison word of a parent at one reset receiver -/
namespace Hierarchy.DescentResetCompactParent
open scoped Classical
noncomputable section

abbrev Label (r : ℕ) := ↥(DescentHostDirectory.codes r)

/-- Good rows use a measured relative base label. Terminals also carry their optional socket. -/
abbrev SiteWord (H r Y : ℕ) := (Fin H × Label r) ⊕ (Fin H × Label r × Fin (Y+1))

/-- The parameters bound the old halo, relative depth, optional socket, old source,
previous capacity, direct-contact slot, and private instruction respectively. -/
abbrev Word (H r Y L cap links program : ℕ) :=
  (Fin 2 × Fin L × Fin cap × Fin cap) ⊕
  (SiteWord H r Y ⊕ ((SiteWord H r Y × Fin links) ⊕ (Fin 2 × SiteWord H r Y × Fin program)))

def append {X Y : Type*} (a : X→X→Prop) (b : Y→Y→Prop) : X⊕Y→X⊕Y→Prop
  | .inl x,.inl y=>a x y
  | .inl _,.inr _=>True
  | .inr _,.inl _=>False
  | .inr x,.inr y=>b x y

def withDigit {X Y : Type*} (a : X→X→Prop) (b : Y→Y→Prop) (x y : X×Y) : Prop :=
  a x.1 y.1 ∨ (¬a x.1 y.1 ∧ ¬a y.1 x.1) ∧ b x.2 y.2

def byFirst {N : ℕ} {X : Type*} (f : X→X→Prop) (a b : Fin N×X) : Prop :=
  a.1<b.1 ∨ a.1=b.1 ∧ f a.2 b.2

def byValue {N : ℕ} {X : Type*} (f : X→X→Prop) (a b : Fin N×X) : Prop :=
  a.1.val<b.1.val ∨ a.1.val=b.1.val ∧ f a.2 b.2

def siteBefore {H r Y : ℕ} (base : ℕ) (zero : Bool) : SiteWord H r Y→SiteWord H r Y→Prop :=
  append (byValue (fun a b : Label r=>a.val.2<b.val.2))
    (byValue (withDigit (fun a b : Label r=>DescentResetDyadicOrder.before base zero a.val.1 a.val.2 b.val.1 b.val.2) (·<·)))

def Word.before {H r Y L cap links program : ℕ} (base : ℕ) (zero : Bool) :
    Word H r Y L cap links program→Word H r Y L cap links program→Prop :=
  let site:=siteBefore (H:=H) (r:=r) (Y:=Y) base zero
  append (byFirst (byValue (byValue (·<·))))
    (append site (append (withDigit site (·<·)) (byFirst (withDigit site (·<·)))))

/-- All natural addresses fit into this finite word dictionary. Its size
depends only on the previous stage's local parameters. -/
theorem site_card (H r Y : ℕ) : Fintype.card (SiteWord H r Y) ≤
    H*(2^(r+1)-1)+H*((2^(r+1)-1)*(Y+1)) := by
  have limit:=DescentHostDirectory.codes_card r
  have bound : Fintype.card (Label r)≤2^(r+1)-1 := by rw [Fintype.card_coe];omega
  simp only [SiteWord,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ bound)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ bound))

theorem word_card (H r Y L cap links program : ℕ) :
    let k:=Fintype.card (SiteWord H r Y)
    Fintype.card (Word H r Y L cap links program)=2*(L*(cap*cap))+(k+(k*links+2*(k*program))) := by
  dsimp only
  simp only [Word,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]

end
end Hierarchy.DescentResetCompactParent

end OAI
