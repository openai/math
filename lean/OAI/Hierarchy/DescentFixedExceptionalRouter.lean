import OAI.Hierarchy.DescentFixedNamedContact
import OAI.Hierarchy.DescentExceptionalRouter
import OAI.Hierarchy.DescentSubstitutionDegree

namespace OAI
/-! # End-to-end exceptional routing with two physical banks of binary relay trees -/

namespace Hierarchy.DescentFixedExceptionalRouter
open Computability.BorderVNP.Crossing DescentRouterSlots DescentNamedContact
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (wt : I→ℕ)
variable (align : ∀s i,site s (input s i)=owner s (contact i))
variable (s : Bool) (w : W) {depth : ℕ} (book : LinkId owner s w ↪ DescentContactTree.Node depth)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "T" => DescentFixedNamedContact.network book lp cost D
local notation "slot" => DescentNetworkSubstitution.Slot B (s,w)
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)

open DescentExceptionalRouter (position words words_local)

def device : Network D slot lens := DescentLocalAdapters.graph T (position D contact input site owner wt s w) lens

def tables : (device D contact input site owner wt s w book).Tables K :=
  DescentLocalAdapters.tables T (position D contact input site owner wt s w) lens
    (DescentFixedNamedContact.tables (K:=K) book lp cost D) (words D contact input site owner wt align s w)

omit [Fintype R] in
/-- This device actually reads its own external root and its assigned direct-link
words, with its contact order translated through the true common bundle labels. -/
theorem value (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt) :
    (device D contact input site owner wt s w book).value (tables (K:=K) D contact input site owner wt align s w book)
      (DescentRouterBank.feed D contact input site owner wt x z s w)=
      if ∀i,owner s (contact i)=w → x s i=z i then 1 else 0 := by
  let f := DescentRouterBank.feed D contact input site owner wt x z s w
  refine (DescentLocalAdapters.value T (position D contact input site owner wt s w) lens
    (DescentFixedNamedContact.tables (K:=K) book lp cost D) (words D contact input site owner wt align s w)
    (words_local D contact input site owner wt align s w T) f).trans ?_
  refine (DescentFixedNamedContact.value_words (K:=K) book lp cost D (sourceWord D contact input site owner wt s w align f)
    (targetWord D contact input site owner wt s w f)).trans ?_
  have indicators (P Q : Prop) (dp : Decidable P) (dq : Decidable Q) (eqv : P ↔ Q) :
      @ite K P dp 1 0 = @ite K Q dq 1 0 := by
    by_cases h : P
    · simp [h,eqv.mp h]
    · have nq : ¬ Q := fun q => h (eqv.mpr q)
      simp [h,nq]
  exact indicators _ _ _ _ (word_agreement D contact input site owner wt s w align x z)

theorem degree (single : Subsingleton (InputId site s w)) (v : (device D contact input site owner wt s w book).Site) :
    (device D contact input site owner wt s w book).bitDegree v≤3 := by
  have one : Function.Injective (fun _ : InputId site s w=>()) := fun _ _ _=>single.elim _ _
  exact (DescentLocalAdapters.degree _ _ _ ((Sum.map_injective.mpr ⟨one,Function.injective_id⟩).comp
    (names D contact input site owner wt s w).injective) v).trans (DescentFixedNamedContact.degree book lp cost D v)

omit [Fintype R] in
theorem wires : (∑e,(device D contact input site owner wt s w book).width e)=
    depth*∑i : Item contact owner s w,wt i.val :=
  DescentFixedNamedContact.wires book lp cost D

end
end Hierarchy.DescentFixedExceptionalRouter

end OAI
