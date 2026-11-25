import OAI.Hierarchy.DescentOrderedFixedContact
import OAI.Hierarchy.DescentFixedExceptionalRouter
import OAI.Hierarchy.DescentOrderedResetRows

namespace OAI
/-! # The installed fallback tables read the true incoming and joining ordered cables -/

namespace Hierarchy.DescentFixedExceptionalRouter.Ordered
open Computability.BorderVNP.Crossing DescentNamedContact DescentOrderedReset DescentRouterSlots
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [CommSemiring K]
variable (D : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W) (wt : I→ℕ)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {depth n : ℕ}
    (book : LinkId owner s w ↪ DescentContactTree.Node depth) (key : I↪Fin n)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lp" => link contact owner s w
local notation "cost" => amount contact owner wt s w
local notation "T" => DescentFixedNamedContact.network book lp cost D
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "ids" => itemKey key contact owner s w
local notation "X" => slotSource key contact wt input site owner align s w D
local notation "Y" => slotTarget key contact wt input site owner s w D
local notation "pos" => DescentExceptionalRouter.position D contact input site owner wt s w

private def leafCodec {E J : Type} [Fintype E] [Fintype J] {m : ℕ}
    (names : E ↪ Fin m) (label : E → J) (weight : E → ℕ) (c : J) :
    (Fin (bits label weight (.inr c)) → Bool) ≃ ((i : Fibre label c) → Fin (weight i.val) → Bool) :=
  DescentOrderedWords.decode (DescentOrderedWords.Named.fibreKey names label c) (fun i => weight i.val)

def pins (p : Ports lens) : Ports (bits lp cost)
  | .inl _ => (DescentOrderedWords.decode ids cost).symm (X p)
  | .inr c => (leafCodec ids lp cost c).symm (fun i=>Y p i.val)

local notation "pinsAt" => pins D contact input site owner wt align s w key

omit [Fintype R] in
theorem pins_root (p : Ports lens) : DescentOrderedWords.decode ids cost (pinsAt p (.inl ()))=X p :=
  Equiv.apply_symm_apply _ _

omit [Fintype R] in
theorem pins_leaf (p : Ports lens) : DescentOrderedWords.Named.branchRead ids lp cost (pinsAt p)=Y p := by
  funext i
  have row := (leafCodec ids lp cost (lp i)).apply_symm_apply
    (fun u : Fibre lp (lp i) => Y p u.val)
  exact congrFun row (⟨i,rfl⟩ : Fibre lp (lp i))

omit [Fintype R] in
theorem local_pins : DescentLocalAdapters.Local T pos lens pinsAt := by
  intro v x y agree pn atv
  rcases pn with ⟨⟩|c
  · change (DescentOrderedWords.decode ids cost).symm _ = (DescentOrderedWords.decode ids cost).symm _
    apply congrArg
    funext i j
    have same := agree (rootSlot D contact input site owner wt s w (root contact input site owner s w align i))
      (by simpa [DescentExceptionalRouter.position] using atv)
    exact congrFun same _
  · have rows : (fun i : Fibre lp c => Y x i.val) = (fun i : Fibre lp c => Y y i.val) := by
      funext i j
      have same := agree (linkSlot D contact input site owner wt s w (link contact owner s w i.val))
        (by simpa [DescentExceptionalRouter.position,i.property] using atv)
      exact congrFun same _
    simp only [pins, rows]

def tables : (device D contact input site owner wt s w book).Tables K :=
  DescentLocalAdapters.tables T pos lens (DescentOrderedWords.Named.tables (K:=K) ids book lp cost) pinsAt

omit [Fintype R] in
theorem value (p : Ports lens) : (device D contact input site owner wt s w book).value
    (tables (K:=K) D contact input site owner wt align s w book key) p =
    if ∀e,X p e=Y p e then 1 else 0 := by
  refine (DescentLocalAdapters.value T pos lens (DescentOrderedWords.Named.tables (K:=K) ids book lp cost)
    pinsAt (local_pins D contact input site owner wt align s w book key) p).trans ?_
  refine (DescentOrderedWords.Named.value (K:=K) (D:=D) ids book lp cost (pinsAt p)).trans ?_
  rw [pins_root,pins_leaf]
  have indicators (P Q : Prop) (dp : Decidable P) (dq : Decidable Q) (eqv : P ↔ Q) :
      @ite K P dp 1 0 = @ite K Q dq 1 0 := by
    by_cases h : P
    · simp [h,eqv.mp h]
    · have nq : ¬Q := fun q => h (eqv.mpr q)
      simp [h,nq]
  exact indicators _ _ _ _ ⟨fun h e=>congrFun h e,fun h=>funext h⟩

omit [Fintype R] in
theorem read (a : (device D contact input site owner wt s w book).Assignment) (p : Ports lens) (q : DescentContactTree.Physical.Site depth) :
    (device D contact input site owner wt s w book).read
      (tables (K:=K) D contact input site owner wt align s w book key) a p q=
    let d := DescentFixedNamedContact.code book lp
    let z := DescentOrderedWords.Contact.innerRows (D:=D) ids d cost a
    if ∀i : DescentContactTree.Cell d q.1.val q.2,DescentContactTree.Physical.incoming cost (X p) z q.1 i.val=
      DescentContactTree.Physical.outgoing cost (Y p) z q.1 i.val then 1 else 0 := by
  refine (DescentLocalAdapters.read T pos lens (DescentOrderedWords.Named.tables (K:=K) ids book lp cost)
    pinsAt (local_pins D contact input site owner wt align s w book key) a p q).trans ?_
  refine (DescentOrderedWords.Named.read (K:=K) (D:=D) ids book lp cost a (pinsAt p) q).trans ?_
  simp only [pins_root,pins_leaf]

end
end Hierarchy.DescentFixedExceptionalRouter.Ordered

end OAI
