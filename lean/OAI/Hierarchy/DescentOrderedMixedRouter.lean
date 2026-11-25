import OAI.Hierarchy.DescentOrderedGoodRouter
import OAI.Hierarchy.DescentOrderedExceptionalRouter
import OAI.Hierarchy.DescentMixedRouter

namespace OAI
/-! # One installed bank of chronologically addressed rotor and fallback tables -/

namespace Hierarchy.DescentMixedRouter.Ordered
open Computability.BorderVNP.Crossing DescentRouterSlots DescentOrderedReset DescentRouterBank
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped BigOperators Classical
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits M : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (key : I↪Fin M)
local notation "wt" => fun _ : I=>u
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align
variable {s : Bool} {w : W} (D : ℕ)
local notation "B" => DescentRouterBank.network D contact input site owner wt
local notation "lens" => DescentNetworkSubstitution.slotWidth B (s,w)
local notation "X" => slotSource key contact wt input site owner align s w D
local notation "Y" => slotTarget key contact wt input site owner s w D

def localTables : (c : Ch s w) → (device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) c).Tables K
  | .exceptional one => DescentFixedExceptionalRouter.Ordered.tables (K:=K) D contact input site owner wt align s w one.book.codes key
  | .good first last _ P => DescentGoodRouter.Ordered.tables D u contact input site owner align s w G first last P key

omit [Fintype R] in
theorem local_value (c : Ch s w) (p : Ports lens) :
    (device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) c).value
      (localTables (K:=K) (C₀:=C₀) G hw u contact input site owner align key D c) p =
    if ∀i,X p i=Y p i then 1 else 0 := by
  cases c with
  | exceptional one => exact DescentFixedExceptionalRouter.Ordered.value (K:=K) D contact input site owner wt align s w one.book.codes key p
  | good first last pay P => exact DescentGoodRouter.Ordered.value D u contact input site owner align s w G first last P key p

/-- Every actual selected device uses the common old chronological wire key. -/
def coefficients (key : I ↪ Fin M) (D : ℕ) (select : ∀ s w, Ch s w) :
    (DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).Tables K :=
  DescentNetworkSubstitution.tables (DescentRouterBank.network D contact input site owner wt)
    (fun v : Bool × W => device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))
    (fun v : Bool × W => localTables (K:=K) (C₀:=C₀) G hw u contact input site owner align key D (select v.1 v.2))

def «public» (p : Ports (publicWidth input wt)) (b : Bool) := words key (input b) wt (fun r=>p (b,r))

omit [Fintype R] in
theorem value (key : I ↪ Fin M) (D : ℕ)
    (select : ∀ (b : Bool) (v : W), Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align b v)
    (p : Ports (publicWidth input wt)) :
    (DescentMixedRouter.network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).value
      (coefficients (K:=K) (C₀:=C₀) G hw u contact input site owner align key D select) p =
    if «public» u input key p false=«public» u input key p true then (1 : K) else 0 := by
  let bank := DescentRouterBank.network D contact input site owner wt
  let dev := fun v : Bool × W => device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2)
  let tab := fun v : Bool × W => localTables (K:=K) (C₀:=C₀) G hw u contact input site owner align key D (select v.1 v.2)
  refine (DescentNetworkSubstitution.value_substitute bank dev tab p).trans ?_
  have ones (z : bank.Assignment) (b : Bool) (a : W) :
      bank.read (DescentNetworkSubstitution.coefficients bank dev tab) z p (b,a) =
      if ∀i,owner b (contact i)=a → «public» u input key p b i=words key contact wt z i then (1:K) else 0 := by
    refine (DescentNetworkSubstitution.read_coefficient bank dev tab z p (b,a)).trans ?_
    refine (local_value (K:=K) (C₀:=C₀) G hw u contact input site owner align key D
      (select b a) (DescentNetworkSubstitution.visible bank z p (b,a))).trans ?_
    refine if_congr ?_ rfl rfl
    constructor
    · intro all i used
      funext j
      let e : Item contact owner b a := ⟨i,used⟩
      have h:=DescentOrderedReset.visible_read key contact wt input site owner align b a D p z e j
      exact h.1.symm.trans ((congrFun (all e) j).trans h.2)
    · intro all e
      funext j
      have h:=DescentOrderedReset.visible_read key contact wt input site owner align b a D p z e j
      exact h.1.trans ((congrFun (all e.val e.property) j).trans h.2.symm)
  let read:=«public» u input key p
  have term (z : bank.Assignment) : (∏ v : bank.Site,bank.read (DescentNetworkSubstitution.coefficients bank dev tab) z p v) =
      if read false=words key contact wt z ∧ read true=words key contact wt z then 1 else 0 := by
    calc _=∏ v : Bool×W, if ∀i,owner v.1 (contact i)=v.2→ read v.1 i=words key contact wt z i then (1:K) else 0 :=
            Finset.prod_congr rfl (fun ⟨b,a⟩ _=>ones z b a)
         _=_ := by
           rw [Fintype.prod_boole]
           apply if_congr _ rfl rfl
           constructor
           · intro all
             exact ⟨funext (fun i=>all (false,owner false (contact i)) i rfl),
               funext (fun i=>all (true,owner true (contact i)) i rfl)⟩
           · rintro ⟨f,t⟩ ⟨(_|_),a⟩ i _
             · exact congrFun f i
             · exact congrFun t i
  unfold Network.value
  simp_rw [term]
  rw [←(words key contact wt).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  by_cases same : read false=read true
  · change _ = if read false = read true then _ else _
    simp [same]
  · have no (a : DescentContactTree.Physical.Row wt) : ¬(read false=a ∧ read true=a) :=
      fun h=>same (h.1.trans h.2.symm)
    change _=if read false=read true then _ else _
    simp [no,same]

end
end Hierarchy.DescentMixedRouter.Ordered

end OAI
