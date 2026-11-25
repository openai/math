import OAI.Hierarchy.DescentGoodRouter
import OAI.Hierarchy.DescentFixedExceptionalRouter

namespace OAI
/-! # A complete physical reset with good-base rotors and exceptional contact trees -/

namespace Hierarchy.DescentMixedRouter
open Computability.BorderVNP.Crossing DescentRouterSlots DescentRotor DescentBaseProfile
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped Classical BigOperators
noncomputable section
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable {n h C₀ bits : ℕ} (G : NonlinearExpanders.Graph n h) (hw : 0<bits)
variable (u : ℕ) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i))

/-- A contact tree can reserve leaves for the complete common roster. -/
structure Book (C : Type) where
  height : ℕ
  codes : C ↪ DescentContactTree.Node height

def Book.observed (C : Type) [Fintype C] : Book C :=
  ⟨DescentContactTree.codeHeight C,DescentContactTree.directory C⟩

structure ExceptionalData (root link : Type) where
  single : Subsingleton root
  book : Book link

/-- The good constructor stores the actual powered binary rotor, not a
coefficient hypothesis. At an exceptional site every local input belongs to
one old terminal. Each terminal's directory and depth are independent. -/
inductive Choice (s : Bool) (w : W) : Type where
  | exceptional (directory : ExceptionalData (InputId site s w) (LinkId owner s w))
  | good (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n)) (pay : ℝ)
      (P : BaseCircuit K G C₀ bits u hw (fun e : Item contact owner s w => first (root contact input site owner s w align e))
        (fun e : Item contact owner s w => last (link contact owner s w e)) pay)

variable {D : ℕ} {s : Bool} {w : W}
local notation "wt" => fun _ : I=>u
local notation "Ch" => Choice (K:=K) (C₀:=C₀) G hw u contact input site owner align

/-- Direct construction of the good branch from the actual integer matrix
row/column budgets and the fixed configurable rotor. -/
def from_matrix (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
    (hu : 0<u) (menu : ∀π : Equiv.Perm (Fin (2^n)),Configures K G.arcs C₀ bits π)
    (F B : ℝ) (unit : (u:ℝ)≤B) (scale : ((2^n:ℕ):ℝ)^2*bits≤F)
    (row : ∀i,(∑j,(matrixOfBundles (fun e : Item contact owner s w => first (root contact input site owner s w align e))
      (fun e : Item contact owner s w => last (link contact owner s w e)) i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ))
    (col : ∀j,(∑i,(matrixOfBundles (fun e : Item contact owner s w => first (root contact input site owner s w align e))
      (fun e : Item contact owner s w => last (link contact owner s w e)) i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ)) : Ch s w :=
  .good first last (F*B) (Classical.choice (circuit_of_matrix G C₀ bits u hw hu menu _ _ unit scale row col))

local notation "B" => DescentRouterBank.network D contact input site owner wt

def device : Ch s w → Network D (DescentNetworkSubstitution.Slot B (s,w)) (DescentNetworkSubstitution.slotWidth B (s,w))
  | .exceptional t => DescentFixedExceptionalRouter.device D contact input site owner wt s w t.book.codes
  | .good first last _ P => DescentGoodRouter.device D u contact input site owner align s w G first last P

def tables : (c : Ch s w) → (device G hw u contact input site owner align (D:=D) c).Tables K
  | .exceptional t => DescentFixedExceptionalRouter.tables D contact input site owner wt align s w t.book.codes
  | .good first last _ P => DescentGoodRouter.tables D u contact input site owner align s w G first last P

def charge : Ch s w → ℝ
  | .exceptional one => (one.book.height*∑_i : Item contact owner s w,u : ℕ)
  | .good _ _ pay _ => 21*((2*h+4)*(2*h*C₀+2):ℕ)*pay

omit [Fintype R] in
theorem device_value (c : Ch s w) (x : Bool→DescentContactTree.Physical.Row wt) (z : DescentContactTree.Physical.Row wt) :
    (device G hw u contact input site owner align (D:=D) c).value (tables G hw u contact input site owner align (D:=D) c)
      (DescentRouterBank.feed D contact input site owner wt x z s w) =
      if ∀i,owner s (contact i)=w → x s i=z i then (1:K) else 0 := by
  cases c with
  | exceptional one => exact DescentFixedExceptionalRouter.value D contact input site owner wt align s w one.book.codes x z
  | good first last pay P => exact DescentGoodRouter.value D u contact input site owner align s w G first last P x z

theorem device_degree (c : Ch s w) (v : (device G hw u contact input site owner align (D:=D) c).Site) :
    (device G hw u contact input site owner align (D:=D) c).bitDegree v≤3 := by
  cases c with
  | exceptional one => exact DescentFixedExceptionalRouter.degree D contact input site owner wt s w one.book.codes one.single v
  | good first last pay P => exact DescentGoodRouter.degree D u contact input site owner align s w G first last P v

omit [Fintype R] in
theorem device_cost (c : Ch s w) :
    ((∑e,(device G hw u contact input site owner align (D:=D) c).width e : ℕ):ℝ)≤
      charge G hw u contact input site owner align c := by
  cases c with
  | exceptional one =>
    exact (congrArg (fun n : ℕ => (n : ℝ))
      (DescentFixedExceptionalRouter.wires D contact input site owner wt s w one.book.codes)).le
  | good first last pay P => exact DescentGoodRouter.wires D u contact input site owner align s w G first last P

def network (select : ∀ s w, Ch s w) (D : ℕ) : Network D (Bool × R) (DescentRouterBank.publicWidth input wt) :=
  DescentNetworkSubstitution.network (DescentRouterBank.network D contact input site owner wt)
    (fun v=>device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))

def coefficients (select : ∀ s w, Ch s w) (D : ℕ) :
    (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).Tables K :=
  DescentNetworkSubstitution.tables (DescentRouterBank.network D contact input site owner wt)
    (fun v=>device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))
    (fun v=>tables (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))

omit [Fintype R] in
theorem value (select : ∀ s w, Ch s w) (p : Ports (DescentRouterBank.publicWidth input wt)) :
    (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).value
      (coefficients (K:=K) (C₀:=C₀) G hw u contact input site owner align select D) p =
      if DescentRouterBank.publicRows input wt p false=DescentRouterBank.publicRows input wt p true then (1:K) else 0 :=
  DescentRouterBank.substituted_value (K:=K) (d:=D) D contact input site owner wt
    (fun v=>device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))
    (fun v=>tables (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2))
    (fun x z a v=>device_value (K:=K) G hw u contact input site owner align (D:=D) (select a v) x z) p

theorem degree (select : ∀ s w, Ch s w)
    (v : (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).Site) :
    (network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).bitDegree v≤3 := by
  have bound {A : Type} {width : A → ℕ} (N : Network D A width) (j : N.Site)
      {left right : Fintype A} {count : ℕ}
      (same : count = @Network.bitDegree D A left width N j)
      (limit : @Network.bitDegree D A right width N j ≤ 3) : count ≤ 3 := by
    cases Subsingleton.elim left right
    exact same.le.trans limit
  let child (j : Bool × W) := device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select j.1 j.2)
  have same := DescentNetworkSubstitution.degree B child v.1 v.2
  have limit := device_degree (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1.1 v.1.2) v.2
  exact bound (child v.1) v.2 same limit

omit [Fintype R] in
theorem cost (select : ∀ s w, Ch s w) :
    ((∑e,(network (K:=K) (C₀:=C₀) G hw u contact input site owner align select D).width e:ℕ):ℝ) ≤
    ((∑_i : I,u : ℕ):ℝ)+∑v : Bool×W,charge G hw u contact input site owner align (select v.1 v.2) := by
  unfold network
  rw [DescentNetworkSubstitution.total_width,DescentRouterBank.contact_width,Nat.cast_add]
  rw [Nat.cast_sum (s := Finset.univ) (f := fun v : Bool × W =>
    ∑ e, (device (K:=K) (C₀:=C₀) G hw u contact input site owner align (D:=D) (select v.1 v.2)).width e)]
  exact add_le_add (le_refl _) (Finset.sum_le_sum (fun (v : Bool × W) _=>
    device_cost (D:=D) G hw u contact input site owner align (select v.1 v.2)))

end
end Hierarchy.DescentMixedRouter

end OAI
