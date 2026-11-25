import OAI.Hierarchy.DescentTerminalBoard
import OAI.Hierarchy.ProtocolStackContraction
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Fixed trivalent factors for physical terminal padding and scalar-count digits -/

namespace Hierarchy.DescentTerminalLocalFactors
open ThreeFlat ThreeFlat.Routing
open Computability.BorderVNP.Crossing ProtocolStackContraction DescentTerminalPorts
open scoped Classical BigOperators
noncomputable section

/-- At the first two pin sorts, false selects the zero-mask bit and true
selects the corresponding payload bit. The remaining sort holds count digits. -/
abbrev Pin (J : Type) (bins W : ℕ) := (Bool×J) ⊕ (Fin bins×Fin W)
abbrev Row (J : Type) (bins W : ℕ) := J ⊕ (Fin bins×Fin W)

variable {F : Type*} [CommSemiring F] {bins W : ℕ} {J : Type} [Fintype J]

def pins (mask payload : J→Bool) (frequency : Fin bins×Fin W→Bool) : Pin J bins W→Bool :=
  Sum.elim (fun x=>if x.1 then payload x.2 else mask x.2) frequency

private def wires (r : Row J bins W) : Fin 3→BitSource 0 (Fintype.card (Pin J bins W)) :=
  match r with
  | .inl j => ![.pin (Fintype.equivFin _ (.inl (false,j))),.pin (Fintype.equivFin _ (.inl (true,j))),.constant false]
  | .inr t => ![.pin (Fintype.equivFin _ (.inr t)),.constant false,.constant false]

private def weight (scalar : Fin bins→F) (r : Row J bins W) (x : Fin 3→Bool) : F :=
  match r with
  | .inl _ => if x 0=true → x 1=false then 1 else 0
  | .inr t => if x 0 then scalar t.1^(2^t.2.val) else 1

/-- Two observed pins suffice for a mask check. A selected count digit
contributes its single precomputed power of the shared field menu entry. -/
def network (F : Type*) [CommSemiring F] (J : Type) [Fintype J] (W : ℕ) (scalar : Fin bins→F) :
    BitNetwork F (Fintype.card (Pin J bins W)) where
  internal := 0
  cells := Fintype.card (Row J bins W)
  source i := wires ((Fintype.equivFin _).symm i)
  table i := weight scalar ((Fintype.equivFin _).symm i)

@[simp] theorem network_internal (scalar : Fin bins→F) : (network F J W scalar).internal=0 := rfl

@[simp] theorem network_cells (scalar : Fin bins→F) : (network F J W scalar).cells=Fintype.card J+bins*W := by
  simp [network,Row,Fintype.card_sum,Fintype.card_prod]

private def reading (scalar : Fin bins→F) (mask payload : J→Bool) (f : Fin bins×Fin W→Bool) :
    Row J bins W→F
  | .inl j => if mask j=true → payload j=false then 1 else 0
  | .inr t => if f t then scalar t.1^(2^t.2.val) else 1

theorem network_value (scalar : Fin bins→F) (mask payload : J→Bool) (frequency : Fin bins×Fin W→Bool) :
    TypedWiring.value (network F J W scalar) (pins mask payload frequency) =
      if ∀j,mask j=true → payload j=false then
        ∏b : Fin bins,∏z : Fin W,if frequency (b,z) then scalar b^(2^z.val) else 1 else 0 := by
  let N := network F J W scalar
  let x := pins mask payload frequency
  let bit := fun i=>x ((Fintype.equivFin (Pin J bins W)).symm i)
  have one (r : Row J bins W) (hidden : Fin 0→Bool) :
      N.factor bit hidden (Fintype.equivFin _ r)=reading scalar mask payload frequency r := by
    rcases r with j|⟨b,z⟩ <;>
      simp [N,network,BitNetwork.factor,weight,wires,BitSource.read,bit,x,pins,reading]
  have product : TypedWiring.value N x=∏r : Row J bins W,reading scalar mask payload frequency r := by
    change (∑hidden : Fin 0→Bool,∏ i,N.factor bit hidden i)=_
    have grouped (hidden : Fin 0→Bool) :
        (∏i,N.factor bit hidden i)=∏r : Row J bins W,reading scalar mask payload frequency r :=
      ((Fintype.equivFin (Row J bins W)).prod_comp (N.factor bit hidden)).symm.trans
        (Finset.prod_congr rfl fun r _=>one r hidden)
    rw [Fintype.sum_unique]
    exact grouped _
  rw [show TypedWiring.value (network F J W scalar) (pins mask payload frequency)=_ from product,
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  by_cases good : ∀j,mask j=true → payload j=false
  · have masks : (∏a : J,reading scalar mask payload frequency (.inl a))=1 := by
      apply Finset.prod_eq_one
      intro a _
      exact ite_eq_left (good a)
    rw [ite_eq_left good,masks,one_mul]; rfl
  · obtain ⟨j,hj⟩ := not_forall.mp good
    have zero : (∏a : J,reading scalar mask payload frequency (.inl a))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [reading,hj])
    rw [zero,zero_mul,ite_eq_right good]

/-! The geometric branch supplies one mask bit per payload coordinate on the
fixed graph. Both dummy slot sorts and the last partial true cable are covered. -/
variable {d w cap : ℕ} {P : Type*} {bits : P→ℕ} (N : Network d P bits)
    (code : N.Edge ↪ ℕ) (place : ∀g,Bool→Fin (groupPieces N w g) ↪ Fin cap)
abbrev Payload := Slot (Group N) cap×Fin w

section FixedHost
variable {G : Type} [Fintype G] {sz : G→ℕ} (number : Piece N w ≃ Edge sz)
    (landing : ∀g,Bool→Fin (sz g) ↪ Fin cap)

def unusedOf (q : Slot G cap) : Prop :=
  match q.1 with
  | none => True
  | some g => q.2.2∉Set.range (landing g q.2.1)

def maskOf (x : Slot G cap×Fin w) : Bool := decide <|
  unusedOf landing x.1 ∨ ∃u : Piece N w,x.1=slotOf N number landing false u ∧ N.width u.1≤u.2.val*w+x.2.val

omit [Fintype G] in
theorem maskOf_iff (s : Slot G cap→Fin w→Bool) :
    (∀j : Slot G cap×Fin w,maskOf N number landing j=true→s j.1 j.2=false) ↔
    Padding landing (fun _=>false) s ∧ Slack N (fun u=>s (slotOf N number landing false u)) := by
  constructor
  · intro checked
    constructor
    · constructor
      · intro b i
        funext j
        exact checked ((none,b,i),j) (decide_eq_true (Or.inl trivial))
      · intro g b i unused
        funext j
        exact checked ((some g,b,i),j) (decide_eq_true (Or.inl unused))
    · intro u j tail
      exact checked (slotOf N number landing false u,j) (decide_eq_true (Or.inr ⟨u,rfl,tail⟩))
  · rintro ⟨padding,slack⟩ ⟨⟨g,b,i⟩,j⟩ hj
    rcases of_decide_eq_true hj with outside|⟨u,atSlot,tail⟩
    · cases g with
      | none => exact congrFun (padding.1 b i) j
      | some g => exact congrFun (padding.2 g b i outside) j
    · exact (congrFun (congrArg s atSlot) j).trans (slack u j tail)

theorem physical_value_of (scalar : Fin bins→F) (s : Slot G cap→Fin w→Bool)
    (frequency : Fin bins×Fin W→Bool) :
    TypedWiring.value (network F (Slot G cap×Fin w) W scalar)
      (pins (maskOf N number landing) (fun x=>s x.1 x.2) frequency) =
      if Padding landing (fun _=>false) s ∧ Slack N (fun u=>s (slotOf N number landing false u))
      then ∏b : Fin bins,∏z : Fin W,if frequency (b,z) then scalar b^(2^z.val) else 1 else 0 := by
  rw [network_value]
  exact if_congr (maskOf_iff N number landing s) rfl rfl

end FixedHost

def Unused (q : Slot (Group N) cap) : Prop :=
  match q.1 with
  | none => True
  | some g => q.2.2∉Set.range (place g q.2.1)

def mask (x : Payload (w:=w) (cap:=cap) N) : Bool := maskOf N (cableIndex N w code) place x

theorem mask_iff (s : Slot (Group N) cap→Fin w→Bool) :
    (∀j : Payload (w:=w) (cap:=cap) N,mask N code place j=true→s j.1 j.2=false) ↔
    Padding place (fun _=>false) s ∧ Slack N (fun u=>s (halfSlot N code place false u)) :=
  maskOf_iff N (cableIndex N w code) place s

theorem physical_value (scalar : Fin bins→F) (s : Slot (Group N) cap→Fin w→Bool)
    (frequency : Fin bins×Fin W→Bool) :
    TypedWiring.value (network F (Payload (w:=w) (cap:=cap) N) W scalar)
      (pins (mask N code place) (fun x=>s x.1 x.2) frequency) =
      if Padding place (fun _=>false) s ∧ Slack N (fun u=>s (halfSlot N code place false u))
      then ∏b : Fin bins,∏z : Fin W,if frequency (b,z) then scalar b^(2^z.val) else 1 else 0 :=
  physical_value_of N (cableIndex N w code) place scalar s frequency

end
end Hierarchy.DescentTerminalLocalFactors

end OAI
