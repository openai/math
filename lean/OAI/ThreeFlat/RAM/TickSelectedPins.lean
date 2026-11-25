import OAI.ThreeFlat.RAM.TickPhysicalABI
import OAI.ThreeFlat.RAM.TickMountedPins
import OAI.ThreeFlat.Diagonal.TickPairProjection

namespace OAI
/-! # Source addresses for the selected tree's external pairs and final wires -/

namespace ThreeFlat.RAM.TickSelectedPins

open Diagonal.ApproximateImage Diagonal.TickAuxiliary
variable {q nt ns np a cap n : ℕ}

/-- A selected factor uses the incoming auxiliary pin in the complete physical tensor. -/
def incoming (q nt ns np : ℕ) (i : Fin a) : Fin (pinCount q nt ns np a) :=
  Fin.natAdd q (Fin.natAdd nt (Fin.natAdd ns (Fin.natAdd np (i.castAdd (a+(a+a))))))

theorem incoming_read {α : Type*} (D : Fin q → α) (t : Fin nt → α) (s : Fin ns → α) (z : Fin np → α)
    (oa na oc nc : Fin a → α) (i : Fin a) :
    fields D t s z oa na oc nc (incoming q nt ns np i) = oa i := by
  simp only [incoming,fields,Fin.append_right,Fin.append_left]

theorem incoming_address {u teams hidden : ℕ} (capacity : ℕ) (i : Fin a) :
    BitLayout.sourceAddress (n:=hidden) (.pin (incoming q nt ns np i)) =
      (TickPhysicalABI.mounted u a teams capacity q nt ns np).oldAux+i.val := by
  simp only [BitLayout.sourceAddress,incoming,Fin.val_natAdd,Fin.val_castAdd,TickPhysicalABI.mounted,
    TickPhysicalABI.layout]
  omega

/-- The two sides of the same external ordinal occupy distinct consecutive
halves of the incoming pair interval. -/
def pair (fit : 1+cap+2*n ≤ a) (q nt ns np : ℕ) (newSide : Bool) (i : Fin n) : Fin (pinCount q nt ns np a) :=
  incoming q nt ns np ⟨1+cap+(if newSide then n else 0)+i.val,by
    have := i.isLt
    cases newSide <;> simp <;> omega⟩

section
variable (fit : 1+cap+2*n ≤ a)

theorem pair_address {u teams hidden : ℕ} (newSide : Bool) (i : Fin n) :
    BitLayout.sourceAddress (n:=hidden) (.pin (pair (a:=a) (cap:=cap) fit q nt ns np newSide i)) =
      (TickPhysicalABI.mounted u a teams cap q nt ns np).oldAux+1+cap+(if newSide then n else 0)+i.val := by
  rw [pair,incoming_address (u:=u) (teams:=teams) (capacity:=cap)]
  simp only [Nat.add_assoc]

theorem pair_read (D : Fin q → Bool) (t : Fin nt → Bool) (s : Fin ns → Bool) (z : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (newSide : Bool) (i : Fin n) :
    fields D t s z oa na oc nc (pair (cap:=cap) fit q nt ns np newSide i) =
      if newSide then newPair fit (project (TickPairHeader.layout cap n fit) oa).pairs i
      else oldPair fit (project (TickPairHeader.layout cap n fit) oa).pairs i := by
  rw [pair,incoming_read]
  cases newSide <;> simp only [Bool.false_eq_true,ite_false,ite_true,oldPair_pin,newPair_pin,Nat.add_zero]

end

/-- Live final wires follow the immutable-length histogram block. Both
incident half-edges refer to the same enumerated physical wire. -/
def wire (q nt ns np : ℕ) {hist live : ℕ} (room : 1+hist+live ≤ a) (i : Fin live) :
    Fin (pinCount q nt ns np a) := incoming q nt ns np ⟨1+hist+i.val, by have := i.isLt; omega⟩

theorem wire_address {u teams hidden hist live : ℕ} (capacity : ℕ) (room : 1+hist+live ≤ a) (i : Fin live) :
    BitLayout.sourceAddress (n:=hidden) (.pin (wire q nt ns np room i)) =
      (TickPhysicalABI.mounted u a teams capacity q nt ns np).oldAux+1+hist+i.val := by
  rw [wire,incoming_address (u:=u) (teams:=teams) (capacity:=capacity)]
  simp only [Nat.add_assoc]

theorem wire_read (D : Fin q → Bool) (t : Fin nt → Bool) (s : Fin ns → Bool) (z : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) {hist live : ℕ} (room : 1+hist+live ≤ a) (i : Fin live) :
    fields D t s z oa na oc nc (wire q nt ns np room i) =
      oa ⟨1+hist+i.val,by have := i.isLt; omega⟩ :=
  incoming_read D t s z oa na oc nc _

end ThreeFlat.RAM.TickSelectedPins

end OAI
