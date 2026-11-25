import OAI.Hierarchy.DescentResetRotorGates
import OAI.Hierarchy.DescentRecipeFootprint
import OAI.Hierarchy.DescentBoundedBitHistory

namespace OAI
/-! # Per-digit physical bit references for a unary rotor ROM request -/

namespace Hierarchy.DescentResetGates
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.BorderVNP.Crossing DescentRotor DescentPhysicalSplit DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
open private Physical.endpoint from OAI.Hierarchy.DescentRotorNetwork
open private Physical.local_legs from OAI.Hierarchy.DescentTrivalentRotor
open private DescentPhysicalSplit.cablePort from OAI.Hierarchy.DescentPhysicalSplit

/-- Flattening one layer, carried digit and bit in the actual physical rotor bundle. -/
def digitBit {R u w : ℕ} (r : Fin R) (k : Fin u) (j : Fin w) : Fin (R*(u*w)) :=
  finProdFinEquiv (r,finProdFinEquiv (k,j))

theorem bundle_digit {R u w : ℕ} (x : Word (R*(u*w))) (r : Fin R) (k : Fin u) :
    Physical.bundle R u w x r k=bitWord w (fun j=>x (digitBit r k j)) := rfl

variable {D : ℕ} {P₀ : Type} [Fintype P₀] {bits₀ : P₀→ℕ} (N : Network D P₀ bits₀)

def tupleBit (v : N.Site) (p : Fibre N v) (j : Fin (width N p.val)) : Fin (∑i,localWidth N v i) :=
  finSigmaFinEquiv ⟨index N v p,Fin.cast (by simp [localWidth,name]) j⟩

theorem tupleBit_read (v : N.Site) (p : Fibre N v) (x : Word (∑i,localWidth N v i)) (j : Fin (width N p.val)) :
    fromTuple N (tuple N v x) p j=x (tupleBit N v p j) := rfl

variable {K E : Type} [Field K] [Fintype E] {n h C w u : ℕ} (G : Graph n h)
variable {hw : 0<w} {src dst : E→Fin (2^n)} {pay : ℝ} (P : BaseCircuit K G C w u hw src dst pay) (d : ℕ)
local notation "H" => Physical.host G.arcs d P.layers C w u
local notation "Q" => Physical.rotor G P d

/-- For every fixed scalar gate, just the selected digit of each of the two demand words
and each supply port word is fetched. Every selected bit belongs to the single spine cable. -/
def rootColumn (v : Fin (2^n)) (r : Fin P.layers) (k : Fin u) :
    (s : Slot G.arcs v)→Fin (SlotWidth G.arcs C w v s)→Fin (∑i,localWidth H v i)
  | .inl b,j => tupleBit H v ⟨.inl (v,b),rfl⟩ (digitBit r k j)
  | .inr p,j => let e : Incident H v := Physical.endpoint G.arcs v p
    tupleBit H v (DescentPhysicalSplit.cablePort H v e) (Fin.cast
      (by unfold DescentPhysicalSplit.cablePort; split <;> rfl : (H).width e.val=width H (DescentPhysicalSplit.cablePort H v e).val)
      (digitBit r k j))

def rootKey (v : Fin (2^n)) (r : Fin P.layers) (read : (s : Slot G.arcs v)→Word (SlotWidth G.arcs C w v s)) : RomKey G C w :=
  key G.arcs C w (P.rotation r,⟨v,bitWord w (read (.inl false)),bitWord w (read (.inl true)),
    fun p=>bitWord (C*w) (read (.inr p))⟩)

theorem rootKey_read (v : Fin (2^n)) (r : Fin P.layers) (k : Fin u) (x : Word (∑i,localWidth H v i)) :
    rootKey G P v r (fun s j=>x (rootColumn G P d v r k s j))=rootAddress G P d v (tuple H v x) r k := rfl

def rootBoundary (v : Fin (2^n)) : Boundary Q ⟨v,.inl false⟩ := .inl ⟨.inr ⟨v,0⟩,Or.inl rfl⟩

def rootRef (v : Fin (2^n)) (r : Fin P.layers) (k : Fin u) (s : Slot G.arcs v) (j : Fin (SlotWidth G.arcs C w v s)) :
    BitRef (boundaryWidth Q ⟨v,.inl false⟩) := ⟨rootBoundary G P d v,rootColumn G P d v r k s j⟩

/-- The concrete root's request is reconstructed solely from the listed slot bits of this digit. -/
theorem rootRequest_read (v : Fin (2^n)) (r : Fin P.layers) (k : Fin u) (a : (Q).Assignment) (pins : Ports (fun _ : Physical.Pin (2^n)=>P.layers*(u*w))) :
    (rotorCalls G P d).request ⟨v,.inl false⟩ (r,k) a pins =
      .lookup (rootKey G P v r (fun s j=>a (.inr ⟨v,0⟩) (rootColumn G P d v r k s j))) :=
  congrArg Request.lookup (rootKey_read G P d v r k _).symm

/-- Across the whole unary site, the gathered ROM operands have exactly one spine word's width. -/
theorem allRootBits (v : Fin (2^n)) :
    (∑_g : Fin P.layers × Fin u,∑s : Slot G.arcs v,SlotWidth G.arcs C w v s)=
      (Q).width (.inr ⟨v,0⟩) := by
  change _=∑i,localWidth H v i
  rw [show (∑i,localWidth H v i)=(∑p : Fibre H v,width H p.val) from
    (index H v).symm.sum_comp (fun p=>width H p.val)]
  simp_rw [Physical.local_legs]
  rw [(Physical.rowFibre G v).sum_comp (fun s=>P.layers*(u*SlotWidth G.arcs C w v s)),
    ←Finset.mul_sum,←Finset.mul_sum]
  simp [Nat.mul_assoc]

end
end Hierarchy.DescentResetGates

end OAI
