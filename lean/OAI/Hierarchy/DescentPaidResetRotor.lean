import OAI.Hierarchy.DescentBatchedRotor
import OAI.Hierarchy.DescentRotorPrivateFields

namespace OAI
/-! # Rotor operation counts from the mounted layer and fixed local leg -/
namespace Hierarchy.DescentPaidResidentCount.Reset.Rotor
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.BorderVNP.Crossing DescentRotor DescentResetGates DescentPhysicalSplit DescentKernelHistory DescentRouterSlots
open DescentLaneGates
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1200000
variable {I C R W K : Type} [Fintype I] [Fintype C] [Fintype R] [Fintype W] [Field K]
variable (D m p : ℕ) (hp : 0<p) (contact : I→C) (input : Bool→I→R) (site : Bool→R→W) (owner : Bool→C→W)
variable (align : ∀s i,site s (input s i)=owner s (contact i)) (s : Bool) (w : W) {n h b C₀ num : ℕ}
    (G : Graph n h) {hw : 0<b} {pay : ℝ} (first : InputId site s w ↪ Fin (2^n)) (last : LinkId owner s w ↪ Fin (2^n))
local notation "u" => m*p
variable (P : BaseCircuit K G C₀ b (m*p) hw
    (fun e : Item contact owner s w => first (root contact input site owner s w align e))
    (fun e : Item contact owner s w => last (link contact owner s w e)) pay) (key : I↪Fin num)
local notation "H" => Physical.host G.arcs D P.layers C₀ b (m*p)
local notation "bare" => Physical.host G.arcs 0 0 0 0 0
local notation "prg" => DescentBatchedRotor.program D m p hp contact input site owner align s w G first last P key

/-- A good-root menu digit supplies the only varying scalar in this tariff. -/
def funded (G : Graph n h) (C b m layers : ℕ) : (DescentCommonPalette.rotor G).Site→ℕ
  | ⟨_,.inl false⟩=>layers*m
  | ⟨_,.inl true⟩=>0
  | ⟨v,.inr j⟩=>layers*m*((2+2*h*C)*b+
      DescentRotorPrivateFields.legPrice G C b (name (Physical.host G.arcs 0 0 0 0 0) v j))

omit [Fintype R] in
theorem physical (x : DescentPhysicalSplit.Vertex H) :
    Fintype.card (prg x).Node=funded G C₀ b m P.layers
      ((DescentCommonPalette.rotorSiteEquiv G D P.layers C₀ b u).symm x) := by
  let sites := DescentCommonPalette.rotorSiteEquiv G D P.layers C₀ b u
  obtain ⟨y,rfl⟩ := sites.surjective x
  change Fintype.card (prg (sites y)).Node=funded G C₀ b m P.layers (sites.symm (sites y))
  rw [sites.symm_apply_apply]
  rcases y with ⟨v,(_|_)|j⟩
  · change Fintype.card (Fin P.layers × Fin m)=P.layers*m
    simp
  · change Fintype.card Empty=0
    simp
  · let k := Fin.cast (DescentCommonPalette.rotor_count_eq G D P.layers C₀ b u v) j
    have legName : name H v k=name (bare) v j :=
      DescentCommonPalette.rotor_name_cast G D P.layers C₀ b u v j
    apply Nat.eq_of_mul_eq_mul_right hp
    change Fintype.card (prg ⟨v,.inr k⟩).Node*p=_
    refine ((DescentBatchedRotor.node_count_mul D m p hp contact input site owner align s w G first last P key
      ⟨v,.inr k⟩).trans (DescentCanonicalRotor.tap_nodes D u contact input site owner align s w G first last P key v k)).trans ?_
    have spine : (DescentPhysicalSplit.graph H).width (.inr ⟨v,k.castSucc⟩)=
        P.layers*(u*((2+2*h*C₀)*b)) :=
      (DescentRotorPrivateFields.edge_width G D P.layers C₀ b u (.inr ⟨v,j.castSucc⟩)).trans
        (congrArg (fun price : ℕ => P.layers*(u*price))
          (DescentRotorPrivateFields.spine_price G C₀ b v j.castSucc))
    have leg : localWidth H v k=P.layers*(u*(DescentRotorPrivateFields.legPrice G C₀ b (name (bare) v j))) := by
      change width H (name H v k)=_
      rw [legName]
      cases name (bare) v j <;> rfl
    change (DescentPhysicalSplit.graph H).width (.inr ⟨v,k.castSucc⟩)+localWidth H v k=_
    refine (congrArg₂ (fun a b : ℕ => a + b) spine leg).trans ?_
    simp only [funded]
    ring

end
end Hierarchy.DescentPaidResidentCount.Reset.Rotor

end OAI
