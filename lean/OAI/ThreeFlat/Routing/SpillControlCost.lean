import OAI.ThreeFlat.Routing.SpillControlNetwork
import OAI.ThreeFlat.Concentrator.TwoPassBank
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace OAI
/-! # Linear cost per round of spill control -/

open scoped BigOperators Classical
noncomputable section
namespace ThreeFlat.Routing.Spill
open Concentrator

universe u
variable {E R V : Type u} {F : Type*} [Fintype E] [LinearOrder E] [Fintype R] [LinearOrder R]
  [Fintype V] [DecidableEq V] [Zero F] [One F]

/-- A common per-input, per-round charge for the four public checks. -/
def controlCharge (D : ℕ) : ℕ :=
  2^(D*D+1)*(D*D+3) +
    3*(2^(max (D+1) 4)*(max (D+1) 4+2)) +
    (2*D)*(2^(5+D)*(5+D+2)) + 2^(3+D)*(3+D+2)

omit [Fintype R] in
theorem controlNetwork_cells (N : E → Finset R) (G : ReserveGraph E V)
    (slots cap D : ℕ) (left : ∀ e, (N e).card ≤ D)
    (right : ∀ r, Fintype.card (Contenders N r) ≤ D)
    (degree : ∀ v, Fintype.card (Adjacent G v) ≤ D)
    (hV : Fintype.card V ≤ 2*Fintype.card E) (hs : slots ≤ D) :
    (controlNetwork (F := F) N G slots cap).cells ≤ Fintype.card E * (cap+1) * controlCharge D := by
  let k := Fintype.card E
  let g := 2^(D*D+1)*(D*D+3)
  let t := 2^(max (D+1) 4)*(max (D+1) 4+2)
  let s := 2^(5+D)*(5+D+2)
  let a := 2^(3+D)*(3+D+2)
  have hk : k ≤ k*(cap+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hg : (greedyCheck (F := F) N).cells ≤ k*(cap+1)*g :=
    (by simpa [greedyCheck,greedyNetwork,LocalChecks.exposed_cells,k,g] using
      (greedyNetwork_cells (F := F) N D right left) : (greedyCheck (F := F) N).cells ≤ k*g).trans
      (Nat.mul_le_mul_right _ hk)
  have ht0 : (reserveCheck (F := F) G slots cap).cells ≤ (Fintype.card V*cap+k*cap)*t := by
    simpa [reserveCheck,reserveNetwork,LocalChecks.exposed_cells,k,t] using
      reserveNetwork_cells (F := F) G slots cap D degree
  have ht : (reserveCheck (F := F) G slots cap).cells ≤ k*(cap+1)*(3*t) := by
    calc
      _ ≤ (Fintype.card V*cap+k*cap)*t := ht0
      _ ≤ ((2*k)*(cap+1)+k*(cap+1))*t := by
        change Fintype.card V ≤ 2*k at hV
        gcongr <;> omega
      _ = _ := by ring
  have hs0 := reserveSelectNetwork_cells (F := F) G slots cap D degree
  have hs' : (reserveSelectNetwork (F := F) G slots cap).cells ≤ k*(cap+1)*((2*D)*s) := by
    calc
      _ ≤ k*(2*slots)*(cap+1)*s := by simpa [k,s,ReserveChoice,Fintype.card_prod] using hs0
      _ ≤ k*(2*D)*(cap+1)*s := by gcongr
      _ = _ := by ring
  have ha (e : E) : (controlModules (F := F) N G slots cap (.inr e)).cells ≤ a := by
    simp only [controlModules, TypedWiring.localTable, TableCompiler.localTableNetwork_cells]
    change 2^Fintype.card (AuditBits N e) * (Fintype.card (AuditBits N e)+2) ≤ a
    have hb : Fintype.card (AuditBits N e) ≤ 3+D := by simpa [AuditBits] using Nat.add_le_add_left (left e) 3
    dsimp only [a]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hb) (Nat.add_le_add_right hb 2)
  have ha' : (∑ e : E, (controlModules (F := F) N G slots cap (.inr e)).cells) ≤ k*(cap+1)*a := by
    calc
      _ ≤ ∑ _ : E, a := Finset.sum_le_sum (fun e _ => ha e)
      _ = k*a := by simp [k]
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  rw [controlNetwork, TypedWiring.glue_cells, Fintype.sum_sum_type, Fin.sum_univ_three]
  change (greedyCheck (F := F) N).cells + (reserveCheck (F := F) G slots cap).cells +
    (reserveSelectNetwork (F := F) G slots cap).cells + _ ≤ _
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hg ht) hs') ha').trans_eq (by
    change _ = k*(cap+1)*(g + 3*t + (2*D)*s + a)
    ring)

/-- The publicly chosen two-pass bank takes at most a logarithmic number of
rounds, and its full selector therefore costs `O(CR log(CR))` cells. -/
theorem twoPassBank_control_cells {C q D R : ℕ} (B : TwoPassBank C q D R) :
    (controlNetwork (F := F) (fun e => (B.N e).toFinset) B.G B.slots
      (Nat.log 2 (C*R)+1)).cells ≤ (C*R) * (Nat.log 2 (C*R)+2) * controlCharge D := by
  let N := fun e => (B.N e).toFinset
  have left (e) : (N e).card ≤ D := (B.N e).toFinset_card_le.trans (B.primaryDegree e)
  have right (r) : Fintype.card (Contenders N r) ≤ D := by
    simpa [Contenders,N,Fintype.card_subtype] using B.reverseDegree r
  have degree (v) : Fintype.card (Adjacent B.G v) ≤ D := by
    simpa [Adjacent,ReserveGraph.incident,Fintype.card_subtype] using B.incidentDegree v
  have h := controlNetwork_cells (F := F) N B.G B.slots (Nat.log 2 (C*R)+1) D left right degree
    (by simpa using B.reserveBound) B.slotBound
  simpa only [Fintype.card_fin] using h

end ThreeFlat.Routing.Spill

end
end OAI
