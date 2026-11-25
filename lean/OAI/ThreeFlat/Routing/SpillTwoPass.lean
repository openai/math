import OAI.ThreeFlat.Routing.SpillBoardCheck
import OAI.ThreeFlat.Routing.SpillBankSemantics
import OAI.ThreeFlat.Routing.SpillBankStage

namespace OAI
/-! # Deterministic sparse compaction through the two-pass public banks -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill
open Concentrator

variable {C q D R : ℕ} (B : TwoPassBank C q D R) {F : Type*} [CommSemiring F]

def bankCap (C R : ℕ) := Nat.log 2 (C*R) + 1

def bankSelect (mask : Fin (C*R) → Bool) : Option (Candidate (fullBoard B) → Bool) :=
  let A := Finset.univ.filter (fun e => mask e = true)
  if Fits B A (bankCap C R) then some (fullPlan B A (bankCap C R)) else none

theorem bankCheck_function (mask : Fin (C*R) → Bool) (c : Candidate (fullBoard B) → Bool) :
    TypedWiring.value (boardCheck (F := F) B (bankCap C R)) (Sum.elim mask c) =
      if bankSelect B mask = some c then 1 else 0 := by
  let A := Finset.univ.filter (fun e => mask e = true)
  have hx : mask = (fun e => decide (e ∈ A)) := by funext e; simp [A]
  calc
    TypedWiring.value (boardCheck (F := F) B (bankCap C R)) (Sum.elim mask c) =
        (if Fits B A (bankCap C R) ∧ c = fullPlan B A (bankCap C R) then (1:F) else 0) := by
      exact (congrArg (fun input => TypedWiring.value (boardCheck (F := F) B (bankCap C R))
        (Sum.elim input c)) hx).trans (boardCheck_eval B (bankCap C R) A c)
    _ = _ := by
      change (if Fits B A _ ∧ c = fullPlan B A _ then (1 : F) else 0) =
        if (if Fits B A _ then some (fullPlan B A _) else none) = some c then 1 else 0
      by_cases h : Fits B A (bankCap C R) <;> simp [h,eq_comm]

def twoPassStage (w : ℕ) : Stage F (SlotBits (Fin (C*R)) w) (SlotBits (Fin R) w) :=
  packingStage (fullBoard B) w (boardCheck B (bankCap C R)) (bankSelect B) (bankCheck_function B)

theorem twoPassStage_complete (w : ℕ) (x : SlotBits (Fin (C*R)) w → Bool)
    (legal : q*(occupied x).card + R ≤ q*R) : ∃ y, (twoPassStage (F := F) B w).run x = some y := by
  have hd : Fits B (occupied x) (bankCap C R) :=
    bank_live_empty_of_legal B (occupied x) (primaryPlan B _) (primaryPlan_valid B _) legal
  change ∃ _, (bankSelect B (fun i => x (i,none))).map _ = _
  change ∃ _, (if Fits B (occupied x) _ then some (fullPlan B (occupied x) _) else none).map _ = _
  rw [ite_eq_left hd]
  exact ⟨_,rfl⟩

theorem twoPassStage_preserves (w : ℕ) (x : SlotBits (Fin (C*R)) w → Bool)
    (y : SlotBits (Fin R) w → Bool) (hy : (twoPassStage (F := F) B w).run x = some y) :
    payloads y = payloads x := by
  let A := occupied x
  let cap := bankCap C R
  change (if Fits B A cap then some (fullPlan B A cap) else none).map _ = some y at hy
  by_cases hd : Fits B A cap
  · rw [ite_eq_left hd,Option.map_some,Option.some.injEq] at hy
    obtain ⟨f,adj,hf⟩ := boardPick_eq_injectionPins B A cap (primaryPlan B A) (primaryPlan_valid B A) hd
    change fullPlan B A cap = _ at hf
    rw [hf] at hy
    rw [← hy]
    exact payloads_packed (fullBoard B) x f adj
  · simp [hd] at hy

end ThreeFlat.Routing.Spill

end
end OAI
