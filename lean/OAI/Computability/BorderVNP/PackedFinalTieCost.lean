import OAI.Computability.BorderVNP.PackedFinalTieTerminal
import OAI.Computability.BorderVNP.PackedFrozenLayerCost

/-! # Sparse cost of the final physical binding tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity CellAddressCircuit PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open FrozenTape
open private view_cubic prefix_size from OAI.Computability.BorderVNP.PackedFrozenLayerCost

variable {s m np C d k w R W : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m np C d k w σ)

private theorem sitePrefixes_size :
    (sitePrefixes F).size ≤ lookupCost s (m+m+np) d w := by
  let payload := fun (v : Fin s) (j : Fin w) =>
    (BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.input
      (.inr (.inr (.inl (.inr (.inl v),j)))) : Expr (Front σ s m np C w))
  let request := fun (u : End m np) (j : Fin d) =>
    (BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.input
      (.inl (F.ptr u j)) : Expr (Front σ s m np C w))
  have h := queries_size (layout (Fin s) (End m np)) (fun i => fixed (σ := Front σ s m np C w) (F.sites i))
    payload request 1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [sitePrefixes,PackedLookup.lookup,lookupCost,End,Fintype.card_sum,Fintype.card_fin,Nat.mul_one,
    payload,request] using h

private theorem keyBudget (rows : 1+CellAddressCircuit.count s m np C+CellAddressCircuit.count s m np s ≤ R)
    (index : Nat.clog 2 R ≤ W) {u v : ℕ} (hu : u ≤ W) (hv : v ≤ W) :
    lookupCost s (m+m+np) u v ≤ 1000*R*(W+1)^3 := by
  have h : s+(m+m+np)+1 ≤ R := by unfold CellAddressCircuit.count at rows; omega
  apply (lookupCost_cubic _ _ _ _ W ((Nat.clog_mono_right 2 (by omega : s+(m+m+np) ≤ R)).trans index) hu hv).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1000 h)

/-- Both allocation scans, the two batched site reads and all physical endpoint selectors
fit a cubic word bound per sparse row. No individual cable lanes are enumerated. -/
theorem inputs_cubic (work : Fin s → Fin w → σ) (occupied : Fin m → σ) (ports : Fin np → Bool)
    (rows : 1+CellAddressCircuit.count s m np C+CellAddressCircuit.count s m np s ≤ R)
    (widths : d ≤ W ∧ k ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    (inputs F work occupied ports).size ≤ 9000*R*(W+1)^3 := by
  obtain ⟨hd,hk,hw,hl⟩ := widths
  have ha := view_cubic F (by omega : 1+CellAddressCircuit.count s m np s ≤ R) ⟨hd,hw,hl⟩
  have hb := LayerRows.cellView_cubic F (by omega : 1+CellAddressCircuit.count s m np C ≤ R) ⟨hd,hk,hw,hl⟩
  have hc := (prefix_size F work).trans (keyBudget rows hl hd hw)
  have he := (sitePrefixes_size F).trans (keyBudget rows hl hd hw)
  have n : 2*m+np ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have per : (1+d+6*w)*(30*d+8) ≤ 500*(W+1)^3 := by
    calc _ ≤ (1+W+6*W)*(30*W+8) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have cost := Nat.mul_le_mul n per
  rw [show R*(500*(W+1)^3) = 500*(R*(W+1)^3) by ring] at cost
  have h := inputs_size F work occupied ports
  rw [Nat.mul_assoc (2*m+np)] at h
  simp only [Nat.mul_assoc 3200 R,Nat.mul_assoc 1000 R,Nat.mul_assoc 9000 R] at *
  omega

variable {shape : Shape} (F' : Fields shape.sites shape.edges np C d k w σ)
variable (occupied : Fin shape.edges → σ) (ports : Fin np → Bool)
local notation3 "S" => shape.sites
local notation3 "M" => shape.edges

/-- The full terminal encoder and optional translation to ordinal site keys fit the same
sparse rectangle times a cubic polynomial in word width and sorting depth. -/
theorem terminal_budget_cubic
    (rows : 1+CellAddressCircuit.count S M np C+CellAddressCircuit.count S M np S ≤ R)
    (widths : d ≤ W ∧ k ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    (Views.frame F').size + 1 + S*3*(100*(w+1)^2) +
      ((inputs (retained F') recoveredPins (Sum.inl ∘ occupied) ports).size + 1 + (2*M+np)*(4500*(w+1)^2)) +
      lookupCost S (Fintype.card (Row M np)) d d ≤ 18500*R*(W+1)^3 := by
  obtain ⟨hd,hk,hw,hl⟩ := widths
  have source := inputs_cubic (retained F') recoveredPins (Sum.inl ∘ occupied) ports rows ⟨hd,hk,hw,hl⟩
  have view := view_cubic F' (by omega : 1+CellAddressCircuit.count S M np S ≤ R) ⟨hd,hw,hl⟩
  have lookup := keyBudget rows hl hd hd
  have card : Fintype.card (Row M np) = M+M+np := by
    simp only [Row,Subdivision.Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
    omega
  rw [card]
  have site : S ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have edge : 2*M+np ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have scale : (w+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2 ≤ 3))
  have recovery := Nat.mul_le_mul site scale
  have ties := Nat.mul_le_mul edge scale
  have one : 0 < R*(W+1)^3 := Nat.mul_pos (by omega) (by positivity)
  simp only [Nat.mul_assoc 9000 R,Nat.mul_assoc 3200 R,Nat.mul_assoc 1000 R,Nat.mul_assoc 18500 R] at *
  rw [show S*3*(100*(w+1)^2) = 300*(S*(w+1)^2) by ring,
    show (2*M+np)*(4500*(w+1)^2) = 4500*((2*M+np)*(w+1)^2) by ring]
  omega

/-- Gate count of the actual source-key terminal tape. -/
theorem terminalTape_cubic
    (rows : 1+CellAddressCircuit.count S M np C+CellAddressCircuit.count S M np S ≤ R)
    (widths : d ≤ W ∧ k ≤ W ∧ w ≤ W ∧ Nat.clog 2 R ≤ W) :
    (terminalTape F' occupied ports).size ≤ 18500*R*(W+1)^3 :=
  (terminalTape_size F' occupied ports).trans ((Nat.le_add_right _ _).trans (terminal_budget_cubic F' occupied ports rows widths))

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
