import OAI.Computability.BorderVNP.ParseBatchVerifierCountWords
import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction

/-!
# Sparse histogram verification by sorted end markers

Use rows are tagged zero; each label has one end-marker row tagged one, with
a proposed position in the low bits. Padding is tagged by a separate high bit.
A single Batcher sort and local comparisons with hardwired output positions
certify all the proposed ranks simultaneously.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchCounts

open VPVNP.VerifierNetwork ParseBatchVerifier ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

variable {U P : Type*} {a b : ℕ}

/-- Binary use labels followed by one guessed rank word per possible label. -/
abbrev MarkerPins (U : Type*) (a b : ℕ) := (U × Fin a) ⊕ (Fin (2^a) × Fin b)

/-- The numerical label obtained by reading the bits of one occurrence. -/
noncomputable def readLabel (z : MarkerPins U a b → Bool) (u : U) : Fin (2^a) :=
  numberWords a (fun j => z (.inl (u,j)))

private def zeroCode (w : ℕ) : Fin (2^w) := ⟨0, Nat.two_pow_pos _⟩

private noncomputable def prepare (row : Rows U (2^a) P) :
    Fin ((b+1+a)+1) → Expr (MarkerPins U a b) :=
  match row with
  | .inl u => word (.const false) (fun j => .input (.inl (u,j))) (.const false)
      (fun _ => .const false)
  | .inr (.inl i) => word (.const false) (fun j => .const ((numberWords a).symm i j)) (.const true)
      (fun j => .input (.inr (i,j)))
  | .inr (.inr _) => word (.const true) (fun j => .const ((numberWords a).symm (zeroCode a) j))
      (.const false) (fun _ => .const false)

private noncomputable def rowWord (z : MarkerPins U a b → Bool) :
    Rows U (2^a) P → Fin ((b+1+a)+1) → Bool
  | .inl u => word false (fun j => z (.inl (u,j))) false (fun _ => false)
  | .inr (.inl i) => word false ((numberWords a).symm i) true (fun j => z (.inr (i,j)))
  | .inr (.inr _) => word true ((numberWords a).symm (zeroCode a)) false (fun _ => false)

private theorem prepare_eval (row : Rows U (2^a) P) (z : MarkerPins U a b → Bool) :
    (fun j => (prepare row j).eval z) = rowWord z row := by
  rcases row with u | i | p <;> exact word_map (StatementCircuit.Expr.eval z) ..

private theorem word_size {σ : Type*} {a b : ℕ} (p m : Expr σ) (l : Fin a → Expr σ)
    (v : Fin b → Expr σ) (hp : p.size = 1) (hm : m.size = 1) (hl : ∀ i, (l i).size = 1)
    (hv : ∀ i, (v i).size = 1) (j : Fin ((b+1+a)+1)) : (word p l m v j).size = 1 := by
  have he := word_map StatementCircuit.Expr.size p l m v
  have hc : word (1 : ℕ) (fun _ : Fin a => 1) 1 (fun _ : Fin b => 1) = fun _ => 1 := by
    have hz := word_map (fun _ : Unit => (1 : ℕ)) () (fun _ : Fin a => ()) () (fun _ : Fin b => ())
    exact hz.symm
  change (StatementCircuit.Expr.size ∘ word p l m v) j = _
  rw [he, hp, hm, show StatementCircuit.Expr.size ∘ l = fun _ => 1 from funext hl,
    show StatementCircuit.Expr.size ∘ v = fun _ => 1 from funext hv, hc]

private theorem prepare_size (row : Rows U (2^a) P) (j : Fin ((b+1+a)+1)) :
    (prepare row j).size = 1 := by
  rcases row with u | i | p <;> exact word_size _ _ _ _ rfl rfl (fun _ => rfl) (fun _ => rfl) j

private theorem row_key (z : MarkerPins U a b → Bool) (row : Rows U (2^a) P) :
    value (rowWord z row) / 2^b = key (readLabel z) row := by
  rcases row with u | i | p
  · simp [rowWord, word_key, key, readLabel, numberWords]
  · simp [rowWord, word_key, key]
  · simp [rowWord, word_key, key, zeroCode]

private noncomputable def positionCheck (i : Fin (2^b)) : Expr (Pins b ((b+1+a)+1)) :=
  .or (.not (.input (i, tagPin a b))) <| every (fun j : Fin b =>
    let bit : Expr (Pins b ((b+1+a)+1)) := .input (i, positionPin a b j)
    if (numberWords b).symm i j then bit else .not bit)

private theorem positionCheck_eval (i : Fin (2^b)) (z : Pins b ((b+1+a)+1) → Bool) :
    (positionCheck i).eval z = true ↔
      z (i,tagPin a b) = true → value (fun j => z (i,positionPin a b j)) = i.val := by
  have bitCheck (j : Fin b) :
      (if (numberWords b).symm i j then (.input (i,positionPin a b j) : Expr _)
        else .not (.input (i,positionPin a b j))).eval z = true ↔
        z (i,positionPin a b j) = (numberWords b).symm i j := by
    cases (numberWords b).symm i j <;> simp [StatementCircuit.Expr.eval]
  have whole : (∀ j, z (i,positionPin a b j) = (numberWords b).symm i j) ↔
      value (fun j => z (i,positionPin a b j)) = i.val := by
    rw [← value_encode i, (value_injective b).eq_iff, funext_iff]
  cases h : z (i,tagPin a b) <;> simp [positionCheck, StatementCircuit.Expr.eval, every_eval, h, bitCheck, whole]

private theorem positionCheck_size (i : Fin (2^b)) : (positionCheck (a := a) i).size ≤ 3*b+4 := by
  apply Nat.le_trans ?_ (Nat.le_refl _)
  have hs := every_size (fun j : Fin b =>
    let bit : Expr (Pins b ((b+1+a)+1)) := .input (i,positionPin a b j)
    if (numberWords b).symm i j then bit else .not bit) 2 (fun j => by split <;> simp [StatementCircuit.Expr.size])
  dsimp [positionCheck, StatementCircuit.Expr.size] at *
  omega

variable [Fintype U] [Fintype P]

/-- The physical histogram sorting circuit checks all ranks with one sorting network. -/
noncomputable def markerFrame (layout : Fin (2^b) ≃ Rows U (2^a) P) :
    Frame (MarkerPins U a b) Unit :=
  let raw := (Frame.initial id).step (fun ij : Pins b ((b+1+a)+1) => prepare (layout ij.1) ij.2)
  ((phases b le_rfl raw).step positionCheck).step (fun _ => every fun i => .input i)

omit [Fintype P] in
private theorem rowFrame_eval (layout : Fin (2^b) ≃ Rows U (2^a) P) (z : MarkerPins U a b → Bool)
    (i : Fin (2^b)) (j : Fin ((b+1+a)+1)) :
    ((Frame.initial id).step (fun ij : Pins b ((b+1+a)+1) => prepare (layout ij.1) ij.2)).eval z (i,j) =
      rowWord z (layout i) j := by
  have hi : (Frame.initial (id : MarkerPins U a b → MarkerPins U a b)).eval z = z :=
    funext fun v => Frame.initial_eval id z v
  simpa only [Frame.step_eval, hi] using congrFun (prepare_eval (layout i) z) j

/-- The guessed words passing the sorted-row checks are exactly the true marker ranks.
The permutation argument includes every copy of a repeated use row. -/
theorem markerFrame_eval (layout : Fin (2^b) ≃ Rows U (2^a) P) (z : MarkerPins U a b → Bool) :
    (markerFrame layout).eval z () = true ↔
      ∀ i : Fin (2^a), value (fun j => z (.inr (i,j))) = markerRank (readLabel z) i := by
  let f := (Frame.initial id).step (fun ij : Pins b ((b+1+a)+1) => prepare (layout ij.1) ij.2)
  let s := phases b le_rfl f
  obtain ⟨π, hπ⟩ := phases_order f z
  let e := π.trans layout
  have wire (i j) : s.eval z (i,j) = rowWord z (e i) j :=
    (hπ i j).trans (rowFrame_eval layout z (π i) j)
  have hs : Monotone (fun i => key (readLabel z) (e i)) := by
    intro i j hij
    change key (readLabel z) (e i) ≤ key (readLabel z) (e j)
    rw [← row_key z (e i), ← row_key z (e j)]
    apply Nat.div_le_div_right
    have ei : rowWord z (e i) = fun v => s.eval z (i,v) := (funext (wire i)).symm
    have ej : rowWord z (e j) = fun v => s.eval z (j,v) := (funext (wire j)).symm
    rw [ei, ej]
    exact phases_monotone f z hij
  change ((s.step positionCheck).step (fun _ : Unit => every fun i => .input i)).eval z () = true ↔ _
  simp only [Frame.step_eval, every_eval, StatementCircuit.Expr.eval, positionCheck_eval]
  constructor
  · intro h i
    let u := e.symm (.inr (.inl i))
    have hu : e u = .inr (.inl i) := e.apply_symm_apply _
    have step := h u
    simp only [wire, hu, rowWord, word_tag, true_implies, word_position] at step
    exact step.trans (marker_rank_eq (readLabel z) e hs i)
  · intro h i
    rcases hi : e i with u | l | p
    · simp [wire, hi, rowWord]
    · simp only [wire, hi, rowWord, word_tag, true_implies, word_position]
      exact (h l).trans ((marker_rank_eq (readLabel z) e hs l).symm.trans
        (congrArg Fin.val (e.symm_apply_eq.mpr hi.symm)))
    · simp [wire, hi, rowWord]

omit [Fintype P] in
/-- The sole sort and all surrounding scans charge a polynomial in word width
per row. No loop over all parameters is performed for any occurrence. -/
theorem markerFrame_size (layout : Fin (2^b) ≃ Rows U (2^a) P) :
    (markerFrame layout).size ≤ 2^b * ((b+1+a+1) + b^2*(24*(b+1+a+1)+1) + (3*b+4)+2) + 1 := by
  let f := (Frame.initial id).step (fun ij : Pins b ((b+1+a)+1) => prepare (layout ij.1) ij.2)
  have h₁ := Frame.step_size_le (Frame.initial id) (fun ij : Pins b ((b+1+a)+1) => prepare (layout ij.1) ij.2) 1
    (fun ij => (prepare_size _ _).le)
  change f.size ≤ _ at h₁
  simp only [Frame.initial_size, zero_add, Fintype.card_prod, Fintype.card_fin, mul_one] at h₁
  have h₂ := phases_size b le_rfl f
  have h₃ := Frame.step_size_le (phases b le_rfl f) positionCheck (3*b+4) (fun i => positionCheck_size i)
  have h₄ := Frame.step_size_le ((phases b le_rfl f).step positionCheck) (fun _ : Unit => every fun i => .input i)
    (2 * 2^b + 1) (fun _ => every_size _ 1 (fun _ => le_rfl))
  simp only [Fintype.card_fin, Fintype.card_unit, one_mul] at h₃ h₄
  change _ ≤ _ at h₄
  exact h₄.trans (by nlinarith only [h₁,h₂,h₃])

end ParseBatchCounts

end BorderVNP
end Computability
end OAI
