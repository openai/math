import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellCompactFields

/-! # Static syntax of a repeated-box sweep

Each factor contributes its one-copy syntax exactly once per block. Copy multiplicities
affect the size of an address literal, never the number of stored instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Total mass for one sweep with a static node budget for each local factor. -/
def sweepMass (w : Factor → ℕ) (bs : List BoxBlock) : ℕ :=
  (bs.map fun b => 4 + b.factors.length + (b.factors.map w).sum).sum + 1

private theorem sum_map_mono {α : Type} (xs : List α) (f g : α → ℕ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (.tail _ hy))

private theorem fragment_mass (w : Factor → ℕ) (b : BoxBlock) (body : FactorBody) (start : ℕ)
    (h : ∀ f ∈ b.factors, ∀ j off copy, j.mass ≤ 7 → off.mass ≤ 5 → copy.mass ≤ 1 →
      (body f j off copy).mass ≤ w f) :
    (b.fragment start body).mass ≤ 3 + b.factors.length + (b.factors.map w).sum := by
  let emit (z : Factor × ℕ) := body z.1
    (.add (.add (.lit start) (.mul (.index 0) (.lit b.factors.length))) (.lit z.2))
    (.add (.lit b.base) (.mul (.index 0) (.lit b.stride))) (.index 0)
  have hh := sum_map_mono b.factors.zipIdx (Stmt.mass ∘ emit) (w ∘ Prod.fst)
    (fun z hz => h z.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hz)) _ _ _ le_rfl le_rfl le_rfl)
  have eq : b.factors.zipIdx.map (w ∘ Prod.fst) = b.factors.map w := by
    rw [← List.map_map, List.zipIdx_map_fst]
  rw [eq] at hh
  change 2+(sequence (b.factors.zipIdx.map emit)).mass ≤ _
  rw [mass_sequence,List.length_map,List.length_zipIdx,List.map_map]
  omega

/-- A static copy of each factor body, its row delimiter, and one loop header per block. -/
theorem sweep_mass_le (w : Factor → ℕ) (bs : List BoxBlock) (body : FactorBody) (start : ℕ)
    (h : ∀ b ∈ bs, ∀ f ∈ b.factors, ∀ j off copy,
      j.mass ≤ 7 → off.mass ≤ 5 → copy.mass ≤ 1 → (body f j off copy).mass ≤ w f) :
    (sweep body bs start).mass ≤ sweepMass w bs := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    have hb := fragment_mass w b body start (h b List.mem_cons_self)
    have ht := ih (start + b.copies*b.factors.length) (fun y hy => h y (.tail _ hy))
    simp only [sweep,Stmt.mass,sweepMass,List.map_cons,List.sum_cons] at ht ⊢
    omega

/-- Numeric literals introduced by the box header and the starting row number, before
any local factor-specific checks. -/
def BoxBlock.HeaderBound (b : BoxBlock) (M : ℕ) : Prop :=
  b.base ≤ M ∧ b.stride ≤ M ∧ b.copies ≤ M ∧ b.factors.length ≤ M

private theorem fragment_field (b : BoxBlock) (body : FactorBody) (start : ℕ) {M B : ℕ}
    (hb : b.HeaderBound M) (hs : start ≤ M) (hM : M ≤ B)
    (h : ∀ f ∈ b.factors, ∀ j off copy, j.field ≤ M → off.field ≤ M → copy.field ≤ M →
      (body f j off copy).field ≤ B) : (b.fragment start body).field ≤ B := by
  obtain ⟨hbase,hstride,hcopies,hlen⟩ := hb
  apply max_le (hcopies.trans hM) (field_sequence_le _ ?_)
  intro t ht
  obtain ⟨⟨f,i⟩,hi,rfl⟩ := List.mem_map.mp ht
  have hget := List.mem_zipIdx_iff_getElem?.mp hi
  have hix := (List.getElem?_eq_some_iff.mp hget).1
  apply h f (List.mem_of_getElem? hget) _ _ _ <;> simp only [NatExpr.field,max_le_iff] <;> omega

/-- All derived start indices are bounded by the last global occurrence number, while
the lexical index and per-block offsets use only the public header fields. -/
theorem sweep_field_le (bs : List BoxBlock) (body : FactorBody) (start : ℕ) {M B : ℕ}
    (hM : M ≤ B) (hs : start + (bs.map fun b => b.copies*b.factors.length).sum ≤ M)
    (hb : ∀ b ∈ bs, b.HeaderBound M)
    (h : ∀ b ∈ bs, ∀ f ∈ b.factors, ∀ j off copy,
      j.field ≤ M → off.field ≤ M → copy.field ≤ M → (body f j off copy).field ≤ B) :
    (sweep body bs start).field ≤ B := by
  induction bs generalizing start with
  | nil => exact Nat.zero_le _
  | cons b bs ih =>
    simp only [List.map_cons,List.sum_cons] at hs
    apply max_le (fragment_field _ _ _ (hb _ List.mem_cons_self) (by omega) hM (h _ List.mem_cons_self))
    exact ih _ (by omega) (fun x hx => hb x (.tail _ hx)) (fun x hx => h x (.tail _ hx))

end CellSparse

end BorderVNP
end Computability
end OAI
