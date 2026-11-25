import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.BorderVNP.CellProfileDepth

/-! # Address and control depths of repeated one-copy tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro.Address (depth)
open private wordIs_fitsAddr from OAI.Computability.BorderVNP.CellProfileDepth

private theorem rowTest_fitsAddr {α : Type} (off : NatExpr) (w : List ℕ) (p : α → Bool)
    (rows : List α) {d : ℕ} (hd : depth off + 2 ≤ d) :
    (rowTest (tableWires off w) p rows).FitsAddr d := by
  apply Term.any_fitsAddr
  intro t ht
  obtain ⟨z, _, hz⟩ := List.mem_filterMap.mp ht
  split at hz <;> simp_all only [Option.some.injEq, reduceCtorEq]
  subst t
  apply wordIs_fitsAddr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  simp [depth]; omega

/-- All reads of a factor's presence test have bounded arithmetic depth. -/
theorem factorPass_fitsAddr (off copy : NatExpr) (f : Factor) {d : ℕ}
    (ho : depth off + 2 ≤ d) (hc : depth copy + 4 ≤ d) : (factorPass off copy f).FitsAddr d := by
  cases f with
  | truth w r => exact rowTest_fitsAddr off w id r ho
  | sign w r => exact rowTest_fitsAddr off w (fun _ => true) r ho
  | gadget w r => exact rowTest_fitsAddr off w (fun _ => true) r ho
  | unary i p =>
    rw [factorPass, Term.equal_fitsAddr]
    simp [Term.FitsAddr, Port.expr, depth]; omega

/-- The sign test has the same wire addressing as the presence test. -/
theorem factorSign_fitsAddr (off : NatExpr) (f : Factor) {d : ℕ} (ho : depth off + 2 ≤ d) :
    (factorSign off f).FitsAddr d := by
  cases f <;> first | exact rowTest_fitsAddr _ _ _ _ ho | trivial

/-- Testing a gadget position requires only two additional address-expression levels. -/
theorem factorSelect_fitsAddr (off : NatExpr) (id : ℕ) (f : Factor) {d : ℕ} (ho : depth off + 2 ≤ d) :
    (factorSelect off id f).FitsAddr d := by
  cases f with
  | gadget w r => exact rowTest_fitsAddr off w (fun a => decide (a = id)) r ho
  | _ => trivial

/-- The range check uses the same address depth as the identifier test. -/
theorem rangeTerm_fitsAddr (limit : ℕ) (off : NatExpr) (f : Factor) {d : ℕ} (ho : depth off + 2 ≤ d) :
    (rangeTerm limit off f).FitsAddr d := by
  cases f <;> first | exact rowTest_fitsAddr _ _ _ _ ho | trivial

private theorem fragment_depth (b : BoxBlock) (start : ℕ) (body : FactorBody) {d h : ℕ}
    (hh : 0 < h)
    (hb : ∀ f j off i, depth j ≤ 3 → depth off ≤ 2 → depth i = 0 →
      (body f j off i).FitsDepth d (h-1)) : (b.fragment start body).FitsDepth d h := by
  refine ⟨hh, Nat.zero_le _, sequence_fitsDepth _ ?_⟩
  intro s hs
  obtain ⟨fj, _, rfl⟩ := List.mem_map.mp hs
  exact hb _ _ _ _ (by simp [depth]) (by simp [depth]) rfl

/-- A public box descriptor adds one loop, its generated offset has depth two, and its
global row index has depth three. Sequences of such blocks require no additional levels. -/
theorem sweep_fitsDepth (body : FactorBody) (blocks : List BoxBlock) (start : ℕ) {d h : ℕ}
    (hh : 0 < h)
    (hb : ∀ f j off i, depth j ≤ 3 → depth off ≤ 2 → depth i = 0 →
      (body f j off i).FitsDepth d (h-1)) : (sweep body blocks start).FitsDepth d h := by
  induction blocks generalizing start with
  | nil => trivial
  | cons b bs ih => exact ⟨fragment_depth b start body hh hb, ih _⟩

/-- The full signed factor sweep fits the fixed generator. -/
theorem factorSweep_fitsDepth (D : Directory) (aux : ℕ) :
    (sweep (factorBody aux) D.blocks 0).FitsDepth 8 3 := by
  apply sweep_fitsDepth _ _ _ (by decide)
  intro f j off i _ hoff hi
  let a := NatExpr.add (.lit aux) off
  have ha : depth a + 2 ≤ 8 := by simp [a, depth]; omega
  exact ⟨Term.guard_fitsDepth _ (factorPass_fitsAddr a i (f.shift aux) ha (by omega)) _,
    Term.emit_fitsDepth _ (factorSign_fitsAddr a (f.shift aux) ha) _ _, trivial⟩

/-- A private range guard consumes just the box loop, independently of table dimensions. -/
theorem Directory.rangeGuard_fitsDepth (D : Directory) : D.rangeGuard.FitsDepth 8 3 := by
  apply sweep_fitsDepth _ _ _ (by decide)
  intro f _ off _ _ hoff _
  exact Term.guard_fitsDepth _ (rangeTerm_fitsAddr _ off f (by omega)) _

/-- Box-copy traversal plus the count-row loop and comparison fit the decoder's three levels. -/
theorem Gadget.steps_fitsDepth (D : Directory) (cap aux id : ℕ) :
    (sweep (stepBody cap aux id) D.blocks 0).FitsDepth 8 3 := by
  apply sweep_fitsDepth _ _ _ (by decide)
  intro f j off i hj hoff _
  apply Prefix.stepGen_fitsDepth _ _ _ _ (by omega) _ (by decide)
  apply factorSelect_fitsAddr
  simp [depth]
  omega

end CellSparse

end BorderVNP
end Computability
end OAI
