import OAI.Computability.BorderVNP.CellGadgetFinishCompact
import OAI.Computability.BorderVNP.CellDirectoryRecords
import OAI.Computability.BorderVNP.CellSparseCompiled
import OAI.Computability.BorderVNP.CellSweepCompact

/-! # Static descriptor costs for the reported subtotals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

namespace Gadget

/-- The one-hot rectangle and its copy loops remain symbolic; a subtotal row has one
static box scan plus a linear number of nodes in the binary output width. -/
theorem row_mass_le (D : Directory) (id : ℕ) (bits : List ℕ) {S : ℕ}
    (h : (sweep (stepBody D.visitCount ((D.visitCount+1)^2) id) D.blocks 0).mass ≤ S) :
    (row D id bits).mass ≤ S + 999*(bits.length+1) := by
  rw [row,mass_localFlags]
  have hi := Prefix.initGen_mass_le 0 D.visitCount
  have hf := finishCount_mass_le 0 ((D.visitCount+1)^2) D.visitCount bits
  simp only [checker,Stmt.mass,← pow_two]
  omega

private theorem init_field {cap B : ℕ} (hc : cap+1 ≤ B) (hB : 2 ≤ B) :
    (Prefix.initGen 0 cap).field ≤ B := by
  let t := Prefix.flagTerm 0 cap (.lit 0) (.index 0)
  have h : t.Fields B := by simp [t,Prefix.flagTerm,Term.Fields,NatExpr.field,hc]
  change max (cap+1) (max (max 0 0) (max t.guard.field t.not.guard.field)) ≤ B
  apply max_le hc (max_le (by simp) ?_)
  exact max_le (Term.guard_field_le _ h (by change 1 ≤ B; omega)) (Term.guard_field_le _ h hB)

/-- Field widths for a single subtotal scan, including the quadratic flag offset. -/
theorem row_field_le (D : Directory) (id : ℕ) (bits : List ℕ) {M : ℕ}
    (hc : D.visitCount ≤ M) (hb : bits.length ≤ M) (ha : ∀ a ∈ bits, a ≤ M)
    (hscan : (sweep (stepBody D.visitCount ((D.visitCount+1)^2) id) D.blocks 0).field ≤ 10000*(M+2)^3) :
    (row D id bits).field ≤ 10000*(M+2)^3 := by
  let B := 10000*(M+2)^3
  have hdim : 16*M+20+(M+1)^2 ≤ B := by
    dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have haux : (D.visitCount+1)^2 ≤ (M+1)^2 := by gcongr
  rw [row,field_localFlags]
  simp only [checker,Stmt.field,← pow_two]
  apply max_le (haux.trans (by omega)) (max_le (init_field (by omega) (by omega)) (max_le hscan ?_))
  exact finishCount_field_le 0 _ _ _ (Nat.zero_le _) (by omega) (fun a h => by have := ha a h; omega) (by omega)

end Gadget

/-- Total number of digits explicitly named in all binary gadget reports. -/
def Directory.reportWidth (D : Directory) : ℕ := (D.reportedCounts.map List.length).sum

private theorem sum_zip_le {α : Type} (xs : List α) (f : α × ℕ → ℕ) (w : α → ℕ)
    (S : ℕ) (h : ∀ z ∈ xs.zipIdx, f z ≤ S + 999*(w z.1+1)) :
    (xs.zipIdx.map f).sum ≤ xs.length*S + 999*((xs.map w).sum + xs.length) := by
  have hh (ys : List (α × ℕ)) (hf : ∀ z ∈ ys, f z ≤ S+999*(w z.1+1)) :
      (ys.map f).sum ≤ ys.length*S + 999*((ys.map (w ∘ Prod.fst)).sum + ys.length) := by
    induction ys with
    | nil => simp
    | cons y ys ih =>
      have h₁ := hf y List.mem_cons_self
      have h₂ := ih (fun z hz => hf z (.tail _ hz))
      simp only [List.map_cons,List.sum_cons,Function.comp_apply,List.length_cons]
      rw [Nat.succ_mul ys.length S]
      omega
  have eq : xs.zipIdx.map (w ∘ Prod.fst) = xs.map w := by rw [← List.map_map,List.zipIdx_map_fst]
  simpa only [List.length_zipIdx,eq] using hh _ h

/-- Each ID incurs one static scan; the final comparisons also account for the
sum of the named report widths, without padding them to the maximum width. -/
theorem Directory.subtotalGuards_mass_le (D : Directory) (S : ℕ)
    (h : ∀ id, (sweep (Gadget.stepBody D.visitCount ((D.visitCount+1)^2) id) D.blocks 0).mass ≤ S) :
    D.subtotalGuards.mass ≤ D.reportedCounts.length*S + 1000*(D.reportWidth + D.reportedCounts.length+1) := by
  rw [subtotalGuards,mass_sequence,List.length_map,List.length_zipIdx,List.map_map]
  have bound := sum_zip_le D.reportedCounts (fun z => (Gadget.row D z.2 z.1).mass) List.length S
    (fun z _ => Gadget.row_mass_le D z.2 z.1 (h z.2))
  change _ ≤ _ + 1000*((D.reportedCounts.map List.length).sum + D.reportedCounts.length+1)
  exact (Nat.add_le_add_right (Nat.add_le_add_left bound _) _).trans (by omega)

/-- All report rows use the same numeric scale as their one-copy factor scans. -/
theorem Directory.subtotalGuards_field_le (D : Directory) {M : ℕ} (hc : D.visitCount ≤ M)
    (hb : ∀ bits ∈ D.reportedCounts, bits.length ≤ M ∧ ∀ a ∈ bits, a ≤ M)
    (hscan : ∀ id, (sweep (Gadget.stepBody D.visitCount ((D.visitCount+1)^2) id) D.blocks 0).field ≤
      10000*(M+2)^3) : D.subtotalGuards.field ≤ 10000*(M+2)^3 := by
  apply field_sequence_le
  intro t ht
  obtain ⟨⟨bits,id⟩,hi,rfl⟩ := List.mem_map.mp ht
  obtain ⟨hl,ha⟩ := hb bits (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hi))
  exact Gadget.row_field_le _ _ _ hc hl ha (hscan id)

end CellSparse

end BorderVNP
end Computability
end OAI
