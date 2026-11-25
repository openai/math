import OAI.Computability.BorderVNP.CellGadgetRowsCompact
import OAI.Computability.BorderVNP.CellBoxFactorCompact

/-! # Static description size of the complete sparse cell validator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- One static site-box sweep. Only the one-copy tables and per-block headers enter
this quantity. The private copy multiplicity is stored as a single literal. -/
def Directory.boxMass (D : Directory) : ℕ := sweepMass (fun f => 10000*f.staticMass) D.blocks

/-- One range scan, one scan per reported gadget ID, and their binary count digits. -/
def Directory.gadgetMass (D : Directory) : ℕ :=
  (D.reportedCounts.length+1)*D.boxMass + 1000*(D.reportWidth+D.reportedCounts.length+1)

/-- Static nodes in the complete validator, including private-wire guessing, all
public wiring guards, the signed factor checks, and all reported subtotal checks. -/
theorem Directory.program_mass_le (D : Directory) (p : ℕ) :
    (D.program p).mass ≤ D.recordMass + D.boxMass + D.gadgetMass + 10 := by
  have hf : (sweep (factorBody 0) D.blocks 0).mass ≤ D.boxMass :=
    sweep_mass_le _ _ _ _ (fun _ _ f _ idx off copy _ ho hi => factorBody_mass_le 0 f idx off copy ho hi)
  have hr : D.rangeGuard.mass ≤ D.boxMass :=
    sweep_mass_le _ _ _ _ (fun _ _ f _ _ off _ _ ho _ => rangeBody_mass_le D.reportedCounts.length f off ho)
  have ht := D.subtotalGuards_mass_le D.boxMass (fun id => sweep_mass_le _ _ _ _
    (fun _ _ f _ idx off copy hj ho _ => Gadget.stepBody_mass_le _ _ id f idx off copy hj ho))
  have hp := D.recordGuards_mass_le
  simp only [program,checkAssignment,countGuards,Stmt.mass,NatExpr.mass,gadgetMass]
  rw [Nat.succ_mul D.reportedCounts.length D.boxMass]
  omega

/-- Source-level numeric restrictions on the complete sparse directory. Bounds on
table arities and row counts control generated Boolean temporary addresses. -/
structure Directory.CompactFields (D : Directory) (p M : ℕ) : Prop where
  /-- Number of initial private wire guesses. -/
  privateWires : p ≤ M
  /-- End of the global occurrence index range for the sparse box traversal. -/
  visits : D.visitCount ≤ M
  /-- Numeric data of public zero, equality and profile descriptors. -/
  records : ∀ r ∈ D.records, r.GuardBound M
  /-- Numeric fields on each resolved one-copy box and its local factor tables. -/
  boxes : ∀ b ∈ D.blocks, b.HeaderBound M ∧ ∀ f ∈ b.factors, f.FieldBound M
  /-- Each binary report has at most the stated number of digits and its wire
  addresses are within the supplied numeric scale. -/
  reports : ∀ bits ∈ D.reportedCounts, bits.length ≤ M ∧ ∀ a ∈ bits, a ≤ M

/-- Each literal in the complete generator is polynomially bounded by the physical
directory parameters, including fields introduced by the private flag rectangles. -/
theorem Directory.program_field_le (D : Directory) (p : ℕ) {M : ℕ} (h : D.CompactFields p M) :
    (D.program p).field ≤ 10000*(M+2)^3 := by
  let B := 10000*(M+2)^3
  have hM : M ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (M^2),Nat.zero_le (M^3)]
  have hbox := fun b hb => (h.boxes b hb).1
  have visit : 0+(D.blocks.map fun b => b.copies*b.factors.length).sum ≤ M := by simpa only [Nat.zero_add,Directory.visitCount] using h.visits
  have hf := sweep_field_le D.blocks (factorBody 0) 0 hM visit hbox
    (fun b hb f hf idx off copy _ ho hi => factorBody_field_le 0 f idx off copy ((h.boxes b hb).2 _ hf)
      (Nat.zero_le _) ho hi)
  have hr : D.rangeGuard.field ≤ B := sweep_field_le _ _ _ hM visit hbox
    (fun b hb f hf _ off _ _ ho _ => rangeBody_field_le D.reportedCounts.length f off ((h.boxes b hb).2 _ hf) ho)
  have ht := D.subtotalGuards_field_le h.visits h.reports (fun id => sweep_field_le _ _ _ hM visit hbox
    (fun b hb f hf idx off copy hj ho _ => Gadget.stepBody_field_le _ _ id f idx off copy ((h.boxes b hb).2 _ hf)
      h.visits (by gcongr; exact h.visits) hj ho))
  have hrec := D.recordGuards_field_le h.records
  have hsmall : 100*(M+2)^3+1 ≤ B := by
    dsimp [B]; nlinarith [Nat.zero_le (M^2), Nat.zero_le (M^3)]
  exact max_le (max_le (h.privateWires.trans hM) (Nat.zero_le _))
    (max_le (hrec.trans hsmall) (max_le hf (max_le hr ht)))

end CellSparse

end BorderVNP
end Computability
end OAI
