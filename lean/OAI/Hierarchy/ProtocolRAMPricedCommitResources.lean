import OAI.Hierarchy.ProtocolRAMCalendarBill
import OAI.Hierarchy.ProtocolRAMReportedChargeKeys
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Resource bounds for the signed stock commit from its actual operands -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open ProbeStage ProbeStage.Native RepairHistogram PurchaseStage CatalogueRows

def stockTimeCap (R U : ℕ) :=
  let K := 100*(U+1)
  4+3*(4+R*(2*K+4))+(35+R*(4*K+20)+R*(8*U+242))

def pricedTimeCap (R U : ℕ) := 4+R*(2*U+4)+(4+18*R+stockTimeCap R U)
def pricedTextCap (U : ℕ) := 10000*(U+1)

/-- Candidate, occurrence and commodity counts share a linear factor. The
instruction bounds are on the slot and two signed transfer expressions, the
broadcast, the label lookup, and the scalar mode. -/
theorem priced_resources {q d : ℕ} (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d)
    (w h R U : ℕ) (rows : a.rows≤2^h*R) (occ : a.occurrences≤2^h*R) (goods : a.goods≤2^h*R)
    (slot : s.slot.work≤U) (credit : s.credit.work≤U) (debit : s.charge.work≤U)
    (mode : s.mode.work≤U) (message : (broadcastTerm b s.price).work≤U)
    (label : ((g.geometry 5).atRow g.edge).work≤U) :
    (pricedSegment a s g w b).ticks ≤ pricedTimeCap R U*2^h ∧
      text (pricedSegment a s g w b).native ≤ pricedTextCap U := by
  let x := fresh a s
  let K := 100*(U+1)
  have dest : x.columns.destination.work≤2*U+5 := by
    change 1+(s.slot.work+1+s.slot.work+1+1)+1≤_;omega
  have pairBound : (pair x.columns).work≤K := by
    let j := Expr.lookup x.columns.occurrence .row
    have h₁ := (substitute_work x.columns.destination j).trans (Nat.mul_le_mul_right 8 dest)
    have h₂ := (substitute_work x.columns.credit j).trans (Nat.mul_le_mul_right 8 credit)
    have h₃ := (substitute_work x.columns.charge j).trans (Nat.mul_le_mul_right 8 debit)
    change 7+1+(x.columns.destination.atRow j).work+
      ((x.columns.credit.atRow j).work+(x.columns.charge.atRow j).work+1)+1≤_
    dsimp only [K];omega
  have directCredit : (ordinaryTerm x.columns x.plan x.goods x.columns.credit).work≤K := by
    change x.columns.destination.work+1+s.credit.work+1+1≤_;dsimp only [K];omega
  have directDebit : (ordinaryTerm x.columns x.plan x.goods x.columns.charge).work≤K := by
    change x.columns.destination.work+1+s.charge.work+1+1≤_;dsimp only [K];omega
  have cast : (broadcastTerm b x.price).work≤K := message.trans (by dsimp only [K];omega)
  have cheap (p) (hp : p ∈ x.charges b a.rows) : p.term.work ≤ K ∧ p.rows≤2^h*R := by
    simp only [StockCommit.charges,directColumns,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨directCredit,occ⟩
    · exact ⟨directDebit,occ⟩
    · exact ⟨cast,rows⟩
  let unitCost := 4+R*(2*K+4)
  have sum : ((x.charges b a.rows).map (passFactor R)).sum≤3*unitCost := by
    have unit (e : Expr) (small : e.work≤K) : 4+R*(2*e.work+4) ≤ unitCost :=
      Nat.add_le_add_left (Nat.mul_le_mul_left R (Nat.add_le_add_right
        (Nat.mul_le_mul_left 2 small) 4)) 4
    have c := unit _ directCredit
    have d' := unit _ directDebit
    have e := unit _ cast
    simp only [StockCommit.charges,directColumns,List.cons_append,List.nil_append,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,passFactor]
    omega
  have coef : stockFactor x a.rows R b ≤ stockTimeCap R U := by
    apply Nat.add_le_add (Nat.add_le_add_left sum 4)
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left R (Nat.add_le_add_right
      (Nat.mul_le_mul_left 4 pairBound) 20)) 35) (Nat.mul_le_mul_left R
      (Nat.add_le_add_right (Nat.mul_le_mul_left 8 mode) 242))
  have stock := (stock_bill x w a.rows (2^h) R b (Nat.two_pow_pos _) occ goods
    (fun p hp => (cheap p hp).2)).trans (Nat.mul_le_mul_left _ coef)
  constructor
  · rw [pricedTicks]
    have fee := Nat.mul_le_mul occ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 label) 4)
    have seed := Nat.mul_le_mul_left 18 goods
    have four : 4 ≤ 2^h*4 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    change 4+_+(4+_+(x.native w a.rows b).ticks) ≤ _
    unfold pricedTimeCap
    nlinarith only [fee,seed,stock,four]
  · have paid := pricedSize a s g w b
    have copied := freshSegment_size a s w b
    have size : text (pricedSegment a s g w b).native =
        rowText ((g.geometry 5).atRow g.edge)+39+commitText x a.rows b := by
      rw [←text_stock x w]
      simp only [text,paid.1,paid.2.1,paid.2.2,copied.1,copied.2.1,copied.2.2,rowText]
      dsimp only [x]
      omega
    rw [size]
    have modex : x.plan.mode.work ≤ U := mode
    simp only [commitText,StockCommit.charges,directColumns,listText,StockAccounts.columns,
      StockAccounts.clipped,StockAccounts.overflow,transfers,retainedTerm,reserveTerm,excessTerm,
      List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      rowText,Expr.work,pricedTextCap] at ⊢
    dsimp only [K] at directCredit directDebit pairBound cast
    omega


end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
