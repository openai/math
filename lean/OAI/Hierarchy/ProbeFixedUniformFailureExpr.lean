import OAI.Hierarchy.ProbeFixedRowPages
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost

namespace OAI
/-! # Uniform instruction work of the two installed failure scans -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripDirectory PurchaseFrozen
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def coordinateWork := 4+30*(publicStages v.W*(2*k))
def quoteWork := 2*v.coordinateWork+16
def quoteCount := max (Fintype.card (PayloadStrip.Quotes (publicStages v.W) k))
  (Fintype.card (ChainStrip.Axes v.depth k))

/-- The radix and both numbers of quote digits are fixed by the public format. -/
def failureExprWork := (v.quoteWork+4)*(v.digitRadix+2)^v.quoteCount+24

theorem quote_work {d : ℕ} (price offsets stocks : Bank) (addr : Fin d → Expr) (i : Fin d) :
    (quoted price offsets stocks addr i).work = 2*(addr i).work+16 := by
  simp only [quoted,AttemptGate.valueTerm,Expr.atRow,Expr.work]; omega

private theorem failure_work {n : ℕ} (s : StripTest n) (arity : n≤v.quoteCount)
    (radix : s.radix=v.digitRadix) (live : s.live.work≤10) (small : ∀i,(s.quoted i).work≤v.quoteWork) :
    s.failure.test.work≤v.failureExprWork := by
  have digits := menuKey_work s.radix v.quoteWork (List.ofFn s.quoted) (fun x hx=>by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact small j)
  have shape : s.failure.test.work = s.live.work+(menuKey s.radix (List.ofFn s.quoted)).work+12 := by
    simp only [StripTest.failure,FailureWords.test,FailureWords.effective,menuLookup,Expr.work]; omega
  have power := Nat.pow_le_pow_right (show 0<v.digitRadix+2 by omega) arity
  have limit := Nat.mul_le_mul_left (v.quoteWork+4) power
  simp only [List.length_ofFn,radix] at digits
  rw [shape,radix]
  unfold failureExprWork
  omega

theorem payload_coordinate (z : ℕ) (x : PayloadStrip.Quotes (Stages z (2^v.W)) k) :
    (payloadSlot z x).work≤v.coordinateWork := by
  cases x with
  | inl => change 2≤4+30*_; omega
  | inr a => rcases a with ⟨j,t⟩; change 4≤4+30*_; omega

theorem purchased_coordinate (z : ℕ) (sh : Shelf) (sampler : PurchaseSampler)
    (header : Calendar.StockCommit.PortHeader) (x : ChainStrip.Axes v.depth k) :
    (allChainSlot (z:=z) (d:=2^v.W) sh sampler v.depth header x).work≤v.coordinateWork := by
  let terms (i : Key z (2^v.W) k) := (keySlot sh sampler v.depth i x).atRow header.fieldTerm
  have small (i : Key z (2^v.W) k) : (terms i).work≤20 := by
    change 16 ≤ 20
    decide
  apply (BoughtSockets.choose_work_bound (count z (2^v.W) k) 0 20 terms header.ballTerm small).trans
  change 1+count z (2^v.W) k*(7+20+2)≤4+30*(publicStages v.W*(2*k))
  rw [count,fixed_stage_count z v.W]
  omega

theorem payload_test_quotes_work (P : v.Placement) (z width phase trial : ℕ)
    (i : Fin (Fintype.card (PayloadStrip.Quotes (Stages z (2^v.W)) k))) :
    ((v.payloadTest P z width phase trial).quoted i).work ≤ v.quoteWork := by
  change (quoted _ _ _ _ i).work ≤ _
  rw [quote_work]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (v.payload_coordinate z _)) 16

theorem purchase_test_quotes_work (P : v.Placement) (z width phase trial j tick : ℕ)
    (i : Fin (Fintype.card (ChainStrip.Axes v.depth k))) :
    ((v.purchasedTest P z width phase trial j tick).quoted i).work ≤ v.quoteWork := by
  change (quoted _ _ _ _ i).work ≤ _
  rw [quote_work]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (v.purchased_coordinate z _ _ _ _)) 16

/-- The bound covers the original two quote lookups, the purchased stratum
selector and the full radix encoding, at every date of every calendar. -/
theorem failure_expr_work (P : v.Placement) (z width : ℕ) (a : Attempt) :
    (v.nativeFormats P z width a).market.failures.test.work≤v.failureExprWork := by
  cases a with
  | outer phase trial =>
    rw [v.payload_failure P z width phase trial]
    have arity : Fintype.card (PayloadStrip.Quotes (Stages z (2^v.W)) k) ≤ v.quoteCount := by
      rw [show Stages z (2^v.W)=publicStages v.W from fixed_stage_count ..]
      exact le_max_left ..
    apply v.failure_work (v.payloadTest P z width phase trial) arity rfl (by change 6≤10; decide)
    exact v.payload_test_quotes_work P z width phase trial
  | inner phase trial j tick =>
    rw [v.purchased_failure P z width phase trial j tick]
    apply v.failure_work (v.purchasedTest P z width phase trial j tick) (le_max_right ..) rfl (by change 7≤10; decide)
    exact v.purchase_test_quotes_work P z width phase trial j tick

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
