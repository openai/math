import OAI.Hierarchy.ProtocolRAMCalendarPrior
import OAI.Hierarchy.ProtocolRAMCalendarVerdict
import OAI.Hierarchy.ProtocolRAMCalendarFuel

namespace OAI
/-! # Historical guard readbacks at the real frozen inventory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open PurchaseStage
open scoped Fin.CommRing Classical
noncomputable section
variable {w q d : ℕ}

private theorem prior_congr (H J : ℕ→ℕ) (n : ℕ) (test : ℕ→Prop) (eqn : ∀ i<n,H i=J i) :
    (∃ i<n,test (H i)) ↔ ∃ i<n,test (J i) := by
  constructor
  · rintro ⟨i,hi,h⟩
    exact ⟨i,hi,(eqn i hi) ▸ h⟩
  · rintro ⟨i,hi,h⟩
    exact ⟨i,hi,(eqn i hi).symm ▸ h⟩

theorem disabled_congr (c : Mesh) (H J : Attempt→ℕ) (a : Attempt) (h : agrees c H J a) :
    disabled c H a ↔ disabled c J a := by
  cases a with
  | outer p a =>
    dsimp only [disabled,externalCap]
    rw [prior_congr _ _ p (fun i=>i=2 ∨ i=3) h.1,prior_congr _ _ a (fun i=>i=1) h.2]
  | inner p a j b =>
    dsimp only [disabled,reserveCap]
    rw [h.1,prior_congr _ _ j (fun i=>i=2) h.2.1,prior_congr _ _ b (fun i=>i=1) h.2.2]

def stopRoom (C : Chart w q d) (a : Attempt) : Prop :=
  let B := repair C a
  let x := C.stopAt a
  (x<(C.frozen a).start ∨ (C.frozen a).stop≤x) ∧
    x<B.tests.excess.out ∧ x<B.tests.payload.out ∧ x<B.tests.discrepancy.out ∧ x<B.repairBits.base

theorem live_stop (C : Chart w q d) (a : Attempt) (m : Memory w) (fit : ready C (.attempt a) m)
    (layout : stopRoom C a) (wide : 4≤2^w) :
    let B := repair C a
    AttemptGate.bit B.policy.stop (postSnapshot (C.layout a) B (prepared C a m)) =
      decide (disabled C.mesh (archive C.modeAt m) a) := by
  let B := repair C a
  let x := C.stopAt a
  let v := prepared C a m
  obtain ⟨hf,hx,hy,hz,hm⟩ := layout
  have outside : ¬(B.repairBits.base≤x ∧ x<B.repairBits.base+(C.layout a).candidates) :=
    fun h => Nat.not_le_of_gt hm h.1
  have observed : postSnapshot (C.layout a) B v x =
      (if disabled C.mesh (archive C.modeAt m) a then (1:Word w) else 0) := by
    calc
      _ = B.tests.after v x := by rw [postSnapshot,image,fillSegment,ite_eq_right outside]
      _ = v x := by
        unfold AttemptGate.TestBoard.after
        rw [B.tests.discrepancy.frame _ _ hz,B.tests.payload.frame _ _ hy,B.tests.excess.frame _ _ hx]
      _ = (guard C a).apply m x := (C.frozen a).frame _ _ fit.2.1 hf
      _ = _ := by
        change image x 1 (stop C.mesh C.modeAt a) m x = _
        simp [image,fillSegment,stop_snapshot _ _ _ _ _ wide]
  have one : (1:Word w)≠0 := by
    intro eqn
    have h := congrArg Fin.val eqn
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (n:=2^w) (a:=1) (by omega)] at h
    exact Nat.one_ne_zero h
  change decide (postSnapshot (C.layout a) B v x≠0)=_
  exact (congrArg (fun value : Word w => decide (value≠0)) observed).trans
    (by split_ifs <;> simp_all)

def seen (C : Chart w q d) (a : Attempt) (m : Memory w) :=
  AttemptGate.actual (repair C a).policy (postSnapshot (C.layout a) (repair C a) (prepared C a m))

private theorem seen_at (C : Chart w q d) (a : Attempt) (m : Memory w) (H : Attempt→ℕ)
    (fit : ready C (.attempt a) m) (layout : stopRoom C a) (wide : 4≤2^w)
    (prior : agrees C.mesh (archive C.modeAt m) H a) :
    let t := (repair C a).policy
    let view_ := postSnapshot (C.layout a) (repair C a) (prepared C a m)
    seen C a m = AttemptGate.selectMode t.injection t.reserve (decide (disabled C.mesh H a))
      (AttemptGate.bit t.excess view_) (AttemptGate.bit t.payload view_) (AttemptGate.bit t.discrepancy view_) := by
  have stop := live_stop C a m fit layout wide
  have swap : decide (disabled C.mesh (archive C.modeAt m) a) = decide (disabled C.mesh H a) :=
    Bool.decide_congr (disabled_congr _ _ _ _ prior)
  let t := (repair C a).policy
  let view_ := postSnapshot (C.layout a) (repair C a) (prepared C a m)
  exact congrArg (fun flag => AttemptGate.selectMode t.injection t.reserve flag
    (AttemptGate.bit t.excess view_) (AttemptGate.bit t.payload view_) (AttemptGate.bit t.discrepancy view_)) (stop.trans swap)

theorem innerLaw_of_snapshot (C : Chart w q d) (H : Attempt→ℕ) (p a j : ℕ)
    (mem : ℕ→Memory w) (wide : 4≤2^w)
    (data : ∀ b<C.mesh.innerFuel, let v := Attempt.inner p a j b
      ready C (.attempt v) (mem b) ∧ stopRoom C v ∧ agrees C.mesh (archive C.modeAt (mem b)) H v ∧
      H v=seen C v (mem b)) : innerLaw C.mesh H p a j := by
  intro b hb
  let v := Attempt.inner p a j b
  obtain ⟨ok,hl,agree,hH⟩ := data b hb
  have actual := seen_at C v (mem b) H ok hl wide agree
  dsimp only at actual ⊢
  rw [hH,actual]
  have reserve : (repair C v).policy.reserve=true := by
    rfl
  by_cases stopped : disabled C.mesh H v
  · have h : disabled C.mesh H (Attempt.inner p a j b) := stopped
    simp [h,stopped,AttemptGate.selectMode]
  · have h : ¬disabled C.mesh H (Attempt.inner p a j b) := stopped
    simp only [ite_eq_right h,Bool.decide_false stopped,AttemptGate.selectMode,reserve]
    split_ifs <;> simp_all

theorem outerLaw_of_snapshot (C : Chart w q d) (H : Attempt→ℕ) (p : ℕ)
    (mem : ℕ→Memory w) (wide : 4≤2^w)
    (data : ∀ a<C.mesh.outerFuel, let v := Attempt.outer p a
      ready C (.attempt v) (mem a) ∧ stopRoom C v ∧ agrees C.mesh (archive C.modeAt (mem a)) H v ∧
      H v=seen C v (mem a)) : outerLaw C.mesh H p := by
  intro a ha
  let v := Attempt.outer p a
  obtain ⟨ok,hl,agree,hH⟩ := data a ha
  have actual := seen_at C v (mem a) H ok hl wide agree
  dsimp only at actual ⊢
  rw [hH,actual]
  have reserve : (repair C v).policy.reserve=false := by
    rfl
  by_cases stopped : disabled C.mesh H v
  · have h : disabled C.mesh H (Attempt.outer p a) := stopped
    simp [h,stopped,AttemptGate.selectMode]
  · have h : ¬disabled C.mesh H (Attempt.outer p a) := stopped
    simp only [ite_eq_right h,Bool.decide_false stopped,AttemptGate.selectMode,reserve]
    split_ifs <;> simp_all

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
