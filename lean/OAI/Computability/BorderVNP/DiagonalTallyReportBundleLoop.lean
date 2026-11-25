import OAI.Computability.BorderVNP.DiagonalTallyReportBundleStep

/-! # Scanning every retained bundle of an owned cell, including empty sections -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA

/-- Chronological memory images from the true ordered bundle section. -/
def bundleImages (l : ReportLayout) : List ReportBundle → LocalReportCursor → (ℕ → ℕ) → ℕ → ℕ
  | [],_,m => m
  | b::bs,q,m => bundleImages l bs (q.advance b) (b.image l q m)

/-- Necessary physical input ranges, stated on the explicit numeric write images. -/
def bundleInputs (w : ℕ) (l : ReportLayout) (description : ℕ) :
    List ReportBundle → LocalReportCursor → ℕ → (ℕ → ℕ) → Prop
  | [],_,_,_ => True
  | b::bs,q,p,m => b.Input (w := w) l q p description m ∧
    bundleInputs w l description bs (q.advance b) (p+6) (b.image l q m)

/-- The actual sparse loop visits each original description once and each of its
marked copies once, in the native order. -/
def bundleTicks (l : ReportLayout) : List ReportBundle → LocalReportCursor → ℕ
  | [],_ => 1
  | b::bs,q => 1+b.cost l q+bundleTicks l bs (q.advance b)

/-- Fixed compiled loop for the half-open range named by the six-word cell header. -/
theorem bundleLoop_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : ReportLayout) (description : ℕ) (bs : List ReportBundle) (q : LocalReportCursor)
    (p : ℕ) (s : Bank w) (m : Memory w)
    (ready : q.ready l p (p+6*bs.length) (readings s))
    (input : bundleInputs w l description bs q p (readings m)) :
    ∃ es t mt, Runs pub mac (.whileLt 5 6 bundleReports) s m es t mt ∧
      traceCost es ≤ bundleTicks l bs q ∧
      (bs.foldl LocalReportCursor.advance q).ready l (p+6*bs.length) (p+6*bs.length) (readings t) ∧
      readings mt=bundleImages l bs q (readings m) := by
  induction bs generalizing q p s m with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.foldl_nil,bundleTicks,bundleImages] at ready ⊢
    have endLoop : ¬s 5<s 6 := by
      change ¬readings s 5<readings s 6
      rw [ready.2.2.1,ready.2.2.2.1]; omega
    exact ⟨_,s,m,.whileDone endLoop,by simp [traceCost,tick,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra],
      ready,rfl⟩
  | cons b bs ih =>
    have tailEnd : p+6*(b::bs).length=(p+6)+6*bs.length := by simp; omega
    have guard : s 5<s 6 := by
      change readings s 5<readings s 6
      rw [ready.2.2.1,ready.2.2.2.1,tailEnd]; omega
    obtain ⟨a,t,mt,r₁,c₁,h₁,m₁⟩ := b.runs l q p _ description pub mac s m ready input.1
    rw [tailEnd] at h₁
    obtain ⟨e,u,mu,r₂,c₂,h₂,m₂⟩ := ih (q.advance b) (p+6) t mt h₁ (m₁ ▸ input.2)
    have r := Runs.whileStep guard r₁ r₂
    refine ⟨_,u,mu,r,?_,?_,?_⟩
    · change 1+traceCost (a++e) ≤ 1+b.cost l q+bundleTicks l bs (q.advance b)
      rw [show traceCost (a++e)=traceCost a+traceCost e from VPVNP.RAMBuckets.cost_append ..]; omega
    · simpa only [List.foldl_cons,tailEnd] using h₂
    · rw [m₂,m₁,bundleImages]

/-- The global descriptor cursors are the ones used in the exact operand list. -/
theorem local_fold_global (bs : List ReportBundle) (q : LocalReportCursor) :
    (bs.foldl LocalReportCursor.advance q).toReportCursor =
      bs.foldl ReportCursor.afterBundle q.toReportCursor := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => exact ih (q.advance b)

/-- Only actual marked copies consume the compact use tail. -/
theorem local_fold_external (bs : List ReportBundle) (q : LocalReportCursor) :
    (bs.foldl LocalReportCursor.advance q).external=q.external+(bs.map ReportBundle.useCount).sum := by
  induction bs generalizing q with
  | nil => simp
  | cons b bs ih => simp [List.foldl_cons,ih,LocalReportCursor.advance,Nat.add_assoc]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
