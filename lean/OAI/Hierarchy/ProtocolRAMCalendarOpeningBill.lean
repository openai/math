import OAI.Hierarchy.ProtocolRAMCalendarNativeAccounts
import OAI.Hierarchy.ProbeReportedGeometry

namespace OAI
/-! # One opening fee for each actually bought catalogue link -/

namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe ProbeStage ProbeStage.ReportSockets ProbeStage.CoreBoard
open scoped BigOperators Classical
noncomputable section
variable {h W k count : ℕ}

/-- Sum over the actual physical edges, with the native common length code and
the native scale. The type of bought edges contains precisely one edge for each
realized chain on each gated purchase tick, including any repeated endpoint pair. -/
theorem catalogue_openings (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k count) (M : ℕ) (p q Q Λ : ℝ) :
    (∑e : Catalogue S π depth marked,Λ*capacity p q Q (scaleOf S π depth marked e)
      (lenCode S π depth marked M e)) =
      coreDebit S h (2^W) k p q Q Λ (dyadicScale W) M+
        ∑a : Fin count,(Fintype.card (LiveChains S π depth (marked a)):ℝ)*(Λ*(dyadicScale W)^p) := by
  classical
  have pos : 0<dyadicScale W := by unfold dyadicScale; positivity
  have opening : Λ*capacity p q Q (dyadicScale W) 1=Λ*(dyadicScale W)^p := by
    simp [capacity,pos.ne']
  rw [Fintype.sum_sum_type]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro e _
    change Λ*capacity p q Q (coreScale (dyadicScale W) e) (coreCode S M e)=_
    rw [coreCode_read]
  · change (∑e : Bought S π depth marked,Λ*capacity p q Q (dyadicScale W) ((1:ℕ):ℝ))=_
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Nat.cast_one,opening,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- The genuine printed row ordering is immaterial to the physical activation
bill. Quantities on every purchased edge enter individually in the sum. -/
theorem reported_openings {R : Type*} [Fintype R] (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k count) (M : ℕ) (p q Q Λ : ℝ)
    (index : R ≃ Catalogue S π depth marked) (t len : R→ℝ)
    (scale : ∀r,t r=scaleOf S π depth marked (index r))
    (length : ∀r,len r=(lenCode S π depth marked M (index r):ℝ)) :
    (∑r,Λ*capacity p q Q (t r) (len r))=
      coreDebit S h (2^W) k p q Q Λ (dyadicScale W) M+
        ∑a : Fin count,(Fintype.card (LiveChains S π depth (marked a)):ℝ)*(Λ*(dyadicScale W)^p) := by
  simp only [scale,length]
  rw [index.sum_comp (fun e=>Λ*capacity p q Q (scaleOf S π depth marked e) (lenCode S π depth marked M e))]
  exact catalogue_openings S π depth marked M p q Q Λ

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
