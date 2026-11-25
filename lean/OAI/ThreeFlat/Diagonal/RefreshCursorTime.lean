import OAI.ThreeFlat.Diagonal.RefreshCursorLayout
import OAI.ThreeFlat.Diagonal.RefreshScanPlan

namespace OAI
/-! # Linear refresh time at the actual immutable chronological header -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan NavigationDirectory RefreshDemandRows

theorem cursor_scan_time {a h k : ℕ} (E : SlotGraph (Fin (mPort a)) h) (pad K : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ) (size bits : Fin (k+1) → ℕ)
    (pool : ∀ j,Fin (size j) → Fin (mPort a) → Fin h → ℕ) :
    ∃ B : ℕ,∀ W (cur : Word W) (c : Cursor) (v t : ℕ),
      let e := allocate K c (.refresh v (mPort a) (2^t) h pad)
      (preScans cur base size).time e.words+(postScans cur E pad K base size bits pool).time e.words+
        (recordScans cur (mPort a) (1+h+pad) K).time e.words≤99+B*(v*mPort a*2^t) := by
  obtain ⟨B,cap⟩ := scan_time E pad K base size bits pool
  refine ⟨B*(19+15*(1+h+pad)+h),?_⟩
  intro W cur c v t
  let P := v*mPort a*2^t
  let d := 1+h+pad
  let e := allocate K c (.refresh v (mPort a) (2^t) h pad)
  let x := RefreshStageLayout.counts v (mPort a) (2^t) h pad
  have bounds := RefreshStageLayout.bounded (h:=h) (pad:=pad) (K:=K) (Nat.two_pow_pos a)
    (Nat.two_pow_pos t) (le_refl P)
  obtain ⟨_,nodes,_,_,_,ww,split,choice,graph,sparse,_⟩ := bounds
  have span : e.words 13+e.words 18+e.words 16+e.words 17+e.words 20+e.words 35+e.words 37+e.words 39+e.words 41≤
      (19+15*d+h)*P := by
    change x.splitSpan+x.choiceSpan+x.graphSpan+x.newWidthSpan+x.sparseSpan+5*x.nodes+6*x.nodes+
      2*x.nodes+8*d*x.nodes≤_
    calc
      _ ≤ 3*P+3*P+6*d*P+d*P+h*P+5*P+6*P+2*P+8*d*P := by
        gcongr
      _ = _ := by ring
  have q := cap W cur e.words
  exact q.trans (Nat.add_le_add_left (by simpa only [P,d,Nat.mul_assoc] using Nat.mul_le_mul_left B span) 99)

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
