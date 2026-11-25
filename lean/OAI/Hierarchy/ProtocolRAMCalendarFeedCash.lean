import OAI.Hierarchy.ProtocolRAMCalendarCash
import OAI.Hierarchy.ProbeCalendarBoundary

namespace OAI
/-! # Price of spilled whole-bit stock at an executed calendar feed -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
variable {w q d : ℕ} {I : Type*} [Fintype I]

/-- Each commodity has its recorded overflow width and its public ordinary route
price table indexed by a resident key. Every earlier paid row and price label is
protected across the feed's scans. -/
structure FeedPosting (A : AccountColumns I) (C : Chart w q d) (event : Boundary) (src dst : Attempt) where
  overflow : I→ℕ
  key : I→ℕ
  price : I→ℕ→ℝ
  enum : Fin (A.charges src) ⊕ I ≃ Fin (A.charges dst)
  old : ∀ i, A.row dst (enum (.inl i))=A.row src i
  rows : ∀ i, A.row dst (enum (.inr i))=⟨overflow i,key i,price i⟩
  protect : ∀ i,protected C (A.row src i).width (.feed event) ∧ protected C (A.row src i).key (.feed event)

theorem FeedPosting.price_eq {A : AccountColumns I} {C : Chart w q d} {event : Boundary} {src dst : Attempt}
    (P : FeedPosting A C event src dst) (m : Memory w) (runReady : ready C (.feed event) m) :
    let out := after C (.feed event) m
    (A.read dst out).paid=(A.read src m).paid+
      ∑ i,((out (P.overflow i)).val:ℝ)*P.price i (out (P.key i)).val/A.payloadWidth := by
  apply A.append_executed C [.feed event] m src dst (fun i=>⟨P.overflow i,P.key i,P.price i⟩)
    P.enum P.old P.rows ⟨runReady,trivial⟩
  intro i e he
  obtain rfl := List.mem_singleton.mp he
  exact P.protect i

theorem FeedPosting.charged {A : AccountColumns I} {C : Chart w q d} {event : Boundary} {src dst : Attempt}
    (P : FeedPosting A C event src dst) (m : Memory w) (runReady : ready C (.feed event) m)
    (cap : ℕ) (raw : I→ℕ)
    (amount : ∀ i,((after C (.feed event) m) (P.overflow i)).val=spillBits cap A.payloadWidth raw i)
    (prices : ∀ i,P.price i ((after C (.feed event) m) (P.key i)).val≤A.box i) :
    (A.read dst (after C (.feed event) m)).paid≤(A.read src m).paid+
      pairing (bitStock A.payloadWidth (spillBits cap A.payloadWidth raw)) A.box := by
  rw [P.price_eq m runReady]
  apply add_le_add le_rfl
  unfold pairing bitStock
  apply Finset.sum_le_sum
  intro i _
  rw [amount i,mul_div_right_comm]
  exact mul_le_mul_of_nonneg_left (prices i) (by positivity)

theorem FeedPosting.quiet {A : AccountColumns I} {C : Chart w q d} {event : Boundary} {src dst : Attempt}
    (P : FeedPosting A C event src dst) (m : Memory w) (runReady : ready C (.feed event) m)
    (stock : ∀ i,(after C (.feed event) m) (A.stockAt dst i)=m (A.stockAt src i))
    (zero : ∀ i, (after C (.feed event) m) (P.overflow i)=0) :
    A.read dst (after C (.feed event) m)=A.read src m := by
  have bits : (A.read dst (after C (.feed event) m)).bits=(A.read src m).bits :=
    funext fun i=>congrArg Fin.val (stock i)
  have cost : (A.read dst (after C (.feed event) m)).paid=(A.read src m).paid := by
    rw [P.price_eq m runReady]
    simp [zero]
  cases h₀ : A.read src m with
  | mk old oldPaid =>
    cases h₁ : A.read dst (after C (.feed event) m) with
    | mk next nextPaid => simpa only [h₁,h₀,Inventory.mk.injEq] using And.intro bits cost

theorem FeedPosting.boundary {A : AccountColumns I} {C : Chart w q d} {p ticks cap : ℕ}
    (m : Memory w) (P : FeedPosting A C (.outer p) (.outer p C.mesh.outerFuel) (.outer (p+1) 0))
    (runReady : ready C (.feed (.outer p)) m)
    (keep : ∀ i,((after C (.feed (.outer p)) m) (A.stockAt (.outer (p+1) 0) i)).val=
       min (A.bank.requests A.payloadWidth ticks p (A.read (.outer p C.mesh.outerFuel) m) i) (cap*A.payloadWidth))
    (amount : ∀ i,((after C (.feed (.outer p)) m) (P.overflow i)).val=
      spillBits cap A.payloadWidth (A.bank.requests A.payloadWidth ticks p (A.read (.outer p C.mesh.outerFuel) m)) i)
    (prices : ∀ i,P.price i ((after C (.feed (.outer p)) m) (P.key i)).val≤A.box i) :
    A.bank.BoundaryRead ticks A.payloadWidth cap p (A.read (.outer p C.mesh.outerFuel) m)
      (A.read (.outer (p+1) 0) (after C (.feed (.outer p)) m)) :=
  ⟨keep,P.charged m runReady cap _ amount prices⟩

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
