import OAI.Hierarchy.HistorySelectedSeedSlot
import OAI.Hierarchy.TraceReceiverSeedOffset

namespace OAI
/-! # Native seed origins agree with the physical pin interval, including its final clip -/

namespace Hierarchy.TraceReceiverSeedWords
open ThreeFlat Diagonal Diagonal.TraceSourceOwner Diagonal.LaneCursor
open Diagonal.HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM FactorPinIntervals GridThrough
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W)

/-- The pointer inherited through any selected join is the actual slot of its
original input bit on the two-constant-shifted receiver tape. Positive cursor
layers have no external origins, and an empty final bucket needs no slot. -/
theorem source_pointer {axes n q d N : ℕ} (Q : Layout (Cell axes n×Fin q) S N d)
    (owner : ℕ→Fin N) (issued : ∀j:Fin S,Q.origin j=owner (j.val/(2*2^low)))
    (v : PairedCursor.Site (k+1)) (receiver : Memory W) (intervals : ℕ) (fit : d≤2^W)
    (offset : ∀ h : 0<width M t hF st v,
      receiver (intervals+4*(finFunctionFinEquiv v.2).val+3)=
        ((Q.slot (source M t hF st v ⟨0,h⟩)).val:Word W))
    (i : Fin (width M t hF st v)) :
    2+(Q.slot (source M t hF st v i)).val =
      2+(receiver (intervals+4*(finFunctionFinEquiv v.2).val+3)).val+i.val := by
  by_cases zero : v.1=0
  · have count:=width_original M t hF st v zero
    have has : 0<width M t hF st v:=Nat.zero_lt_of_lt i.isLt
    have active : 0<bucketLength S (2*2^low) (finFunctionFinEquiv v.2).val:=count ▸ has
    have first:=offset has
    rw [source_original M t hF st v zero] at first ⊢
    exact HistorySelectedSeed.pointer_at Q owner issued (by positivity)
      (finFunctionFinEquiv v.2) active receiver intervals fit first (i.cast count)
  · have noPins : width M t hF st v=0 := by simp [width,zero]
    exact Fin.elim0 (i.cast noPins)

end Hierarchy.TraceReceiverSeedWords

end OAI
