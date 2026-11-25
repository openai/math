import OAI.Hierarchy.TraceReceiverSeedWords
import OAI.Hierarchy.GridPinReceiverPrefix

namespace OAI
/-! # The actual first assigned word of each nonempty receiver interval -/

noncomputable section
namespace Hierarchy.TraceReceiverSeedWords
open ThreeFlat Diagonal Diagonal.TraceSourceOwner Diagonal.LaneCursor
open Diagonal.HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM FactorPinIntervals
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W)

theorem width_original (v : PairedCursor.Site (k+1)) (first : v.1=0) :
    width M t hF st v=bucketLength S (2*2^low) (finFunctionFinEquiv v.2).val := by
  unfold width
  rw [ite_eq_left first, bitIndex_pinCount]
  simp only [bucketLength,pinCount,pinSpan,Nat.one_mul,Nat.mul_one]

theorem source_original (v : PairedCursor.Site (k+1)) (first : v.1=0)
    (i : Fin (width M t hF st v)) :
    source M t hF st v i = blockBit S (2*2^low) (finFunctionFinEquiv v.2).val
      (i.cast (width_original M t hF st v first)) := by
  apply Fin.ext
  rw [source,dite_eq_left first]
  change (finFunctionFinEquiv v.2).val*pinSpan 1 low+i.val=
    (finFunctionFinEquiv v.2).val*(2*2^low)+i.val
  rfl

end Hierarchy.TraceReceiverSeedWords

namespace Hierarchy.TraceReceiverOriginal
open ThreeFlat Diagonal RAM PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals TraceReceiverSeedWords
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {W pc regs words S base k low fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F≤2^W) (st : Word W)

/-- First word of every nonempty original interval, read at S5 after the
receiver itself ran its four bounded scans. -/
theorem interval_original {axes n q d N : ℕ} (P : GridPinPublisher.Plan)
    (Q : FactorPinIntervals.Layout (Cell axes n×Fin q) S N d) (base₅ : ℕ) (mem : Memory W)
    (span : P.source.span=2*2^low) (count : P.lanes=(S+P.source.span-1)/P.source.span)
    (lanes : P.lanes<2^W) (blocks : P.source.blocks+P.lanes≤2^W) (space : base₅+4*P.lanes≤2^W)
    (pins : P.header.pins=d) (pinsFit : d<2^W) (fit : (n+1)^axes*(q*d)≤2^W)
    (apart : ∀ b<P.lanes,∀ i<P.lanes,P.source.blocks+b≠base₅+4*i+3)
    (offset : ∀j:Fin S,P.bucketed mem (P.source.blocks+j.val/P.source.span)+
      ((j.val%P.source.span:ℕ):Word W)=((GridPinAddressImage.code (Q.address j)).val:Word W))
    (v : PairedCursor.Site (k+1)) (h : 0<width M t hF st v) :
    P.intervalMemory base₅ mem (base₅+4*(finFunctionFinEquiv v.2).val+3)=
      ((Q.slot (source M t hF st v ⟨0,h⟩)).val:Word W) := by
  have zero : v.1=0 := by
    by_contra neq
    simp only [width,ite_eq_right neq] at h
    omega
  let j:=source M t hF st v ⟨0,h⟩
  let b:=(finFunctionFinEquiv v.2).val
  have old : j.val=b*P.source.span := by
    change (source M t hF st v ⟨0,h⟩).val=_
    rw [source_original M t hF st v zero,span]
    change b*(2*2^low)+0=_
    simp
  have positive : 0<P.source.span := by rw [span];positivity
  have quotient : j.val/P.source.span=b := by rw [old,Nat.mul_div_cancel _ positive]
  have remainder : j.val%P.source.span=0 := by simp [old]
  have bound : b<P.lanes := by rw [count,←quotient];exact GridPinPublisher.bucket_visited positive j
  exact P.interval_read Q base₅ mem lanes blocks space pins pinsFit fit apart offset ⟨b,bound⟩ j quotient remainder

end Hierarchy.TraceReceiverOriginal
end

end OAI
