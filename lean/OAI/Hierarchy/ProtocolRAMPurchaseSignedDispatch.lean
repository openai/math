import OAI.Hierarchy.ProtocolRAMPurchaseSigned
import OAI.Hierarchy.ProtocolRAMPurchaseDispatch

namespace OAI
/-! # Feeding the greedy purchase interpreter from the signed sampler scan -/

namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {w n m groups D h k : ℕ} {G : Type*}

def layout (s : PurchaseTape.Plan D) (b : PurchaseTape.Signed k) (n h : ℕ) : Dispatch :=
  ⟨PurchaseTape.count n D h,h+1,n+1,s.first,s.packed,s.work,s.source,s.gates,b.marks⟩

noncomputable abbrev liveRows (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (h : ℕ) :=
  PurchaseColumns.rowTile (h:=h) (ProtocolRAMPurchaseOwners.successor p enc sampler)

theorem ready_of_fits (s : PurchaseTape.Plan D) (b : PurchaseTape.Signed k)
    (size : PurchaseTape.Fits s w n groups m h) (bounds : PurchaseTape.SignedFits s b w n)
    (separate : s.packed + 3*(PurchaseTape.count n D h*(4*(h+1)+3)) ≤ s.work)
    (room : decisionBase (layout s b n h) + PurchaseTape.count n D h < 2^w) :
    DispatchReady (layout s b n h) w := by
  have sourceEnd := size.sourceFit.2.2
  have marksEnd := bounds.marks.2.2
  have sourceAfter := size.sourceAfter
  exact ⟨size.wide,size.sourceCapacity,size.sourceFit,size.gateFit,
    ⟨bounds.marks.1,bounds.marks.2.1,by change b.marks.base + b.marks.size ≤ s.packed; omega⟩,separate,room⟩

theorem signed_of_resident (L : Dispatch) (m : Memory w) (left : Finset (Fin L.tiles)) (wide : 0<w)
    (resident : Native.Resident L.marks m (fun i : Fin L.tiles => (decide (i∈left)).toNat)) :
    SignedWords L m ∧ marked L m = left := by
  have one : (1:Word w) ≠ 0 := by
    intro eqn
    have hn := congrArg Fin.val eqn
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')] at hn
    exact Nat.one_ne_zero hn
  constructor
  · intro i
    by_cases h : i ∈ left
    · right
      simpa [h] using resident i
    · left
      simpa [h] using resident i
  · ext i
    simp only [marked,Finset.mem_filter,Finset.mem_univ,true_and,resident i]
    by_cases h : i∈left <;> simp [h,one]

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
