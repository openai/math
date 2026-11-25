import OAI.Computability.NearSquareRoot.PhysicalWalshSwapData
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapIdle
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapRulers
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeConjugate

/-! # Near-root interchange of the upper parts of two Walsh slots

The program pads the outer prefix, packs complete suffixes into uniform
bitstrings, interchanges the high fields, then restores record boundaries
and crops the trailing prefix. Its only input is the compact Walsh
descriptor and the original lane of signed complex records.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap
open IntegerMultiplication Code Space
open PhysicalWalshSwapCodec (payload)
open ElementarySchedule (slotWidth)

private theorem upperOne {ρ : ℝ} {a : ℕ} (W D : ℕ) (i j : Fin (a+1)) (order : j.val < i.val)
    (nonneg : 0 ≤ ρ)
    (core : ∀ {I : Type} (data : I → Packet), (∀ t, 0 < (data t).width) →
      (∀ t, (data t).geometry.wing=0 ∨ (size (data t).geometry.header+1)^D ≤ (data t).width) →
      BoundedTask (fun t => ⌈((data t).volume : ℝ)*(((data t).geometry.wing+1:ℕ):ℝ)^ρ⌉₊)
        (Packet.volume ∘ data) (Packet.input ∘ data) (Packet.output ∘ data)) :
    let s : XorInput W → Shape := XorInput.shape
    Stage ρ (a+1) s (fun t => send (Header.wire (a+1) (s t),laneFlat (a+1) W (s t) t.row))
      (fun t => send (laneFlat (a+1) W (s t) (upper D i j (s t) t.row))) := by
  intro s
  let A := a+1
  let c t := reserve D A (s t)
  let z t := geometry W i j (s t) (c t)
  let b t := stride i j (s t) (c t)
  let n t := (z t).grid.count
  let w t := (s t).w
  let hd t := Header.wire A (s t)
  let x (t : XorInput W) := SwapPrefix.extend A W (s t) t.row
  let d (t : XorInput W) := bank W D i j (s t) (x t)
  let y t := x t ∘ moved W D i j (s t)
  have ne : i ≠ j := by intro h; subst j; exact (Nat.lt_irrefl _ order)
  have pos (t : XorInput W) : 0 < (s t).level := t.positive
  have hb t : 0 < b t := Nat.mul_pos (Nat.two_pow_pos _) (s t).suff_pos
  have hn t : 0 < n t := by dsimp only [n];rw [geometry_count]; exact Nat.two_pow_pos _
  have vol t : n t*b t = SwapPrefix.paddedSize A W (s t) :=
    volume_eq (W:=W) i j ne (s t) (pos t) (c t) (min_le_left ..)
  have bound t : (n t*b t+1)*(w t+1) ≤ 2*allowance A 0 (s t) := by
    rw [vol]; exact lane_volume_le ..
  let linear {p q : XorInput W → Tree}
      (h : BoundedTask (fun t => (n t*b t+1)*(w t+1)) (fun t => (n t*b t+1)*(w t+1)) p q) :
      Stage ρ A s p q := Stage.linear (d:=0) (h.bound 2 2 (fun t => by have := bound t; omega)
        (fun t => by have := bound t; omega))
  obtain ⟨pd,pad⟩ := SwapPrefix.padWithHeader A W s (fun t => t.row)
  have prep := (Stage.linear (ρ:=ρ) (d:=pd) pad)
  have emit := PhysicalWalshSwapCodec.packOrdinal w b n x hn hb
  have packing := Stage.supply (Rulers.pack_bounded D W i j s ne pos) (linear emit)
  have actual := core d (fun t => Nat.mul_pos (hb t) (by omega))
    (fun t => bank_room W D i j (s t) (x t) ne (pos t))
  have rect : Stage ρ A s (Packet.input ∘ d) (Packet.output ∘ d) := by
    refine ⟨0,actual.bound 5 4 ?_ ?_⟩ <;> intro t
    · have h := bank_cost W D i j nonneg (s t) (x t) ne (pos t)
      change ⌈((d t).volume : ℝ)*(((d t).geometry.wing+1:ℕ):ℝ)^ρ⌉₊+1 ≤ _
      exact h.trans (Nat.mul_le_mul_left 5 (Nat.succ_le_succ (Nat.le_add_left ..)))
    · change (d t).volume+1 ≤ _
      rw [show (d t).volume = SwapPrefix.paddedSize A W (s t)*(2*(w t+1)) from bank_volume W D i j _ _ ne (pos t)]
      have h := lane_volume_le A W 0 (s t)
      change (SwapPrefix.paddedSize A W (s t)+1)*(w t+1) ≤ _ at h
      ring_nf at h ⊢
      omega
  have perm : ∀ t, (d t).output = send ((List.range (n t)).map (payload (b t) (y t))) := by
    intro t
    apply congrArg send
    apply List.map_congr_left
    intro k _
    exact (PhysicalWalshSwapCodec.payload_map (hb t) (x t) (wingSource (z t)) k).symm
  have swapping : Stage ρ A s
      (fun t => send ((z t).header,(List.range (n t)).map (payload (b t) (x t))))
      (fun t => send ((List.range (n t)).map (payload (b t) (y t)))) := by
    exact (show (Packet.output ∘ d) = _ from funext perm) ▸ rect
  have swapping' := Stage.supply (Rulers.rect_bounded D W i j s) swapping
  have read := PhysicalWalshSwapCodec.unpackOrdinal w b n y hn hb
  have unpacking := Stage.supply (Rulers.unpack_bounded D W i j s ne pos) (linear read)
  obtain ⟨cd,crop⟩ := SwapPrefix.crop A W s y
  have clean := Stage.linear (ρ:=ρ) (d:=cd) crop
  have packedStage := packing.thenRun (swapping'.thenRun unpacking)
  have paddedStage : Stage ρ A s
      (fun t => send (hd t, SwapPrefix.stream (SwapPrefix.paddedSize A W (s t)) (x t)))
      (fun t => send (hd t, SwapPrefix.stream (SwapPrefix.paddedSize A W (s t)) (y t))) := by
    change Stage ρ A s (fun t => send (hd t,SwapPrefix.stream (n t*b t) (x t)))
      (fun t => send (hd t,SwapPrefix.stream (n t*b t) (y t))) at packedStage
    simpa only [vol] using packedStage
  have eq (t : XorInput W) : laneFlat A W (s t) (y t) = laneFlat A W (s t) (upper D i j (s t) t.row) := by
    apply List.map_congr_left
    intro k hm
    have h := moved_lt W D i j (s t) (pos t) order k (List.mem_range.mp hm)
    change Dusk.mark (SwapPrefix.extend A W (s t) t.row (moved W D i j (s t) k)) = _
    rw [SwapPrefix.extend,ite_eq_left h,moved_eq W D i j (s t) order k]
    rfl
  have complete := prep.thenRun (paddedStage.thenRun clean)
  simpa only [eq] using complete

/-- A single reserve degree precedes all ordered pairs and every recursive
level. The three preparatory scans use the same linear arena as the swap. -/
theorem upperRun (a W : ℕ) {ρ : ℝ} (rate : 1/2 < ρ) : ∃ D d : ℕ, ∀ e, d ≤ e →
    ∀ i j : Fin (a+1), j.val < i.val → Route.FlatRun (W:=W) a
      (nodeScan a W e (wideExtra ρ (a+1))) (nodeArena a W e) (upper D i j) := by
  classical
  obtain ⟨D,core⟩ := packed_or_idle rate
  let G := {g : Fin (a+1) × Fin (a+1) // g.2.val < g.1.val}
  choose d run using (fun g : G => upperOne W D g.val.1 g.val.2 g.property (by linarith : 0 ≤ ρ) core)
  refine ⟨D,Finset.univ.sup d,fun e le i j order => ?_⟩
  let g : G := ⟨(i,j),order⟩
  have enough (t : XorInput W) : allowance (a+1) (d g) t.shape ≤ nodeArena a W e t.shape :=
    (allowance_mono ((Finset.le_sup (f:=d) (Finset.mem_univ g)).trans le) _).trans (le_max_left ..)
  exact (run g).mono (fun t => Nat.add_le_add_right (enough t) _) enough

end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
