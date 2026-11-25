import OAI.Computability.BorderVNP.CubeTeamOwnedPublicPrefix
import OAI.Computability.BorderVNP.CubeGroupDirectoryBalances
import OAI.Computability.BorderVNP.CubeGroupDirectoryVolume

/-! # Capacity of the greedy teams with the actual public label and delivery arrays

The public label optimizer bounds the incoming group load of each physical
seven-word row. Its total width is bounded by the original compact processor
and live-field inventory. At the rounded paper dimensions, the native group
histogram fits a word and satisfies both actual checked limits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Crossing Physical MeanChoice LabelIndex TeamScales Filter RoutingISA VPVNP.BurstRAM

universe u v t

/-- Uniform eventual bounds for the true label-coded histogram on the actual
published directory. The second assertion uses the real unchecked schedule to
identify the arithmetic greedy loads and then proves both checks on them. -/
theorem PacketFormat.eventually_directory_capacity {F : Type u} [Field F] {n : ℕ} {η α ξ : ℝ}
    (p : PacketFormat F n η) (hη : 0 < η) (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(n+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ {netDim : ℕ} {P : Type v} {bits : P → ℕ} {Cell : Type}
      [Fintype Cell] [DecidableEq Cell] {A : Type t} [Fintype A] (r w : ℕ) (l : GroupWeights.Layout) (teams : TeamNative.Layout)
      (blocks : ℕ) (dir : LabelIndex.Layout) (producer : Packing.Directory.Layout)
      (pp lp : ℕ → ℕ × ℕ) (head : ℕ) (initial : Memory w)
      (N : Network netDim P bits) (cell : N.Site → Cell) (recv : A → Cell) (size : A → ℕ)
      (cellNum : Cell ≃ Fin dir.cells) (edgeOrd : N.CrossingEdge cell ↪ Fin dir.cableCount)
      (dataOrd : A ↪ Fin dir.deliveryCount) (M : ℕ)
      (D : LengthDeclaration n l.groups) (select : Packet n l.groups blocks → Selector n p.K p.h)
      (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (regs : Bank w) (mem : Memory w),
      let old := readings (Packing.Directory.ISA.publish initial head dir.deliveries (producer.directory pp lp))
      let X := exterior ξ r k
      ∀ (ep : Endpoints dir old) (cells : l.cells = dir.cells) (hd : 0 < l.groups),
        RowPlacement (networkRows N cell recv size) (fromTables dir old ep) cellNum (edgeOrd.sumMap dataOrd) →
        PackedLabelBudget N cell recv size ((X*(teams.r+1) : ℕ) : ℝ) M (l.groups^(n+1)) →
        producer.teams = teams.r+1 → producer.processors = r → producer.literal = literal α k →
        0 < producer.fields → 0 < producer.block → producer.fields ≤ 2 →
        producer.entries*producer.description ≤ producer.teams*producer.processors*(producer.literal/2) →
        dir.deliveryCount = (producer.directory pp lp).length → head+9 < dir.deliveries →
        (∀ j : Fin (producer.directory pp lp).length, ∀ t ∈ (producer.directory pp lp)[j.val].words, t < 2^w) →
        1 ≤ r → (teams.r+1 : ℝ) ≤ (k : ℝ)^(2*α) → l.groups = alphabet α k →
        blocks = blocksFor (X*(teams.r+1) : ℕ) (p.h*p.b) (l.groups^(n+1)) →
        passesLengths p.b p.s select D →
        PhysicalImage l (readings mem) blocks p.b p.K p.h D (directoryLabel cells hd ep n)
          (directoryRecv cells ep) (fun j => (deliveryAt dir old j.val).2) →
        readings pub 0 = l.frame →
        (⟨teams.r+1,X,teams.totals⟩ : TeamBudget.Layout).Fits l.frame w →
        ((∑ j ∈ Finset.range l.groups, l.weight (readings mem) j) < 2^w → CheckedFrame l teams (readings mem) w X) →
        (∑ j ∈ Finset.range l.groups, l.weight (readings mem) j) < 2^w ∧
          LocalRow.capacities l teams X (readings mem) := by
  have gap : 8*α*((n+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using hgap
  filter_upwards [p.eventually_budget_passes hη fixed hα hξ hgap,
    eventually_group_charge_room hα hξ (n+1) (p.h*p.b) p.expansion p.blockPositive gap] with k caps room
  intro netDim P bits Cell _ _ A _ r w l teams blocks dir producer pp lp head initial N cell recv size cellNum edgeOrd dataOrd M D select pub mac regs mem
    old X ep cells hd place labelBudget nteams proc lit fields block f2 tails count after fitted hr hR groups blockCount
    pass image base budgetFit mkFrame
  let widths := fun j : Fin dir.deliveryCount => (deliveryAt dir old j.val).2
  let label := directoryLabel cells hd ep n
  let dst := directoryRecv cells ep
  have balanced (u : Label (n+1) l.groups) :
      Balancing.load (Balancing.datum (fun j : Balancing.Bits widths => dst j.1) u) label ≤
      4*((X*(teams.r+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ) :=
    directory_data_balanced N cell recv size cellNum place cells n hd labelBudget u
  have pos : 0 < producer.processors := proc ▸ hr
  have width := Packing.CableTriples.published_deliveryWidth_le dir initial producer pp lp head pos fields block f2 tails
    count after fitted
  have volume : (∑ j, widths j) ≤ 3*(teams.r+1)*r*literal α k := by
    simpa only [widths,old,nteams,proc,lit] using width
  obtain ⟨small,_,pad,charges⟩ := room r (teams.r+1) hr (by omega) (by exact_mod_cast hR)
  rw [← groups] at small pad
  rw [← blockCount] at pad
  have total := sum_jointCost_le_volume (label := label) (recv := dst) p.s select pass
    (X*(teams.r+1)) hd η hη.le fixed p.width p.selector
    (by simpa only [Nat.cast_add,Nat.cast_one] using small) pad (charges _ volume)
  have sumFits := histogram_sum_fits image total budgetFit
  have frame := mkFrame sumFits
  obtain ⟨_,_,_,_,_,result⟩ := run_schedule pub mac l teams regs mem base frame.fields frame.setup frame.fits frame.allocated
    frame.frameFit frame.frame frame.groups frame.weights frame.keepAssign sumFits
  exact ⟨sumFits,(result.passes_iff X).mp (caps r l teams blocks (readings mem) _ (Fin dir.deliveryCount)
    D select label dst widths hr hR groups blockCount result image pass balanced volume)⟩

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
