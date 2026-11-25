import OAI.Hierarchy.TaggedWideNamedWidths
import OAI.Hierarchy.ProbeFixedWideNeighborCapacity

namespace OAI
/-! Width of a whole neighbor word in the numbered dated chart. -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph WireTelescope AdaptiveProbe ProtocolRAM ReportSockets
open scoped Classical BigOperators

variable {h W k jobs N : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k jobs) (exclusive : Exclusive marks)
    (rows : Fin N≃Source S π depth marks)
local notation "ends" => sorted S π depth marks ∘ rows
local notation "roles" => named S π depth marks exclusive rows
local notation "degree" => stride k S.degree jobs

include exclusive

/-- The positive rows on one chord inject into the native role codes at
its first endpoint. Parallel paid rows and parallel goods are counted separately. -/
theorem chord_width_room (quantity : Fin N→ℕ) (budget : ℕ) (each : ∀i,quantity i≤budget)
    (ch : Chord (siteLast h (2^W) k+1)) :
    installedWidths ends quantity ch ≤ degree*budget := by
  classical
  let band:=Finset.univ.filter (fun i : Fin N=>ends i=ch)
  let position (i : Fin N) := roles (i,false)
  let digit (i : Fin N) : Fin degree := ⟨code S (position i),code_bound S (position i)⟩
  have anchor (i : Fin N) (hi : i∈band) :
      name (site S (position i))=(portGraph _).vertex ch false := by
    have edge : ends i=ch:=(Finset.mem_filter.mp hi).2
    exact (named_site S π depth marks exclusive rows i false).trans
      (congrArg (fun e=>(portGraph _).vertex e false) edge)
  have width : band.card≤degree := by
    have bound := Finset.card_le_card_of_injOn (s:=band) (t:=(Finset.univ : Finset (Fin degree))) digit
      (fun _ _=>Finset.mem_univ _) (by
        intro i hi j hj eq
        have same : shelfSlot S (position i)=shelfSlot S (position j) := by
          apply congrArg finProdFinEquiv
          exact Prod.ext ((anchor i hi).trans (anchor j hj).symm) eq
        exact congrArg Prod.fst ((roles).injective ((shelfSlot S).injective same)))
    simpa using bound
  calc
    installedWidths ends quantity ch = ∑i ∈ band,quantity i := by
      simp only [installedWidths,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,band,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hit : ends i=ch
      · simp [unitChord,Finsupp.single_apply]
      · simp [unitChord,Finsupp.single_apply]
    _ ≤ ∑i ∈ band,budget := Finset.sum_le_sum (fun i _=>each i)
    _ = band.card*budget := by simp
    _ ≤ degree*budget := Nat.mul_le_mul_right _ width

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles ReportSockets WireTelescope LinearAlgebra.SpectralBooks ChordGraph

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width unitCost : ℕ) (π : Equiv.Perm (Fin (2^h))) (mark : Marks h v.W k v.wideJobs)
    (ex : Exclusive mark) {N : ℕ} (rows : Fin N≃Source v.sampler π v.depth mark)

include ex in
theorem wide_neighbor_chord (quantity : Fin N→ℕ)
    (each : ∀i,quantity i≤v.wideHistoryUnit unitCost*width)
    (ch : Chord (siteLast h (2^v.W) k+1)) :
    installedWidths (sorted v.sampler π v.depth mark ∘ rows) quantity ch≤v.wideNeighborCap width unitCost := by
  have counted:=chord_width_room v.sampler π v.depth mark ex rows quantity _ each ch
  apply le_trans counted
  dsimp only [wideNeighborCap,wideNeighborDigits]
  rw [←Nat.mul_assoc]
  exact (Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1<2) _)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
