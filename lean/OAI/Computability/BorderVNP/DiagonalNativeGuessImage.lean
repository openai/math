import OAI.Computability.BorderVNP.TransmissionPinIndex
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # The substituted row and original live column on every pin-preparation return

The single fixed-length local choice on team zero and the empty choice on other teams
give an exact path bijection. Its memory image contains the clamped substituted row
at every physical slot and the unchanged original column at each real lead-team slot.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator

variable {w R r t d link inner n : ℕ} {Edge : Type}

/-- One actual native pin return per substituted row on the lead team, with its genuine
original column and every prescribed zero in the resulting physical RAM image. -/
theorem Wiring.guessImageEquiv (G : Wiring R r t d link inner n Edge) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :
    let L := G.pinLayout u ibase hbase starbase
    (G.processorFields u pin ext ibase hbase starbase).ContainsInput m →
    Frame L (readings pub) (readings m) → (pub 0).val+24 < 2^w →
    L.stride < 2^w → L.count < 2^w → L.width ≤ L.count → LoopFits w L → Separated L →
    ∃ E : (Fin L.guessWidth → Bool) ≃ Returns preparePins pub mac s m, ∀ b,
      (E b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b ∧
      traceCost (E b).val.1 ≤ pinSetup.slots+17*L.count+1 ∧
      (E b).val.2.2 = preparedMemory L (extendGuess b) m L.count ∧
      (∀ i < L.count, (E b).val.2.2 (ibase+i) = TeamTapeInputEmit.word w (extendGuess b i).toNat) ∧
      (u = 0 → ∀ i : Fin d, (E b).val.2.2 (hbase+i.val) = TeamTapeInputEmit.word w (pin i).toNat) := by
  intro L physical frame hf hs hc room fits sep
  obtain ⟨E,effects⟩ := preparePins_exact L pub mac m s frame hf (Nat.succ_pos _) hs hc room fits
  refine ⟨E,?_⟩
  intro b
  obtain ⟨bits,cost,_,_,mem⟩ := effects b
  refine ⟨bits,cost,mem,?_,?_⟩
  · intro i hi
    apply (congrFun mem (ibase+i)).trans
    change preparedMemory L (extendGuess b) m L.count (L.ibase+i) = _
    rw [preparedMemory_substitute L _ _ sep le_rfl hi]
    by_cases active : L.active i
    · rw [ite_eq_left active]
    · have outside : ¬ i < L.guessWidth := by
        unfold Layout.guessWidth
        split_ifs with hz
        · exact fun h => active ⟨hz,h⟩
        · omega
      simp [active,extendGuess,outside,TeamTapeInputEmit.word]
  · intro lead i
    apply (congrFun mem (hbase+i.val)).trans
    have live : L.active i.val := ⟨congrArg Fin.val lead,i.isLt⟩
    have inside : i.val < L.count := i.isLt.trans_le room
    change preparedMemory L (extendGuess b) m L.count (L.hbase+i.val) = _
    rw [preparedMemory_liveCopy L _ _ sep le_rfl inside live]
    change m (livePinAddress (R+1) (G.program.length+t) link i.val) = _
    rw [G.read_liveBit u pin ext ibase hbase starbase m physical i.val inside]
    simp [liveBit,lead,i.isLt]

end TeamContraction

end BorderVNP
end Computability
end OAI
