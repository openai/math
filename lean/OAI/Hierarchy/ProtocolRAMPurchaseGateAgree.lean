import OAI.Hierarchy.ProtocolRAMPurchaseDispatch
import OAI.Hierarchy.ProtocolRAMPurchaseFlagPack
import OAI.Hierarchy.ProtocolRAMMarkTapeAgree

namespace OAI
/-! # Prefix agreement for the live gate compiler, purchase dispatch and flag pack -/

namespace Hierarchy.ProtocolRAM.GateAgree

open Computability.VPVNP.BurstRAM PrivateRAM Calendar ProbeStage.Native
open scoped Fin.CommRing
variable {w cut : ℕ} {m n : Memory w}

/-- The destination can straddle the cutoff. Each column reads only banks
below the cutoff, and prior writes may occur anywhere. -/
theorem columns (same : Below cut m n) (rows base : ℕ) (es : List Expr)
    (reads : ∀ e ∈ es, e.Fits w cut) :
    Below cut (result (ProbeStage.Native.columns rows base es) m)
      (result (ProbeStage.Native.columns rows base es) n) := by
  induction es generalizing m n base with
  | nil => exact same
  | cons e es ih =>
    apply ih
    · exact same.fill base rows _ _ (fun _ _ _ _ => same.expr e _ (reads e (List.mem_cons_self ..)) le_rfl)
    · exact fun t ht => reads t (List.mem_cons_of_mem e ht)

theorem gates (same : Below cut m n) (R H : ℕ) (source : Bank) (D : GateColumns.Directory)
    (work base : ℕ) (src : source.Fits w cut) (dir : ∀ j, j<6 → (D.bank j).Fits w cut) :
    Below cut (ProtocolRAMPurchaseGateColumns.output R H source D work base m)
      (ProtocolRAMPurchaseGateColumns.output R H source D work base n) := by
  apply columns same
  intro e he
  simp only [GateColumns.inputs,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> exact GateColumns.term_fits _ _ _ _ src dir

theorem flags (same : Below cut m n) {k : ℕ} (source : Fin k → Bank) (R base : ℕ)
    (src : ∀ i, (source i).Fits w cut) :
    Below cut (ProtocolRAMPurchaseFlagPack.output source R base m)
      (ProtocolRAMPurchaseFlagPack.output source R base n) := by
  apply columns same
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact ⟨src i,trivial⟩

private theorem bank_mono {source : Bank} {a b : ℕ} (h : source.Fits w a) (ab : a≤b) : source.Fits w b :=
  ⟨h.1,h.2.1,h.2.2.trans ab⟩

/-- The whole dispatch preserves agreement below the report end, including
all temporary gate words and mark-scan scratch. -/
theorem dispatch (same : Below cut m n) (L : PurchaseStage.Dispatch)
    (rows : Fin L.candidates → Fin L.depth → Fin L.tiles) (ready : PurchaseStage.DispatchReady L w)
    (before : PurchaseStage.decisionBase L+L.candidates≤cut) :
    Below cut (PurchaseStage.dispatchMemory L rows m) (PurchaseStage.dispatchMemory L rows n) := by
  have separate := ready.separate
  have workHi : L.work≤cut := by unfold PurchaseStage.decisionBase at before; omega
  have tapeWork : L.tape≤L.work := by omega
  have tapeHi := tapeWork.trans workHi
  have generated := gates same L.candidates L.depth L.source L.directory L.work L.tape
    (bank_mono ready.source tapeHi) (fun j hj => bank_mono (ready.directory j hj) tapeHi)
  have final := MarkTape.load_run_below generated L.tiles L.work L.first (PurchaseStage.paths L rows)
    L.marks (bank_mono ready.marks tapeWork) (by
      simpa only [PurchaseStage.paths,List.length_ofFn,PurchaseStage.decisionBase] using before)
  simpa only [PurchaseStage.dispatchMemory,PurchaseStage.paths,List.length_ofFn] using final

end Hierarchy.ProtocolRAM.GateAgree

end OAI
