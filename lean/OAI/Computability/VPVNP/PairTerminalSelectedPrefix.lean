import OAI.Computability.VPVNP.PairTerminalQuietPrefix
import OAI.Computability.VPVNP.PairTerminalSharedBits
import OAI.Computability.VPVNP.PairTraversalControllerMemory

/-!
# Three forced terminal phases on an actual compressed branch

The physical level directories determine the complete deterministic prefix of
the terminal program. The returned block sequence ends with the selected DFS
rows and role tags available for the shared-bit and vertex interpreters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM Compression CompressorRecords TerminalLink TerminalPrefix.Linked
open TraversalRows TraversalRoles TraversalControllerInputs DirectoryRun LocalHistory
open scoped Fin.CommRing

variable {w lanes : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)

/-- Native construction and readback of the deterministic part of the actual
terminal program. The selected placement witnesses are read from the retained
level directories on the same memory where the preceding prefix scan ended. -/
theorem selectedQuietPrefix (workers : Stage → LiveProgram.PairTable) (pub : Fin 11 → Word w)
    (cap fuel base H first pitch : ℕ) (inc : IncidenceDirectory w) (starts : Word w)
    (input : Memory w) (boot : Report w) (prefixRows : List (Report w))
    (bank : workers Stage.traversalRows = ⟨_, _, TraversalController.Native.table⟩)
    (clock₀ : fuel + 30 ≤ cap) (clock₁ : 60 ≤ cap)
    (clock₂ : TraversalController.callFuel B.recordLimit + 30 ≤ cap) :
    let Y := (B.execute f hf T hT X).finalState z
    let src := prefixMemory pub input boot prefixRows
    let ls := selectedLayers B f hf T hT X z
    let size := words B.recordLimit ls
    let off := size+Y.totalWidth
    let vs := executeLevels B f hf T hT X z
    let tags := selected B f hf T hT X z
    let arena := build B.recordLimit base base ls (writeTags off B.recordLimit base tags src)
    Start workers pub cap fuel Y inc starts input boot prefixRows →
    ∀ ds : (i : Fin vs.length) → LevelDirectory vs[i] src base,
      Resident pub src H first pitch off B.recordLimit base ⟨leafLayer (siteOrder X),.cursor⟩
        (levelFibers vs ds) →
      (∀ j ≤ vs.length, first+j*pitch+28 ≤ base) →
      base+2*size+Y.totalWidth ≤ H → 2*tags.length*(X.positions+1) < 2^w →
      ∃ q : QuietPrefix workers pub cap input,
        let ready := q.traversalRows.val.memory
        q.boot.val.choices = [[]] ∧
        q.prefixRows.val.choices = List.replicate (TerminalPrefix.arcCount Y+1) [] ∧
        q.traversalRows.val.choices =
          List.replicate (2*(ls.map Layer.count).sum+2*tags.length+1) [] ∧
        SourceTransport.Agree (workerCell (header pub)) arena ready ∧
        (Entry.resume Stage.sharedBits (0 : Word w)).Valid (header pub) ready ∧
        AllRows w ready B.recordLimit base base ls ∧ Reads w ready off B.recordLimit base tags ∧
        (∀ x < base, ready x = src x) ∧
        ∀ j : ℕ, 0 < j → j < 31 → ready (H+j) = src (H+j) := by
  intro Y src ls size off vs tags arena start ds resident heads below ordinal
  obtain ⟨ts,rs,out,_,_,seg,_,_,tagOK,rowOK,low,_,reads,_⟩ :=
    TraversalController.selected_run_with_reads B f hf T hT X z base src ds pub Y.totalWidth
      H first pitch resident heads below ordinal
  have wide : 32 ≤ 2^w := by have := resident.headerFits; omega
  obtain ⟨q,h₀,h₁,h₂,_,agree,valid⟩ := quietPrefixOfRows start clock₀ clock₁ wide bank
    B.recordLimit _ _ arena out clock₂ seg reads
  let ready := q.traversalRows.val.memory
  have head : (header pub).val = H := by
    change (terminalHead pub).val = H
    rw [resident.header,Fin.val_natCast,Nat.mod_eq_of_lt (by have := resident.headerFits; omega)]
  have last : (header pub + 31).val = H+31 := by
    change ((header pub).val+31%(2^w))%(2^w) = _
    rw [head,Nat.mod_eq_of_lt (by omega : 31 < 2^w),
      Nat.mod_eq_of_lt (by have := resident.headerFits; omega)]
  have data (x : ℕ) (hx : x < H) : workerCell (header pub) x := ⟨by omega,by omega⟩
  have equal : ControllerMemory.AgreeBelow H ready (after src (eventLog out)) := by
    intro x hx
    exact (agree x (data x hx)).symm.trans (congrFun seg.memory.symm x)
  have tagSize : tagWords B.recordLimit tags = size := by
    rw [tagWords, show tags.map TaggedLayer.layer = ls from selected_layers B f hf T hT X z]
  refine ⟨q,h₀,h₁,h₂,agree,valid,ControllerMemory.allRows_below ls equal (by omega)
    (selected_capacity B f hf T hT X z) rowOK,
    ControllerMemory.reads_below tags equal (by rw [tagSize]; dsimp only [off]; omega) tagOK,
    fun x hx => (equal x (hx.trans_le (by omega))).trans (low x hx),?_⟩
  intro j hj hj'
  have high : workerCell (header pub) (H+j) := ⟨by omega,by omega⟩
  apply (agree _ high).symm.trans
  change build B.recordLimit base base ls (writeTags off B.recordLimit base tags src) _ = _
  rw [← show tags.map TaggedLayer.layer = ls from selected_layers B f hf T hT X z]
  simpa only [tagSize,off] using
    TerminalLayout.arena_above B.recordLimit base Y.totalWidth tags src (H+j)
      (by rw [tagSize]; omega)

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
