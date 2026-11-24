import OAI.Computability.VPVNP.PairTerminalSharedBits
import OAI.Computability.VPVNP.PairTraversalControllerMemory
import OAI.Computability.VPVNP.PairSimulationTerminalProgram

/-!
# Readback at the actual entry of the terminal vertex phase

The linked bit stage writes the shared interval and hands off through the two
controller cells. Its physical post-memory carries the selected DFS child rows,
role words and the same bit assignment. Earlier level descriptors and all
noncontrol header fields are still readable by the native vertex interpreter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLayout

open BurstRAM PrivateRAM Compression CompressorRecords TraversalRows TraversalRoles
open scoped Fin.CommRing

open private reads_above from OAI.Computability.VPVNP.PairTraversalRoleExecution

variable {w : ℕ}

private theorem high_offset (h : Word w) (fit : h.val + 32 ≤ 2 ^ w) (j : ℕ) (hj : j < 32) :
    (h+(j : Word w)).val = h.val+j := by
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]

/-- All data read by the DFS and endpoint gather after the linked shared
scan. The range of preserved header fields excludes the two stage controls. -/
theorem linked_vertexMemory (workers : TerminalLink.Stage → LiveProgram.PairTable)
    (bank : workers TerminalLink.Stage.sharedBits = ⟨28, 5, FinalBits.Worker.table⟩)
    (pub : Fin 11 → Word w) (src phy : Memory w) (fuel cap base F : ℕ)
    (roles : List TaggedLayer) (bits : Fin F → Bool)
    (capacity : ∀ L ∈ roles.map TaggedLayer.layer, ∀ i, (L.ids i).length ≤ cap) :
    let ls := roles.map TaggedLayer.layer
    let size := words cap ls
    let lo := base+size
    let H := TerminalLink.header pub
    let stage := TerminalLink.Entry.resume TerminalLink.Stage.sharedBits (0 : Word w)
    let raw := FinalBits.Worker.reports pub 0 src bits
    let linked := TerminalLink.stageReports H stage raw
    let mem := after phy (eventLog linked)
    FinalBits.Worker.Layout pub src lo F → H.val+32 ≤ 2^w → base+2*size+F ≤ H.val →
    54 ≤ fuel → stage.Valid H phy → SourceTransport.Agree (TerminalLink.workerCell H) src phy →
    AllRows w src cap base base ls → Reads w src (size+F) cap base roles →
    TerminalLink.StageRun workers pub fuel stage src phy (FinalBits.calls bits ++ [[]]) raw ∧
      AllRows w mem cap base base ls ∧ Reads w mem (size+F) cap base roles ∧
      (∀ i : Fin F, mem (lo+i) = PrimedInputRAM.encodeBit w (bits i)) ∧
      (∀ x < base, mem x = src x) ∧
      ∀ j : ℕ, 0 < j → j < 31 → mem (H+(j : Word w)).val = src (H+(j : Word w)).val := by
  intro ls size lo H stage raw linked mem layout room above clock valid agree rows tags
  have below : lo+F ≤ H.val := by dsimp only [lo]; omega
  have run := FinalBits.Worker.stageRun workers bank pub src phy layout bits fuel clock room below
    valid agree
  have last : (H+31).val = H.val+31 := high_offset H room 31 (by decide)
  have area (x : ℕ) (hx : x < H.val) : TerminalLink.workerCell H x :=
    ⟨hx.ne,(by omega : x ≠ (H+31).val)⟩
  have low (x : ℕ) (hx : x < lo) : mem x = src x := by
    exact (run.agree x (area x (hx.trans_le (Nat.le_add_right lo F |>.trans below)))).symm.trans
      (FinalBits.Worker.outside pub src layout bits x (Or.inl hx))
  let rawOut := after src (eventLog raw)
  have rawTags : Reads w rawOut (size+F) cap base roles :=
    reads_above tags (fun x hx => FinalBits.Worker.outside pub src layout bits x
      (Or.inr (by change base+size+F ≤ x; omega)))
  refine ⟨run,ControllerMemory.allRows_below ls low le_rfl capacity rows,
    ControllerMemory.reads_below roles (fun x hx => (run.agree x (area x hx)).symm)
      (by change size+F+base+size ≤ H.val; omega) rawTags, ?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    exact (run.agree (lo+i) (area _ (by omega))).symm.trans
      (FinalBits.Worker.readback pub src layout bits i)
  · intro x hx
    exact low x (hx.trans_le (Nat.le_add_right _ _))
  · intro j hj hj'
    have atJ := high_offset H room j (by omega)
    have data : TerminalLink.workerCell H (H+(j : Word w)).val := ⟨by omega,by omega⟩
    exact (run.agree _ data).symm.trans
      (FinalBits.Worker.outside pub src layout bits _ (Or.inr (by omega)))

end PairSimulation.TerminalLayout

end VPVNP
end Computability
end OAI
