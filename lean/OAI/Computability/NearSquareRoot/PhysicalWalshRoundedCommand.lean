import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution

/-! # Named rounded piece sweep on the physical input trajectory -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space KernelPass PhysicalWalshNode

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

/-- Use the single effective agenda interpreter and the indicated emitted
piece command. Only the constant factors in its clock and arena are chosen. -/
theorem roundedSweepNamed {I : Type} (step : Cmd) (ha : 1<a+1) (b : I → Root)
    (capacity : ∀ i,(b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1))
    (fits : ∀ i,(b i).Feasible hw p ha) (T S : Shape → ℕ)
    (raw : EffectiveBoundedTask.Runs step (fun v : Admissible hw p => T v.val.shape) (fun v => S v.val.shape)
      (fun v => buffer (a+1) v.val.shape v.val.row)
      (fun v => buffer (a+1) v.val.shape (run hw p v.val.shape v.val.row)))
    (clockAt : I → ℕ → ℕ) (arena : I → ℕ)
    (times : ∀ i (j : Fin ((b i).pieces (a:=a) hw).length), T (((b i).pieces hw).get j) ≤
      clockAt i (((b i).pieces hw).get j).level)
    (spaces : ∀ i (j : Fin ((b i).pieces (a:=a) hw).length), S (((b i).pieces hw).get j) ≤ arena i)
    (vol : ∀ i, (b i).size (a:=a) (W:=W)*(4*((b i).w+1)+4)+1 ≤ arena i) :
    ∃ d C : ℕ,
      let G i := C*((b i).k+(b i).s+(b i).w+1)^d+arena i
      let time i := 2*(G i+1) + ∑ j : Fin (walshPieceDigits (a+1) (b i).s).length,
        (walshPieceDigits (a+1) (b i).s).get j * (clockAt i j+G i+1)
      EffectiveBoundedTask.Runs (sweepCmd (a+1) W step) time G (fun i => send (((tally (b i).k,tally (b i).s),tally ((b i).w+1)),
          words ((b i).size (a:=a) (W:=W)) (b i).row))
        (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) := by
  let L (i : I) := (b i).pieces (a:=a) hw
  let X := (i : I) × Fin (L i).length
  have packet (z : X) := reachedPackets hw p ha (b z.1) (capacity _) (fits _) z.2
  let inv (z : X) := (packet z).choose
  have localRun := (raw.on inv).mono (fun z => ((congrArg T (packet z).choose_spec.1).trans_le (times z.1 z.2)))
    (fun z => ((congrArg S (packet z).choose_spec.1).trans_le (spaces z.1 z.2)))
  apply generatedSweepNamed ha hw (fun i => (b i).k) (fun i => (b i).s) (fun i => (b i).w)
    (fun i => (b i).stream hw p) clockAt arena
  · intro i j _; exact ((b i).stream_size hw p j).le.trans (vol i)
  · obtain ⟨C,run⟩ := localRun
    refine ⟨C,fun z env r base reserve => ?_⟩
    have check := run z env r base reserve
    change BoundedFits _ _ (pile 0 (buffer _ (inv z).val.shape (inv z).val.row) _)
      (pile 0 (buffer _ (inv z).val.shape _) _) _ _ _ at check
    simpa only [(packet z).choose_spec.2.1,(packet z).choose_spec.2.2,inv] using check

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
