import OAI.Computability.BorderVNP.TeamPublicWords

/-! # Public RAM registers from the remaining literal bits

The retained physical start-address word has one extra high bit for the paired sorting
records. The startup measures that word and drops one width marker before decoding the
public register bank. The rest of the literal remains available to the routing parser.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPublicStartup

open VPVNP VPVNP.RAMTape VPVNP.BurstRAM

variable {w k : ℕ}

/-- Existing entry workspace and the logical public operand workspace. -/
abbrev Port (k : ℕ) := TeamTapeInput.Entry.Port ⊕ TeamPublicWords.Port k

private abbrev peek : Port k := .inl (.inl (.peek .input))
private abbrev start : Port k := .inl (.inr .start)
private abbrev width : Port k := .inr .width
private abbrev tmp : Port k := .inr .tmp

/-- The logical public-word reader consumes the literal remainder. -/
def readPort : TeamPublicWords.Port k → Port k
  | .input => peek
  | p => .inr p

private theorem read_injective : Function.Injective (readPort (k := k)) := by
  intro a b h; cases a <;> cases b <;> simp_all [readPort]

private def removeMarker : FiniteRoutine (Port k) :=
  FiniteRoutine.ofRoutine (Routine.popCase width (Routine.halt false) (Routine.halt false) Routine.ret)

/-- Measure the retained physical address width and decode each fixed public register. -/
def program (k : ℕ) : FiniteRoutine (Port k) :=
  ((WordCopy.mapWord tmp width (fun _ => true) start).followedBy removeMarker).followedBy
    ((TeamPublicWords.program k).onPorts readPort)

/-- The output of the fixed physical public-operand loader. -/
def loaded (s : Stacks (Port k)) (pub : Fin k → Word w) (tail : List Bool) : Stacks (Port k)
  | .inl (.inl (.peek .input)) => tail
  | .inr .width => List.replicate w true
  | .inr (.pub i) => wordBits (pub i)
  | p => s p

/-- The loader reads its actual logical word width from the already decoded physical start
word. It consumes exactly the contiguous public fields and preserves the record buffer,
routing stream and all unrelated workspace. -/
theorem runs (s : Stacks (Port k)) (pub : Fin k → Word w) (tail : List Bool)
    (hs : (s start).length = w+1) (hi : s peek = TeamPublicWords.bytes pub ++ tail)
    (hw : s width = []) (ht : s tmp = []) (hp : ∀ i, s (.inr (.pub i)) = []) :
    (program k).Runs ((5*(w+1)+2+2) + (k*(6*w+2)+1)) s (loaded s pub tail) := by
  let marked := Function.update s width (List.replicate (w+1) true)
  let ready := Function.update s width (List.replicate w true)
  have measure : (WordCopy.mapWord tmp width (fun _ => true) start).Runs (5*(w+1)+2) s marked := by
    simpa only [hs, hw, marked, List.map_const', List.reverse_replicate, List.append_nil] using
      WordCopy.mapWord_run tmp width (fun _ => true) (show (start : Port k) ≠ tmp from by intro e; cases e)
        (by intro e; cases e) (by intro e; cases e) s ht
  have marker : marked width = true :: List.replicate w true := by simp [marked, List.replicate_succ]
  have one : (removeMarker (k := k)).Runs 2 marked ready := by
    change (Routine.popCase width (Routine.halt false) (Routine.halt false) Routine.ret).Runs 2 marked ready
    simpa only [marked, ready, Function.update_idem] using
      Routine.runs_popCase_true width (Routine.halt false) (Routine.halt false) Routine.ret marker
        (Routine.runs_ret (Function.update marked width (List.replicate w true)))
  let small := ready ∘ readPort
  have smallRun := TeamPublicWords.runs small pub tail (by simpa [small, ready, readPort] using hi)
    (by simp [small, ready, readPort]) (by simpa [small, ready, readPort] using ht)
    (fun i => by simpa [small, ready, readPort] using hp i)
  have read : ((TeamPublicWords.program k).onPorts readPort).Runs (k*(6*w+2)+1) ready (loaded s pub tail) := by
    apply (TeamPublicWords.program k).runs_onPorts_framed read_injective smallRun (fun _ => rfl)
    · intro p; cases p <;> simp [small, loaded, readPort, ready]
    · intro p h
      have hn := Ne.symm (h .input)
      have hwidth := Ne.symm (h .width)
      have hpub (i) := Ne.symm (h (.pub i))
      rcases p with p | p
      · rcases p with p | p
        · rcases p with p | p | _ | _ | _ <;> first | cases p <;> simp_all [readPort, loaded, ready, peek, width] | simp [loaded, ready]
        · rfl
      · cases p <;> simp_all [readPort, loaded, ready, peek, width]
  exact (measure.followedBy one).followedBy read

end TeamPublicStartup

end BorderVNP
end Computability
end OAI
