import OAI.Computability.BorderVNP.TeamTapeInputEntry
import OAI.Computability.BorderVNP.TeamTapeSorting
import OAI.Computability.VPVNP.RAMTapeInputFields

/-! # Routing a processor's interior bits to its physical sort registers

A real owner handles at most two virtual blocks. For each block the routing stream
contains its previous record, sent record, and the Batcher send/receive bits in schedule
order. The cutter stages these disjoint fields while retaining the rest of the stream and
all registers of the processor's initialization and instruction verifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape

/-- Input parser and initialized record buffer, public comparison-bit count, input-cutter
workspaces, and two post-pass banks for the virtual blocks of a single owner. -/
inductive Port where
  | entry (p : TeamTapeInput.Entry.Port)
  | suffixSize
  | work (p : InputPort)
  | post (lane : Bool) (p : SitePost.Port)
  deriving DecidableEq, Fintype

/-- The actual interior link stream retained by the input splitter. -/
abbrev source : Port := .entry (.inl (.cut .incident))

/-- The preserved padded address word also supplies the sorter-word width. -/
abbrev widthSource : Port := .entry (.inr .start)

private abbrev count := Port.work .count
private abbrev scratch := Port.work .tmp

/-- Three serialized fields of one virtual post-pass. -/
inductive Field where
  | previous | sent | comparisons
  deriving DecidableEq

/-- The exact post-pass destination used by the boundary and sorting checks. -/
def Field.sink : Field → SitePost.Port
  | .previous => SitePost.previousPort
  | .sent => SitePost.sentPort
  | .comparisons => SitePost.incidentPort

/-- Width source for a boundary field or comparison payload. -/
def template : Field → Port
  | .previous | .sent => widthSource
  | .comparisons => .suffixSize

/-- A boundary field has five words; a comparison payload uses one bit tally. -/
def copies : Field → ℕ
  | .previous | .sent => 5
  | .comparisons => 1

private def marks (f : Field) : ℕ → FiniteRoutine Port
  | 0 => .ret
  | k+1 => (WordCopy.mapWord scratch count (fun _ => true) (template f)).followedBy (marks f k)

private theorem marks_runs (f : Field) (k : ℕ) (s : Stacks Port) (hs : s scratch = []) :
    (marks f k).Runs (k*(5*(s (template f)).length+2)+1) s
      (Function.update s count (List.replicate (k*(s (template f)).length) true ++ s count)) := by
  induction k generalizing s with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.nil_append, Function.update_eq_self]
    exact Routine.runs_ret s
  | succ k ih =>
    let L := (s (template f)).length
    let mid := Function.update s count (List.replicate L true ++ s count)
    have h₁ : (WordCopy.mapWord scratch count (fun _ => true) (template f)).Runs (5*L+2) s mid := by
      simpa [mid,L,List.map_const'] using WordCopy.mapWord_run scratch count (fun _ => true)
        (by cases f <;> decide : template f ≠ scratch) (by cases f <;> decide) (by decide) s hs
    have h₂ := ih mid (by simpa [mid] using hs)
    have eq : mid (template f) = s (template f) := by cases f <;> rfl
    rw [eq] at h₂
    change (marks f k).Runs (k*(5*L+2)+1) mid
      (Function.update mid count (List.replicate (k*L) true ++ mid count)) at h₂
    change (marks f (k+1)).Runs ((k+1)*(5*L+2)+1) s
      (Function.update s count (List.replicate ((k+1)*L) true ++ s count))
    rw [show (k+1)*(5*L+2)+1 = (5*L+2)+(k*(5*L+2)+1) by ring, Nat.succ_mul k L, List.replicate_add]
    simpa only [marks, mid, Function.update_self, Function.update_idem, List.append_assoc]
      using h₁.followedBy h₂

private def readerPorts (lane : Bool) (f : Field) : InputPort → Port
  | .input => source
  | .header => .post lane f.sink
  | p => .work p

private theorem reader_inj (lane : Bool) (f : Field) : Function.Injective (readerPorts lane f) := by
  intro i j h; cases i <;> cases j <;> simp_all [readerPorts]

/-- Extract one raw field in its original bit order; the sizes of endpoint records are five
times the physical word width. -/
def take (lane : Bool) (f : Field) : FiniteRoutine Port :=
  (marks f (copies f)).followedBy
    ((FiniteRoutine.ofRoutine (InputReader.readField .header)).onPorts (readerPorts lane f))

/-- Full poststate after one extraction. This specifies exactly which two stacks change. -/
def putField (s : Stacks Port) (lane : Bool) (f : Field) (data suffix : List Bool) : Stacks Port :=
  Function.update (Function.update s source suffix) (.post lane f.sink)
    (data ++ s (.post lane f.sink))

/-- Bound-independent run on arbitrary raw bits, including malformed record tags. -/
theorem take_runs (lane : Bool) (f : Field) (s : Stacks Port) (data suffix : List Bool)
    (hin : s source = data ++ suffix) (hlen : data.length = copies f * (s (template f)).length)
    (hc : s count = []) (ht : s scratch = []) :
    (take lane f).Runs (10*data.length+2*copies f+3) s (putField s lane f data suffix) := by
  let mid := Function.update s count (List.replicate data.length true)
  have hm := marks_runs f (copies f) s ht
  rw [← hlen, hc, List.append_nil] at hm
  have hd := InputReader.readField_runs (mid ∘ readerPorts lane f) .header data suffix hin
    (by change mid count = _; exact Function.update_self ..) ht
  have hr : ((FiniteRoutine.ofRoutine (InputReader.readField .header)).onPorts (readerPorts lane f)).Runs
      (5*data.length+2) mid (putField s lane f data suffix) := by
    apply (FiniteRoutine.ofRoutine (InputReader.readField .header)).runs_onPorts_framed (reader_inj lane f) hd
    · intro p; rfl
    · intro p
      cases p <;> simp [putField, InputReader.fieldResult, InputReader.Field.counter, InputReader.Field.output,
        readerPorts, mid, hc]
    · intro p hp
      have h₁ : p ≠ source := fun e => hp .input e.symm
      have h₂ : p ≠ .post lane f.sink := fun e => hp .header e.symm
      have h₃ : p ≠ count := fun e => hp .count e.symm
      simp [putField,mid,h₁,h₂,h₃]
  have he : copies f*(5*(s (template f)).length+2)+1+(5*data.length+2) =
      10*data.length+2*copies f+3 := by rw [hlen]; ring
  simpa only [take, he] using hm.followedBy hr

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
