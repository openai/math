import OAI.Computability.BorderVNP.TeamTapeInputEmitRecord
import OAI.Computability.VPVNP.RAMTapeRoutineTotalPorts
import OAI.Computability.VPVNP.StructuredStackCount

/-! # Emitting the team's time-zero input records

One finite named-stack table consumes a consecutive segment of arbitrary input bits. Each
bit contributes the read of a zero followed by the write of its value at the running global
address. The table preserves already buffered records and returns before the next processor
phase. Its deterministic execution bound is linear in the number of input bits times the
physical word width. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputEmit

open VPVNP BurstRAM RAMTape RAMSerialization

/-- All time-zero probes supplied by this input segment. -/
def probes (w : ℕ) : ℕ → List Bool → List (TeamRecords.Record (Word w))
  | _, [] => []
  | a, b :: bs => probe w a b :: probes w (a+1) bs

/-- Canonical read/write halves in the order emitted. -/
def records (w : ℕ) : ℕ → List Bool → List (WordRecord w)
  | _, [] => []
  | a, b :: bs => half w a b false :: half w a b true :: records w (a+1) bs

/-- Reading back the emitted words recovers exactly the expanded input-initialization
probes at successive addresses. -/
theorem records_decode {w a : ℕ} (bs : List Bool) (hf : 2*(a+bs.length) ≤ 2^w) :
    (records w a bs).map WordRecord.record = (probes w a bs).flatMap TeamRecords.pair := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at hf
    have ha : 2*a+1 < 2^w := by omega
    have hp := TeamTapeSorting.wordPair_decode (probe w a b) ⟨ha, Nat.two_pow_pos w⟩
    rw [← halves_eq_wordPair w a b ha] at hp
    have rest := ih (a := a+1) (by omega)
    simpa only [records, probes, List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] using congrArg₂ (fun l r : List _ => l ++ r) hp rest

@[simp] theorem length_records (w a : ℕ) (bs : List Bool) :
    (records w a bs).length = 2*bs.length := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [records, List.length_cons, ih]; omega

private def step (b : Bool) : FiniteRoutine Port :=
  ((emitHalf false b).followedBy (emitHalf true b)).followedBy (load .advance .increment)

/-- Finite control independent of word width, starting address, and input length. -/
def program : FiniteRoutine Port := .ofRoutine
  (Routine.popLoop Port.bits (fun _ => true) (step false).body (step true).body)

/-- Time allowed for the two staged emissions, one increment, and one input pop per bit. -/
def budget (w count : ℕ) : ℕ := count*(138*w+60)+1

variable {w H a : ℕ} {hw : 2 ≤ w} {bs : List Bool} {rs : List (WordRecord w)} {s : Stacks Port}

private theorem popReady {b : Bool} (ready : Ready hw H a (b :: bs) rs s) :
    Ready hw H a bs rs (Function.update s .bits bs) := by
  exact ⟨Function.update_self .., by simpa using ready.cursor, ready.buffer, ready.fields⟩

private theorem step_runs (ready : Ready hw H a bs rs s) (b : Bool)
    (ha : a < 2^w) (free : rs.length+2 ≤ 4*H) :
    ∃ t out, t ≤ 138*w+59 ∧ (step b).Runs t s out ∧
      Ready hw H (a+1) bs (rs ++ [half w a b false,half w a b true]) out := by
  obtain ⟨t₁,mid,h₁,r₁,m,_⟩ := emitHalf_runs ready ha (by omega) false b
  obtain ⟨t₂,next,h₂,r₂,n,hn⟩ := emitHalf_runs m ha (by simp; omega) true b
  have r₃ := load_runs .advance .increment next (word w a) hn n.buffer.scratch n.buffer.output
  rw [Move.dst, n.cursor, length_wordBits, Op.eval, show (word w a).val = a from Nat.mod_eq_of_lt ha] at r₃
  let out := Function.update next .cursor (BurstRAM.wordBits (word w (a+1)))
  have same : (rs ++ [half w a b false]) ++ [half w a b true] =
      rs ++ [half w a b false,half w a b true] := by simp
  rw [same] at n
  exact ⟨_,out,by omega,(r₁.followedBy r₂).followedBy r₃,
    ⟨by simpa [out] using n.bits, Function.update_self .., n.buffer, n.fields⟩⟩

/-- Starting with an arbitrary admitted prefix, the single table appends the two canonical
initialization halves for each input bit and returns its exact stopping cost. -/
theorem runs (ready : Ready hw H a bs rs s)
    (fits : 2*(a+bs.length) ≤ 2^w) (free : rs.length+2*bs.length ≤ 4*H) :
    ∃ t out, t ≤ budget w bs.length ∧ program.Runs t s out ∧
      Ready hw H (a+bs.length) [] (rs ++ records w a bs) out := by
  induction bs generalizing a rs s with
  | nil =>
    exact ⟨1,s,by simp [budget],Routine.Runs.popLoop_empty Port.bits (fun _ => true)
      (step false).body (step true).body ready.bits, by simpa [records] using ready⟩
  | cons b bs ih =>
    simp only [List.length_cons] at fits free
    obtain ⟨n,mid,hn,hr,hm⟩ := step_runs (popReady ready) b (by omega) (by omega)
    obtain ⟨m,out,ht,htail,hout⟩ := ih hm (by omega) (by simp; omega)
    refine ⟨1+n+m,out,?_,?_,?_⟩
    · unfold budget at ht ⊢
      rw [List.length_cons, Nat.succ_mul bs.length (138*w+60)]; omega
    · exact Routine.Runs.popLoop_continue Port.bits (fun _ => true) (step false).body (step true).body
        ready.bits rfl (by cases b <;> exact hr) htail
    · simpa only [records, List.length_cons, List.append_assoc, List.cons_append, List.nil_append,
        show a+1+bs.length = a+(bs.length+1) by omega] using hout

/-- The deterministic run consumes one path and stops on every bit stream, giving the
residual clock and the appended record buffer to the caller. -/
theorem spec (ready : Ready hw H a bs rs s) (fits : 2*(a+bs.length) ≤ 2^w)
    (free : rs.length+2*bs.length ≤ 4*H) (fuel : ℕ) (enough : budget w bs.length ≤ fuel) :
    ∃ t out, t ≤ budget w bs.length ∧ Ready hw H (a+bs.length) [] (rs ++ records w a bs) out ∧
      (∀ c, program.body.count c fuel s = c (fuel-t) out) ∧
      ∀ c, program.body.AllStops c fuel s ↔ c (fuel-t) out := by
  obtain ⟨t,out,ht,run,ho⟩ := runs ready fits free
  have he : fuel-t+t = fuel := by omega
  exact ⟨t,out,ht,ho,fun c => by simpa only [he] using run.count_eq c (fuel-t),
    fun c => by simpa only [he] using run.allStops_iff c (fuel-t)⟩

end TeamTapeInputEmit

end BorderVNP
end Computability
end OAI
