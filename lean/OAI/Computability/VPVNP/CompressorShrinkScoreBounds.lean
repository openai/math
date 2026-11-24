import OAI.Computability.VPVNP.CompressorShrinkScoreWalk
import OAI.Computability.VPVNP.CompressorSourceOnline

/-! # Memory footprints and cursor progress of the ten score stages -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScorePackets

open BurstRAM SourceTransport SourceOnline TermScores Compression
open scoped Classical Fin.CommRing

variable {w : ℕ} (T : Tables w) (n : ℕ)

/-- Physical address information used by every score visit. -/
structure Region : Prop where
  one : 1 < 2^w
  rows : n < 2^w
  counters : ∀ l, T.termBase.val ≤ (counter T l).val
  level : T.termBase.val ≤ T.levelCell.val
  repetitions : ∀ i < n, T.termBase.val ≤ (TermScores.repetitions T (word i)).val
  payload : ∀ j : Fin 8, ∀ i < n, T.termBase.val ≤ (TermScores.payload T (SelectedScore.axes j) (word i)).val

theorem Region.selected {a g : ℕ} (X : State a (packingLaneBits a g)) (term stride selectors : Word w)
    (wide : 10 ≤ stride.val) (fit : SelectedArena.Fits X term stride) :
    Region (SelectedArena.scoreTables X term stride selectors) (SelectedArena.motifs X) := by
  let L := SelectedArena.scoreTables X term stride selectors
  let N := SelectedArena.motifs X
  let endRows := term.val+N*stride.val
  have room : endRows+2 < 2^w := by
    change endRows+3+_+_ < 2^w at fit; omega
  have base : L.scoreBase.val = endRows := by
    change endRows % (2^w) = endRows
    exact Nat.mod_eq_of_lt (by omega)
  have le : N ≤ N*stride.val := Nat.le_mul_of_pos_right _ (by omega)
  have row (i : ℕ) (hi : i < N) : i*stride.val + stride.val ≤ N*stride.val := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right stride.val hi
  have hs : L.termBase.val = term.val := rfl
  have st : L.termStride.val = stride.val := rfl
  have hEnd : endRows = term.val+N*stride.val := rfl
  refine ⟨by omega,by omega,?_,?_,?_,?_⟩
  · intro l
    have hl : l.toNat ≤ 1 := by cases l <;> decide
    change term.val ≤ (counter L l).val
    rw [counter,Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,base,Nat.mod_eq_of_lt (by omega)]
    omega
  · change term.val ≤ (endRows+2)%(2^w)
    rw [Nat.mod_eq_of_lt room]; omega
  · intro i hi
    have h := row i hi
    change term.val ≤ (TermScores.repetitions L _).val
    rw [repetitions_val L (by rw [hs,st]; omega),hs]; omega
  · intro j i hi
    have h := row i hi
    have hc : (SelectedScore.axes (w := w) j).coordinate.val ≤ j.val := Nat.mod_le ..
    change term.val ≤ (TermScores.payload L _ _).val
    rw [payload_val L _ (by rw [hs,st]; have := j.isLt; omega),hs]; omega

/-- Exclusive stopping cursor for a score visit. Each axis scans `n` motif rows, while clearing
and comparison each take one call. -/
def Stage.limit (n : ℕ) : Stage → ℕ | .axis _ => n | _ => 1

private theorem worker_access (region : Region T n) (j : Fin 8) (mem : Memory w) (k : ℕ) (hk : k < n) :
    Reads (T.termBase.val ≤ ·) (workerReport T (SelectedScore.axes j) mem (word k)).events ∧
      Writes (T.termBase.val ≤ ·) (workerReport T (SelectedScore.axes j) mem (word k)).events := by
  constructor
  · intro a v ha
    simp only [workerReport,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.read.injEq,and_false,or_false,false_or] at ha
    rcases ha with (⟨rfl,_⟩ | ⟨rfl,_⟩) | ⟨rfl,_⟩
    exacts [region.repetitions _ hk,region.payload _ _ hk,region.counters _]
  · intro a v ha
    simp only [workerReport,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.write.injEq,and_false,or_false,false_or] at ha
    obtain ⟨rfl,_⟩ := ha
    exact region.counters _

open private word_succ from OAI.Computability.VPVNP.CompressorRecordTermScores

private theorem axis_progress (region : Region T n) (j : Fin 8) (left k : ℕ) (endAt : k+left=n)
    (mem : Memory w) (rs : List (Report w))
    (run : runSegment (workerMachine T (SelectedScore.axes j)).program 27 (some (word k)) mem
      (List.replicate left []) = some rs) :
    Progress (word n) (word k) rs ∧ Reads (T.termBase.val ≤ ·) (eventLog rs) ∧
      Writes (T.termBase.val ≤ ·) (eventLog rs) := by
  induction left generalizing k mem rs with
  | zero =>
    have e : [] = rs := Option.some.inj run
    subst rs
    rw [Nat.add_zero] at endAt
    subst k
    exact ⟨.done le_rfl,by simp [Reads,eventLog],by simp [Writes,eventLog]⟩
  | succ left ih =>
    have hk : k < n := by omega
    have active : word (w := w) k < word n := Fin.lt_def.mpr (by
      change k%(2^w)<n%(2^w)
      rw [Nat.mod_eq_of_lt (hk.trans region.rows),Nat.mod_eq_of_lt region.rows]; exact hk)
    let head := workerReport T (SelectedScore.axes j) mem (word k)
    rw [List.replicate_succ,runSegment,execute_worker] at run
    obtain ⟨tail,ht,rfl⟩ := Option.map_eq_some_iff.mp run
    change runSegment _ _ (some (word k+1)) (after mem head.events) (List.replicate left []) = some tail at ht
    rw [word_succ] at ht
    obtain ⟨prog,rd,wr⟩ := ih (k+1) (by omega) _ tail ht
    have acc := worker_access T n region j mem k hk
    exact ⟨.next active (congrArg some (word_succ k)) prog,
      fun a v hv => (List.mem_append.mp hv).elim (acc.1 a v) (rd a v),
      fun a v hv => (List.mem_append.mp hv).elim (acc.2 a v) (wr a v)⟩

theorem Native.bounds (region : Region T n) (j : Stage) (mem : Memory w) (rs : List (Report w))
    (h : Native T n j mem rs) : Progress (word (j.limit n)) 0 rs ∧
    Reads (T.termBase.val ≤ ·) (eventLog rs) ∧ Writes (T.termBase.val ≤ ·) (eventLog rs) := by
  have pos : (0 : Word w) < 1 := Fin.lt_def.mpr (by
    change 0 < 1%(2^w); rw [Nat.mod_eq_of_lt region.one]; decide)
  have h₀ : T.termBase.val ≤ T.scoreBase.val := (counter_false T) ▸ region.counters false
  have h₁ : T.termBase.val ≤ (T.scoreBase+1).val := region.counters true
  cases j with
  | axis j => exact axis_progress T n region j n 0 (Nat.zero_add _) mem rs h
  | clear =>
    subst rs
    refine ⟨.next pos rfl (.done le_rfl),?_,?_⟩
    · simp [Reads,eventLog,advance,clearReport]
    · intro a v ha
      simp [eventLog,advance,clearReport] at ha
      rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> assumption
  | compare =>
    subst rs
    refine ⟨.next pos rfl (.done le_rfl),?_,?_⟩
    · intro a v ha
      simp [eventLog,advance,compareReport] at ha
      rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> assumption
    · intro a v ha
      simp [eventLog,advance,compareReport] at ha
      obtain ⟨rfl,_⟩ := ha; exact region.level

private theorem Native.writes_walk {stages : List Stage} {mem : Memory w} {rs : List (Report w)}
    (region : Region T n) (h : SourceWalk (Native T n) stages mem rs) :
    Writes (T.termBase.val ≤ ·) (eventLog rs) := by
  induction h with
  | done => simp [Writes,eventLog]
  | next head _ ih =>
    have wr := (head.bounds T n region _ _ _).2.2
    intro a v ha
    rw [eventLog,List.flatMap_append] at ha
    exact (List.mem_append.mp ha).elim (wr a v) (ih a v)

/-- The actual score run leaves the old level header and every earlier
allocation untouched. -/
theorem score_frame (mem : Memory w) (rs : List (Report w))
    (execute : TermScores.run T n (List.ofFn SelectedScore.axes) mem = some rs)
    (region : Region T n) (x : ℕ) (hx : x < T.termBase.val) :
    after mem (eventLog rs) x = mem x := by
  obtain ⟨logs,hw,he⟩ := walk T n mem rs execute
  rw [← he]
  exact after_outside mem (Native.writes_walk T n region hw) (Nat.not_le_of_lt hx)

end CompressorRecords.ScorePackets

end VPVNP
end Computability
end OAI
