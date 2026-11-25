import OAI.ThreeFlat.Diagonal.TickChronology
import Mathlib.Data.List.FinRange

namespace OAI
/-! # Partitioning all tick times into the scheduled native phases -/

namespace ThreeFlat.Diagonal.TickRangeChronology

open TickChronology

def leadingIdle (c : Clock) := List.ofFn (fun j : Fin (c.beginTick-1) => 1+j.val)
def trailingIdle (c : Clock) := List.ofFn (fun j : Fin (c.last-c.stop) => c.stop+j.val)
def scanTicks (c : Clock) (g : ℕ) := List.ofFn (fun j : Fin c.chunks => c.base g+(1+j.val))
def evalTicks (c : Clock) (g : ℕ) :=
  List.ofFn (fun j : Fin c.evaluateTicks => c.base g+(c.chunks+1+j.val))
def padCount (c : Clock) := c.groupDuration-(c.chunks+c.evaluateTicks+2)
def padTicks (c : Clock) (g : ℕ) :=
  List.ofFn (fun j : Fin (padCount c) => c.base g+(c.chunks+c.evaluateTicks+1+j.val))

def groupTicks (c : Clock) (g : ℕ) :=
  ((([c.base g] ++ scanTicks c g) ++ evalTicks c g) ++ padTicks c g) ++ [c.base g+(c.groupDuration-1)]

def allGroups (c : Clock) := (List.ofFn (fun g : Fin c.groups => groupTicks c g.val)).flatten

private theorem enumerate (s n : ℕ) :
    List.ofFn (fun j : Fin n => s+j.val) = List.range' s n := by
  apply List.ext_getElem
  · simp
  · intro i ha hb
    simp

private theorem single (s : ℕ) : [s] = List.range' s 1 := by simp [List.range'_succ]
private theorem join (s n t k : ℕ) (h : s+n=t) :
    List.range' s n ++ List.range' t k = List.range' s (n+k) := by
  subst t
  exact List.range'_append_1

theorem groupTicks_eq_range (c : Clock) (g : ℕ) :
    groupTicks c g = List.range' (c.base g) c.groupDuration := by
  let b := c.base g
  let p := padCount c
  have cap : 1+c.chunks+c.evaluateTicks+p+1=c.groupDuration := by
    have := c.room
    dsimp [p,padCount]
    omega
  have sc : scanTicks c g = List.range' (b+1) c.chunks := by simpa [scanTicks,b,Nat.add_assoc] using enumerate (b+1) c.chunks
  have ev : evalTicks c g = List.range' (b+c.chunks+1) c.evaluateTicks := by
    simpa [evalTicks,b,Nat.add_assoc] using enumerate (b+c.chunks+1) c.evaluateTicks
  have pad : padTicks c g = List.range' (b+c.chunks+c.evaluateTicks+1) p := by
    simpa [padTicks,b,p,Nat.add_assoc] using enumerate (b+c.chunks+c.evaluateTicks+1) p
  change ((([b] ++ scanTicks c g) ++ evalTicks c g) ++ padTicks c g) ++ [b+(c.groupDuration-1)] = _
  rw [sc,ev,pad,single b,single (b+(c.groupDuration-1)),
    join b 1 _ _ rfl,join b (1+c.chunks) _ _ (by omega),
    join b (1+c.chunks+c.evaluateTicks) _ _ (by omega),
    join b (1+c.chunks+c.evaluateTicks+p) _ _ (by omega),cap]

private theorem grouped_range (s d k : ℕ) :
    (List.range k).flatMap (fun g => List.range' (s+g*d) d) = List.range' s (k*d) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ,List.flatMap_append,ih]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [List.range'_append_1,Nat.succ_mul]

theorem allGroups_eq_range (c : Clock) :
    allGroups c = List.range' c.beginTick (c.groups*c.groupDuration) := by
  have h : List.ofFn (fun g : Fin c.groups => groupTicks c g.val) =
      (List.range c.groups).map (groupTicks c) := by
    apply List.ext_getElem <;> simp
  rw [allGroups,h,← List.flatMap_def]
  rw [show groupTicks c = (fun g => List.range' (c.beginTick+g*c.groupDuration) c.groupDuration) from
    funext (groupTicks_eq_range c)]
  exact grouped_range c.beginTick c.groupDuration c.groups

/-- Every transition number appears exactly once in the concatenation. -/
theorem range_eq_chronology (c : Clock) :
    List.range (c.last+1) = ((([0] ++ leadingIdle c) ++ allGroups c) ++ trailingIdle c) ++ [c.last] := by
  have hb := c.begin_pos
  have he : c.stop ≤ c.last := c.fits
  symm
  rw [leadingIdle,trailingIdle,enumerate,enumerate,allGroups_eq_range,single 0,single c.last,
    join 0 1 1 _ rfl,join 0 (1+(c.beginTick-1)) c.beginTick _ (by omega),
    join 0 (1+(c.beginTick-1)+c.groups*c.groupDuration) c.stop _ (by unfold Clock.stop; omega),
    join 0 (1+(c.beginTick-1)+c.groups*c.groupDuration+(c.last-c.stop)) c.last 1 (by unfold Clock.stop at *; omega)]
  rw [List.range_eq_range']
  congr 1
  unfold Clock.stop at *
  omega

theorem phase_leadingIdle (c : Clock) {t : ℕ} (h : t ∈ leadingIdle c) : c.phase t = .idle := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  have hj := j.isLt
  have endAt := c.fits
  have hp := c.begin_pos
  change j.val < c.beginTick-1 at hj
  simp [Clock.phase,show 1+j.val ≠ c.last by omega,
    show 1+j.val < c.beginTick by omega]

theorem phase_trailingIdle (c : Clock) {t : ℕ} (h : t ∈ trailingIdle c) : c.phase t = .idle := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  have hj := j.isLt
  have lo : c.beginTick ≤ c.stop := Nat.le_add_right _ _
  have hp := c.begin_pos
  change j.val < c.last-c.stop at hj
  simp [Clock.phase,show c.stop+j.val ≠ c.last by omega,
    show ¬c.stop+j.val < c.beginTick by omega,show ¬c.stop+j.val < c.stop by omega]; omega

theorem phase_scanTicks (c : Clock) {g t : ℕ} (hg : g < c.groups) (h : t ∈ scanTicks c g) :
    c.phase t = .scan := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  exact c.scan hg j.isLt

theorem phase_evalTicks (c : Clock) {g t : ℕ} (hg : g < c.groups) (h : t ∈ evalTicks c g) :
    c.phase t = .evaluate := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  exact c.evaluate hg j.isLt

theorem phase_padTicks (c : Clock) {g t : ℕ} (hg : g < c.groups) (h : t ∈ padTicks c g) :
    c.phase t = .idle := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
  have hj := j.isLt
  change j.val < c.groupDuration-(c.chunks+c.evaluateTicks+2) at hj
  have room := c.room
  let o := c.chunks+c.evaluateTicks+1+j.val
  have bound : o < c.groupDuration-1 := by dsimp [o]; omega
  change c.phase (c.base g+o) = .idle
  rw [(c.in_group hg (show o < c.groupDuration by omega)).1]
  simp [Clock.within,o,show ¬c.chunks+c.evaluateTicks+1+j.val < c.chunks+1 by omega,
    show ¬c.chunks+c.evaluateTicks+1+j.val < c.chunks+c.evaluateTicks+1 by omega,
    show c.chunks+c.evaluateTicks+1+j.val ≠ c.groupDuration-1 from bound.ne]

end ThreeFlat.Diagonal.TickRangeChronology

end OAI
