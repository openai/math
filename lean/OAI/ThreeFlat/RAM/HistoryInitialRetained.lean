import OAI.ThreeFlat.RAM.HistoryInitialSeed
import OAI.ThreeFlat.RAM.HistoryReadyTape

namespace OAI
/-! # The three seed jobs and their retained memory -/

namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalProcedure HistoryReadyTape
open scoped Fin.CommRing

noncomputable section
variable {W : ℕ}

/-- The leaf decoder stream, packed endpoint stream, and cache result stream
have exactly the bounds used in the three control rows. The output words are
indexed by absolute address to agree with the underlying native scan. -/
def jobs (A : Layout) (z : Site) (record endpoint : ℕ→Word W) : List (Job W) :=
  [⟨z.stream A,4*z.rows A,record⟩,⟨z.extBase A,z.extPins,endpoint⟩,
    ⟨z.resultBase A,6,fun a => if h : a-z.resultBase A<6 then
      (z.words A ⟨36+(a-z.resultBase A),by omega⟩ : Word W) else 0⟩]

def mounted (A : Layout) (z : Site) (m : Memory W) :=
  ∀ j : Fin 42,m (A.ctrl+j.val)=(z.words A j : Word W)

set_option maxRecDepth 8000 in
theorem bounds_loaded (A : Layout) (z : Site) (record endpoint : ℕ→Word W)
    (m : Memory W) (loaded : mounted A z m) :
    Loaded (A.ctrl+2) (jobs A z record endpoint) m := by
  intro k
  change Fin 3 at k
  fin_cases k
  · exact ⟨by simpa [Site.words,jobs] using loaded (3:Fin 42),
            by simpa [Site.words,jobs,Job.finish] using loaded (8:Fin 42)⟩
  · exact ⟨by simpa [Site.words,jobs] using loaded (10:Fin 42),
            by simpa [Site.words,jobs,Job.finish] using loaded (15:Fin 42)⟩
  · exact ⟨by simpa [Site.words,jobs] using loaded (17:Fin 42),
            by simpa [Site.words,jobs,Job.finish] using loaded (22:Fin 42)⟩

theorem jobs_cost (z : Site) (A : Layout) (record endpoint : ℕ→Word W) (k : ℕ) :
    cost k (jobs A z record endpoint)=63+(4*z.rows A+z.extPins+6)*(2*k+4) := by
  simp only [jobs,cost]; ring

theorem loaded_of_fill (A : Layout) (z : Site) (m : Memory W) :
    mounted A z (fillSegment A.ctrl 42
       (fun a => if h : a-A.ctrl<42 then (z.words A ⟨a-A.ctrl,h⟩ : Word W) else 0) m) := by
  intro j
  have ij := j.isLt
  simp [fillSegment,show A.ctrl+j.val<A.ctrl+42 by omega,j.isLt]

/-- Only the control address changes while these three jobs execute. The
other 41 words include the numeric operands as well as the operation tags. -/
def Control (A : Layout) (z : Site) (job : ℕ) (m : Memory W) :=
  m A.ctrl=((A.ctrl+2+7*job : ℕ) : Word W) ∧
  ∀ j : Fin 42, 0<j.val → m (A.ctrl+j.val)=(z.words A j : Word W)

theorem Control.start {A : Layout} {z : Site} {m : Memory W} (h : mounted A z m) : Control A z 0 m := by
  refine ⟨?_,fun j _ => h j⟩
  simpa [Site.words] using h 0

theorem Control.preserve {A : Layout} {z : Site} {k : ℕ} {s n : ℕ} {m v : Memory W}
    (h : Control A z k m) (frame : n+s≤A.ctrl ∨ A.ctrl+42≤ s)
    (same : DescriptorScan.agreesOutside s (s+n) v m) : Control A z k v := by
  refine ⟨(same A.ctrl (by omega)).trans h.1,?_⟩
  intro i hi
  have := i.isLt
  exact (same _ (by omega)).trans (h.2 i hi)

theorem Control.next {A : Layout} {z : Site} {k : ℕ} {s n : ℕ} {m : Memory W} (word : ℕ→Word W)
    (h : Control A z k m) (room : A.ctrl<2^W) (frame : n+s≤A.ctrl ∨ A.ctrl+42≤ s) :
    Control A z (k+1) (HistoryJoinController.bumpMemory (A.ctrl : Word W) (fillSegment s n word m)) := by
  have same : DescriptorScan.agreesOutside s (s+n) (fillSegment s n word m) m := by
    intro x outside
    simp [fillSegment,show ¬(s≤x ∧ x<s+n) by omega]
  have keep := h.preserve frame same
  constructor
  · simp [HistoryJoinController.bumpMemory,writeMemory,Fin.val_cast_of_lt room,keep.1,
      Nat.mul_add,Nat.cast_add,Nat.cast_mul]
   ; ring
  · intro j hj
    have nonzero : j ≠ 0 := by
      intro zero
      subst j
      simp at hj
    simp [HistoryJoinController.bumpMemory,writeMemory,Fin.val_cast_of_lt room,nonzero,keep.2 j hj]

/-- Native images have a common high-memory scratch interval, and disjoint
record/endpoint/result intervals. The original trace projection and pair
projection have separate, known operand banks outside those intervals. -/
def Site.scratch (z : Site) (A : Layout) (m : Memory W) := fillSegment A.ctrl 42
  (fun a => if h : a-A.ctrl<42 then (z.words A ⟨a-A.ctrl,h⟩ : Word W) else 0) m

def Site.writes (z : Site) (A : Layout) (a : ℕ) :=
  (A.ctrl≤a ∧ a<A.ctrl+42) ∨ (z.stream A≤a ∧ a<z.stream A+4*z.rows A) ∨
    (z.extBase A≤a ∧ a<z.extBase A+z.extPins) ∨ (z.resultBase A≤a ∧ a<z.resultBase A+6)

def Site.retains (z : Site) (A : Layout) (m source : Memory W) :=
  ∀ a, ¬z.writes A a → m a=source a

theorem Site.retains_scratch (z : Site) (A : Layout) (m : Memory W) : z.retains A (z.scratch A m) m := by
  intro a h; simp only [writes,not_or] at h
  simp [scratch,fillSegment,h.1]

theorem Site.retains_write (z : Site) (A : Layout) (m m' src : Memory W) (s n : ℕ)
    (old : z.retains A m src) (loc : ∀ a, s≤a → a<s+n → z.writes A a)
    (change : DescriptorScan.agreesOutside s (s+n) m' m) : z.retains A m' src := by
  intro a ha
  exact (change a (by by_contra q; exact ha (loc a (by omega) (by omega)))).trans (old a ha)

theorem Site.retains_next (z : Site) (A : Layout) (m src : Memory W) (s n : ℕ) (q : ℕ→Word W)
    (room : A.ctrl<2^W) (old : z.retains A m src) (loc : ∀ a,s≤a → a<s+n → z.writes A a) :
    z.retains A (HistoryJoinController.bumpMemory (A.ctrl:Word W) (fillSegment s n q m)) src := by
  intro a ha
  have h : ¬(s≤a ∧ a<s+n) := fun v => ha (loc a v.1 v.2)
  have neq : a≠A.ctrl := by rintro rfl; exact ha (Or.inl ⟨le_rfl,by omega⟩)
  simp [HistoryJoinController.bumpMemory,writeMemory,Fin.val_cast_of_lt room,neq,fillSegment,h,old a ha]

/-- The exact chronological result of running the native leaf body. -/
def Site.output (z : Site) (A : Layout) (record endpoint : ℕ→Word W) (m : Memory W) :=
  after (A.ctrl:Word W) (jobs A z record endpoint) (z.scratch A m)

end
end ThreeFlat.RAM.HistoryInitialSeed

end OAI
