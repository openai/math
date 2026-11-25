import OAI.Computability.BorderVNP.FragmentBucketScatterStep

/-! # Stable native scatter into consecutive per-cell triples -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- An address is outside this half-open allocation. -/
def Outside (a size addr : ℕ) : Prop := addr < a ∨ a+size ≤ addr

private theorem outside_of_apart {a n b m i : ℕ} (h : apart a n b m) (hi : i < n) :
    Outside b m (a+i) := by rcases h with h|h <;> unfold Outside <;> omega

/-- All words outside the two scatter destinations retain their initial contents. -/
def Layout.Unchanged (l : Layout) (before after : ℕ → ℕ) : Prop :=
  ∀ addr, Outside l.triples (3*l.rows) addr → Outside l.cursors l.cells addr → after addr = before addr

theorem Layout.Unchanged.input {l : Layout} {tag : Fin l.rows → Fin l.cells} {p : Fin l.rows → Fin 3 → ℕ}
    {before after} {w : ℕ} (h : l.Unchanged before after) (fit : l.Fits w) (input : l.Input tag p before) :
    l.Input tag p after := by
  have eq (i : Fin l.rows) (j : ℕ) (hj : j < 4) :
      after (l.quads+4*i.val+j) = before (l.quads+4*i.val+j) := by
    rw [Nat.add_assoc]
    have lt : 4*i.val+j < 4*l.rows := by have := i.isLt; omega
    exact h _ (outside_of_apart fit.qt lt) (outside_of_apart fit.qc lt)
  refine ⟨fun i => (eq i 0 (by decide)).trans (input.cell i),fun i j => ?_⟩
  rw [Nat.add_assoc,eq i (1+j.val) (by have := j.isLt; omega),← Nat.add_assoc]
  exact input.field i j

private theorem read_other (mem : ℕ → ℕ) (base cursor next addr : ℕ) (p : Fin 3 → ℕ)
    (slot : Outside base 3 addr) (away : addr ≠ cursor) :
    scatterWrites mem base cursor next p addr = mem addr := by
  have h0 : addr ≠ base := by rcases slot with h|h <;> omega
  have h1 : addr ≠ base+1 := by rcases slot with h|h <;> omega
  have h2 : addr ≠ base+2 := by rcases slot with h|h <;> omega
  simp [scatterWrites,Function.update_of_ne,h0,h1,h2,away]

private theorem read_field (mem : ℕ → ℕ) (base cursor next : ℕ) (p : Fin 3 → ℕ)
    (j : Fin 3) (apart : base+j.val ≠ cursor) :
    scatterWrites mem base cursor next p (base+j.val) = p j := by
  fin_cases j <;> simp_all [scatterWrites,Function.update_of_ne]

variable {l : Layout} (tag : Fin l.rows → Fin l.cells) (p : Fin l.rows → Fin 3 → ℕ)

/-- At prefix length i the cell cursor is its exclusive base plus the occurrences
read so far. All earlier physical triples are already at their stable addresses. -/
structure ScatterState (before : ℕ → ℕ) (i : ℕ) (mem : ℕ → ℕ) : Prop where
  cursor : ∀ c : Fin l.cells, mem (l.cursors+c.val) = start tag c.val + prior tag i c
  written : ∀ j : Fin l.rows, j.val < i → ∀ k : Fin 3,
    mem (l.triples+3*(dest tag j).val+k.val) = p j k
  other : l.Unchanged before mem

theorem ScatterState.first {before : ℕ → ℕ} (starts : ∀ c : Fin l.cells, before (l.cursors+c.val) = start tag c.val) :
    ScatterState tag p before 0 before :=
  ⟨fun c => by rw [prior_zero,Nat.add_zero,starts],fun _ h => by omega,fun _ _ _ => rfl⟩

theorem ScatterState.next {w : ℕ} (fit : l.Fits w) (i : Fin l.rows) {before mem : ℕ → ℕ}
    (old : ScatterState tag p before i.val mem) :
    ScatterState tag p before (i.val+1) (scatterWrites mem (l.triples+3*(dest tag i).val) (l.cursors+(tag i).val)
      ((dest tag i).val+1) (p i)) := by
  let dst := (dest tag i).val
  have di : dst < l.rows := (dest tag i).isLt
  have sep (j : Fin l.rows) (k : Fin 3) (c : Fin l.cells) : l.triples+3*j.val+k.val ≠ l.cursors+c.val := by
    rw [Nat.add_assoc]
    exact apart_ne fit.tc (by have := j.isLt; have := k.isLt; omega) c.isLt
  constructor
  · intro c
    rw [prior_step]
    by_cases eq : tag i = c
    · subst c
      simp only [scatterWrites,Function.update_self,ite_true,dest_val]
      omega
    · have neq : l.cursors+c.val ≠ l.cursors+(tag i).val := by
        intro h; exact eq (Fin.ext (Nat.add_left_cancel h).symm)
      have out : Outside (l.triples+3*dst) 3 (l.cursors+c.val) := by
        have h := fit.tc; have hc := c.isLt
        rcases h with h|h <;> unfold Outside <;> omega
      rw [read_other mem _ _ _ _ _ out neq,ite_eq_right eq,Nat.add_zero,old.cursor]
  · intro j hj k
    by_cases eq : j = i
    · subst j; exact read_field mem _ _ _ (p i) k (sep (dest tag i) k (tag i))
    · have ne : (dest tag j).val ≠ dst := by
        intro same; exact eq ((dest tag).injective (Fin.ext same))
      have oldi : j.val < i.val := by have := Fin.val_ne_of_ne eq; omega
      have out : Outside (l.triples+3*dst) 3 (l.triples+3*(dest tag j).val+k.val) := by
        have hk := k.isLt; unfold Outside; omega
      rw [read_other mem _ _ _ _ _ out (sep (dest tag j) k (tag i)),old.written j oldi]
  · intro addr ha hb
    have out : Outside (l.triples+3*dst) 3 addr := by rcases ha with h|h <;> unfold Outside <;> omega
    have away : addr ≠ l.cursors+(tag i).val := by have := (tag i).isLt; rcases hb with h|h <;> omega
    exact (read_other mem _ _ _ _ _ out away).trans (old.other addr ha hb)

/-- Scatter the chronological quadruple directory once, copying only its three
actual words per retained interval and charging one constant per input row. -/
def scatter : Code := forEach 13 3 scatterStep

/-- Native postcondition giving exact stable output, final cursors, the untouched
physical source and every unrelated memory address, including both cell header words. -/
theorem scatter_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (fit : l.Fits w) (s : Bank w) (m : Memory w) (ready : l.Ready (.ofWords s m))
    (input : l.Input tag p (readings m)) (starts : ∀ c : Fin l.cells, readings m (l.cursors+c.val) = start tag c.val) :
    BoundedRun pub macros scatter s m (2+l.rows*(scatterStep.slots+1)) (fun z =>
      l.Ready z ∧ z.reg 0 = (s 0).val ∧ ScatterState tag p (readings m) l.rows z.mem) := by
  let I (i : ℕ) (z : NatState) := l.Ready z ∧ z.reg 13 = i ∧ z.reg 0 = (s 0).val ∧
    ScatterState tag p (readings m) i z.mem
  have init : I 0 ((Code.constant 13 0).fixedEval (readings pub) (.ofWords s m)) := by
    simpa (config := {decide := true}) [I,Layout.Ready,Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using
      And.intro ready (ScatterState.first tag p starts)
  have step (i : Fin l.rows) (t : Bank w) (mt : Memory w) (h : I i.val (.ofWords t mt)) :
      BoundedRun pub macros scatterStep t mt scatterStep.slots (I (i.val+1)) := by
    obtain ⟨rd,idx,r0,prev⟩ := h
    have cursor := (prev.cursor (tag i)).trans (dest_val tag i).symm
    apply (scatterStep_run pub macros l tag p fit i t mt rd idx (prev.other.input fit input) cursor).mono le_rfl
    rintro z ⟨idx',low,mem⟩
    refine ⟨?_,idx',(low 0 (by decide)).trans r0,mem ▸ prev.next tag p fit i⟩
    rcases rd with ⟨a,b,c,d,e,f⟩
    exact ⟨(low 2 (by decide)).trans a,(low 3 (by decide)).trans b,(low 4 (by decide)).trans c,
      (low 5 (by decide)).trans d,(low 6 (by decide)).trans e,(low 7 (by decide)).trans f⟩
  apply (forEach_run pub macros 13 3 scatterStep l.rows scatterStep.slots I s m init
    (fun _ _ h => ⟨h.2.1,h.1.2.1⟩) step).mono le_rfl
  exact fun _ h => ⟨h.1,h.2.2.1,h.2.2.2⟩

end FragmentBucket

end BorderVNP
end Computability
end OAI
