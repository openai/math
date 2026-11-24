import OAI.Computability.VPVNP.CompressionState
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Local histories of placed wire kernels

A term of (7.1) sends each complete old vertex to one new vertex. At a fixed
new vertex the recursive expansion visits precisely this placement fiber and
its local maps and fields. For a selected sequence of terms, Theorem 7.1 bounds
both the occurrence count and the largest field or individual map-entry degree
by exponentiating a constant per compressor block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

open scoped Classical

/-- The field and map occurrences of a kernel at one site, with their bit lengths
and monomial degree bounds. Occurrences can have equal lengths or identical values. -/
structure SiteRecords where
  /-- Finite index type of individual bit-field occurrences recorded for a kernel at one output
  site. -/
  Field : Type
  fieldFintype : Fintype Field
  /-- Length in bits of each recorded field occurrence at the site. -/
  width : Field → ℕ
  /-- Finite index type of local map occurrences recorded for a kernel at one output site. -/
  Map : Type
  mapFintype : Fintype Map
  /-- Monomial degree bound attached to each recorded local map occurrence, controlling its
  individual entries. -/
  degree : Map → ℕ

attribute [instance] SiteRecords.fieldFintype SiteRecords.mapFintype

/-- Count the vertex itself and all its immediate map and field occurrences. -/
def SiteRecords.count (r : SiteRecords) : ℕ := 1 + Fintype.card r.Map + Fintype.card r.Field

/-- The largest field length or degree of an individual map entry at this site. -/
noncomputable def SiteRecords.largest (r : SiteRecords) : ℕ :=
  max (Finset.univ.sup r.width) (Finset.univ.sup r.degree)

theorem SiteRecords.width_le_largest (r : SiteRecords) (f : r.Field) : r.width f ≤ r.largest :=
  (Finset.le_sup (f := r.width) (Finset.mem_univ f)).trans (le_max_left _ _)

theorem SiteRecords.degree_le_largest (r : SiteRecords) (j : r.Map) : r.degree j ≤ r.largest :=
  (Finset.le_sup (f := r.degree) (Finset.mem_univ j)).trans (le_max_right _ _)

variable {k : Type*} {N Y : Network}

/-- The same finite placement fiber occurs in `Term.pushWitness`. -/
abbrev Term.Preimage (t : Term k N) (v : t.output.Site) := {u : N.Site // v = t.place u}

/-- A new vertex visits all local records and each old history in its own fiber once. -/
noncomputable def Term.pushHistorySize (t : Term k N) (rec : t.output.Site → SiteRecords)
    (previous : N.Site → ℕ) (v : t.output.Site) : ℕ :=
  (rec v).count + ∑ u : t.Preimage v, previous u.val

theorem Term.pushHistorySize_le (t : Term k N) (rec : t.output.Site → SiteRecords)
    (previous : N.Site → ℕ) {M : ℕ} (hM : 1 ≤ M) (hp : ∀ u, previous u ≤ M)
    (v : t.output.Site) : t.pushHistorySize rec previous v ≤
      ((rec v).count + Fintype.card (t.Preimage v)) * M := by
  rw [Nat.add_mul]
  apply Nat.add_le_add (Nat.le_mul_of_pos_right _ hM)
  calc
    _ ≤ ∑ _ : t.Preimage v, M := Finset.sum_le_sum fun u _ => hp u.val
    _ = _ := by simp

/-- One selected branch with its actual terms, placements and records. -/
inductive TermChain (k : Type*) : Network → Network → Type _
  | done (N : Network) : TermChain k N N
  | more {N Y : Network} (t : Term k N) (rec : t.output.Site → SiteRecords)
      (tail : TermChain k t.output Y) : TermChain k N Y

namespace TermChain

/-- Number of selected kernel terms along the branch from the initial network to the final
network. -/
def length {N Y : Network} : TermChain k N Y → ℕ
  | .done _ => 0
  | .more _ _ tail => tail.length + 1

/-- Count occurrences of the initial vertices and subsequent local records at each final site. -/
noncomputable def occurrences {N Y : Network} (chain : TermChain k N Y) (initial : N.Site → ℕ) : Y.Site → ℕ :=
  match chain with
  | .done _ => initial
  | .more t rec tail => tail.occurrences (t.pushHistorySize rec initial)

/-- The next length bound includes every field and degree at every output site. -/
noncomputable def largest {V : Type} [Fintype V] (rec : V → SiteRecords) : ℕ :=
  Finset.univ.sup fun v => (rec v).largest

/-- Maximum over the initial stage and all intermediate stages on this branch. -/
noncomputable def peak {N Y : Network} : TermChain k N Y → ℕ → ℕ
  | .done _, W => W
  | .more _ rec tail, W => max W (tail.peak (largest rec))

theorem le_peak (chain : TermChain k N Y) (W : ℕ) : W ≤ chain.peak W := by
  cases chain with
  | done => exact le_rfl
  | more => exact le_max_left _ _

/-- Every bit field and every individual map entry on every intermediate level. -/
def AllRecordsLe {N Y : Network} : TermChain k N Y → ℕ → Prop
  | .done _, _ => True
  | .more _ rec tail, B =>
      (∀ v f, (rec v).width f ≤ B) ∧ (∀ v j, (rec v).degree j ≤ B) ∧ tail.AllRecordsLe B

theorem allRecordsLe_of_peak (chain : TermChain k N Y) {W B : ℕ} (h : chain.peak W ≤ B) :
    chain.AllRecordsLe B := by
  induction chain generalizing W with
  | done => trivial
  | more t rec tail ih =>
    have ht : tail.peak (largest rec) ≤ B := (le_max_right _ _).trans h
    have hl (v : t.output.Site) : (rec v).largest ≤ B :=
      (Finset.le_sup (f := fun u => (rec u).largest) (Finset.mem_univ v)).trans
        ((tail.le_peak _).trans ht)
    exact ⟨fun v f => ((rec v).width_le_largest f).trans (hl v),
      fun v j => ((rec v).degree_le_largest j).trans (hl v), ih ht⟩

/-- Local bounds used at every substep. `W` is a bound on its incoming fields.
The next substep uses the actual largest field or degree from this one. -/
def Bounded (C : ℕ) {N Y : Network} : TermChain k N Y → ℕ → Prop
  | .done _, _ => True
  | .more t rec tail, W =>
      (∀ v, (rec v).count + Fintype.card (t.Preimage v) ≤ C) ∧
      largest rec + 1 ≤ C * (W + 1) ∧ tail.Bounded C (largest rec)

/-- Iteration bounds both the number of operations at each final site and the
largest field or single-entry degree reached anywhere on the selected branch. -/
theorem growth {C W M : ℕ} (chain : TermChain k N Y) (hC : 1 ≤ C)
    (hb : chain.Bounded C W) (initial : N.Site → ℕ) (hM : 1 ≤ M) (hi : ∀ u, initial u ≤ M) :
    (∀ v, chain.occurrences initial v ≤ C ^ chain.length * M) ∧
    chain.peak W + 1 ≤ C ^ chain.length * (W + 1) := by
  induction chain generalizing W M with
  | done => simp [occurrences, length, peak, hi]
  | more t rec tail ih =>
    obtain ⟨hc, hw, ht⟩ := hb
    have hcM : 1 ≤ C * M := Nat.mul_le_mul hC hM
    have hp (v : t.output.Site) : t.pushHistorySize rec initial v ≤ C * M :=
      (t.pushHistorySize_le rec initial hM hi v).trans (Nat.mul_le_mul_right _ (hc v))
    obtain ⟨hcount, hpeak⟩ := ih ht _ hcM hp
    constructor
    · intro v
      simpa only [occurrences, length, pow_succ, Nat.mul_assoc] using hcount v
    · simp only [peak, length, ← max_add_add_right, max_le_iff, pow_succ, Nat.mul_assoc]
      constructor
      · exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.pow_pos hC) hC) |>.trans_eq (Nat.mul_assoc ..)
      · exact hpeak.trans (Nat.mul_le_mul_left _ hw)

/-- A block with at most `s` elementary substeps costs a fixed factor `C^s`.
The constant in Theorem 7.1 is uniform in the number of blocks and the branch. -/
theorem blockGrowth {C W s T : ℕ} (chain : TermChain k N Y) (hC : 1 ≤ C)
    (hb : chain.Bounded C W) (hlen : chain.length ≤ s * T) :
    (∀ v, chain.occurrences (fun _ => 1) v ≤ (C ^ s) ^ T) ∧
      chain.peak W + 1 ≤ (C ^ s) ^ T * (W + 1) := by
  obtain ⟨hc, hw⟩ := chain.growth hC hb (fun _ => 1) (M := 1) le_rfl (fun _ => le_rfl)
  have hpow : C ^ chain.length ≤ (C ^ s) ^ T := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hC hlen
  exact ⟨fun v => (by simpa using hc v : _ ≤ C ^ chain.length).trans hpow,
    hw.trans (Nat.mul_le_mul_right _ hpow)⟩

end TermChain
end NetworkKernel

namespace Compression

open NetworkKernel
open scoped Classical

variable {a b g n : ℕ}

/-- The largest actual wire width of a lifted state. -/
noncomputable def State.maxWireWidth (X : State a g) : ℕ := Finset.univ.sup X.width

theorem State.width_le_maxWireWidth (X : State a g) (e) : X.width e ≤ X.maxWireWidth :=
  Finset.le_sup (f := X.width) (Finset.mem_univ e)

variable {R : Type*} [CommSemiring R] {X : State a g}

/-- A substep supplies its local records on every branch, even when its topology
and placement depend on the selected terms. -/
abbrev StatePass.Records (p : StatePass R X b n) :=
  (i : p.step.Choice) → (p.step.term i).output.Site → SiteRecords

/-- The substep count and width estimates needed by the history recursion. -/
def StatePass.Bounded (p : StatePass R X b n) (rec : p.Records) (C : ℕ) : Prop :=
  ∀ i, (∀ v, (rec i v).count + Fintype.card ((p.step.term i).Preimage v) ≤ C) ∧
    TermChain.largest (rec i) + 1 ≤ C * (X.maxWireWidth + 1) ∧
    (p.next i).maxWireWidth ≤ TermChain.largest (rec i)

namespace StateExecution

/-- Local site records for every pass and each branch-dependent continuation of the execution,
with the unit record at a terminal state. -/
def Records {a g : ℕ} {X : State a g} : StateExecution R b n X → Type 1
  | .done _ => PUnit
  | .more p tail => p.Records × ((i : p.step.Choice) → (tail i).Records)

/-- The recursive data contains exactly the terms selected by this execution path. -/
noncomputable def termChain {a g : ℕ} {X : State a g} (E : StateExecution R b n X) :
    E.Records → (z : E.Choices) → TermChain R X.network (E.finalState z).network :=
  match E with
  | .done _ => fun _ _ => .done _
  | .more p tail => fun rec z => .more (p.step.term z.1) (rec.1 z.1)
      ((p.output_eq z.1).symm ▸ (tail z.1).termChain (rec.2 z.1) z.2)

/-- Every pass on every branch satisfies its local bounds with constant `C`, controlling record
and preimage counts, field widths and map-entry degrees. -/
def Bounded (C : ℕ) {a g : ℕ} {X : State a g} (E : StateExecution R b n X) : E.Records → Prop :=
  match E with
  | .done _ => fun _ => True
  | .more p tail => fun rec => p.Bounded rec.1 C ∧ ∀ i, (tail i).Bounded C (rec.2 i)

omit [CommSemiring R] in
private theorem chain_input_mono {N Y : Network} (chain : TermChain R N Y) {C W W' : ℕ}
    (h : chain.Bounded C W) (hle : W ≤ W') : chain.Bounded C W' := by
  cases chain with
  | done => trivial
  | more t rec tail =>
    exact ⟨h.1, h.2.1.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hle)), h.2.2⟩

omit [CommSemiring R] in
private theorem cast_bounded {N Y Z : Network} (h : N = Y) (chain : TermChain R Y Z) {C W : ℕ}
    (hb : chain.Bounded C W) : (h.symm ▸ chain : TermChain R N Z).Bounded C W := by
  cases h
  exact hb

theorem termChain_bounded (E : StateExecution R b n X) (rec : E.Records) {C : ℕ}
    (hb : E.Bounded C rec) (z : E.Choices) : (E.termChain rec z).Bounded C X.maxWireWidth := by
  induction E with
  | done => trivial
  | more p tail ih =>
    obtain ⟨hpass, htail⟩ := hb
    obtain ⟨hc, hw, hnext⟩ := hpass z.1
    exact ⟨hc, hw, cast_bounded (p.output_eq z.1) _
      (chain_input_mono _ (ih z.1 (rec.2 z.1) (htail z.1) z.2) hnext)⟩

omit [CommSemiring R] in
private theorem cast_peak {N Y Z : Network} (h : N = Y) (chain : TermChain R Y Z) (W : ℕ) :
    (h.symm ▸ chain : TermChain R N Z).peak W = chain.peak W := by cases h; rfl

/-- The maximum actual final arc width is among the quantities controlled by
this branch's peak, even when the terminal layout depends on all earlier choices. -/
theorem final_maxWireWidth_le_peak (E : StateExecution R b n X) (rec : E.Records) {C W : ℕ}
    (hb : E.Bounded C rec) (hw : X.maxWireWidth ≤ W) (z : E.Choices) :
    (E.finalState z).maxWireWidth ≤ (E.termChain rec z).peak W := by
  induction E generalizing W with
  | done => exact hw
  | more p tail ih =>
    have hh := ih z.1 (rec.2 z.1) (hb.2 z.1) (hb.1 z.1).2.2 z.2
    change _ ≤ max W (((p.output_eq z.1).symm ▸ (tail z.1).termChain (rec.2 z.1) z.2 :
      TermChain R (p.step.term z.1).output _).peak (TermChain.largest (rec.1 z.1)))
    rw [cast_peak (p.output_eq z.1)]
    exact hh.trans (le_max_right _ _)

/-- Theorem 7.1's local growth conclusion for a chosen branch of an execution
of `T` blocks, each containing at most `s` substeps with bounded local records. -/
theorem localHistory_bounds (E : StateExecution R b n X) (rec : E.Records) {C s T : ℕ}
    (hC : 1 ≤ C) (hb : E.Bounded C rec) (z : E.Choices)
    (hlen : (E.termChain rec z).length ≤ s * T) :
    (∀ v, (E.termChain rec z).occurrences (fun _ => 1) v ≤ (C ^ s) ^ T) ∧
    (E.termChain rec z).peak X.maxWireWidth + 1 ≤ (C ^ s) ^ T * (X.maxWireWidth + 1) :=
  (E.termChain rec z).blockGrowth hC (E.termChain_bounded rec hb z) hlen

end StateExecution
end Compression

end VPVNP
end Computability
end OAI
