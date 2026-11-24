import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorBlockHeaderPlan
import OAI.Computability.VPVNP.CompressorCatalogRates

/-!
# Uniform traffic of the shrinking assignment and level publishers

The greedy run contains all six native projection, preparation and read visits.
At each substep two scalar rows and one array-head row are published.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledRates

open Compression BurstRAM Greedy Greedy.WalkLayout
open PhaseRecipe DescriptorSpace

variable {w : ℕ}

/-- Uniform coefficient for the relocated six-visit color and tag directory. -/
def greedyRate (d : ℕ) := 18+7*d+8*d^2+5*tagCount d+8*(tagCount d)^2

private theorem assignmentCap {V A : Type*} {N d width arity tests : ℕ}
    {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d}
    {order : V ≃ Fin N} {rows : OperandRows d} {src : Memory w} {encode : A → Word w} {f : V → A}
    (h : GreedyArena.Assignment L T G order rows arity tests src encode f) :
    ∀ r ∈ h.prep++h.reads, r.events.length+1 ≤ CatalogRates.greedyCap rows.length width arity
      tests := by
  intro r hr
  rcases List.mem_append.mp hr with hp|hq
  · apply le_trans _ (le_max_left ..)
    have := (h.prepWork r hp).1; omega
  · rw [(h.readWork r hq).1]
    exact le_trans (by omega) (le_max_right ..)

/-- The six fixed rows in `GreedyLevelPlan.visits` run on the incoming state.
Projection, both relocated preparers, and both readers have degree-only clocks. -/
theorem greedyProgram {a g : ℕ} (X : GreedyArena.ShrinkingState a g)
    (T : IncidenceDirectory w) (origin : ℕ) (m : Memory w) (r : GreedyArena.Run X T origin m) :
    r.reports.length = Fintype.card X.Base*(2^a+4)+1 ∧
      RAMBuckets.cost Report.probes r.reports ≤ X.positions*greedyRate (2^a) ∧
      ∀ rep ∈ r.reports, rep.events.length+1 ≤ max 14 (CatalogRates.greedyShrinkCap (2^a)) := by
  have hc := r.reports_cost
  let d := 2^a
  let K := 16+7*d+8*d^2+5*tagCount d+8*(tagCount d)^2
  have hn : Fintype.card X.Base ≤ X.positions := by
    rw [State.positions,Fintype.card_prod]; exact Nat.le_mul_of_pos_right _ Fintype.card_pos
  have hc' : RAMBuckets.cost Report.probes r.reports = 2+Fintype.card X.Base*K := hc
  refine ⟨r.reports_length,?_,?_⟩
  · rw [hc',show greedyRate (2^a) = 2+K from by dsimp [greedyRate,K,d]; ring]
    exact (Nat.add_le_add (by have := X.positions_pos; omega : 2 ≤ X.positions*2)
      (Nat.mul_le_mul_right K hn)).trans_eq (Nat.mul_add ..).symm
  · intro rep hr
    have color := assignmentCap r.color rep
    have off := assignmentCap r.offsets rep
    have csz : (colorOperandRows (2^a)).length = 2*2^a := by simp [colorOperandRows]
    have tsz : (tagOperandRows (2^a)).length = tagCount (2^a) := by simp [tagOperandRows,tagCount]
    rw [csz] at color; rw [tsz] at off
    simp only [GreedyArena.Run.reports,List.mem_append] at hr
    rcases hr with (((hp|cp)|cr)|tp)|tr
    · apply le_trans _ (le_max_left ..)
      have := (r.projection.work rep hp).1; omega
    · exact (color (List.mem_append_left _ cp)).trans ((le_max_left ..).trans (le_max_right ..))
    · exact (color (List.mem_append_right _ cr)).trans ((le_max_left ..).trans (le_max_right ..))
    · exact (off (List.mem_append_left _ tp)).trans ((le_max_right ..).trans (le_max_right ..))
    · exact (off (List.mem_append_right _ tr)).trans ((le_max_right ..).trans (le_max_right ..))

/-- Charge of one generated field-publisher row, including the call itself. -/
def publisherRate {g : ℕ} (R : FormulaRow g) := 1+R.recipe.reads+(g+3)

/-- Fuel for a formula-row publisher, equal to its instruction count plus one. -/
def publisherCap {g : ℕ} (R : FormulaRow g) := R.recipe.code.length+1

private theorem publisherCounts {g : ℕ} (R : FormulaRow g) (p : Fin 5 → Word w)
    (s : Word w) (m : Memory w) :
    let r := R.recipe.report p s m
    execute (R.recipe.table.instantiate w p).program (publisherCap R)
      ((R.recipe.table.instantiate w p).program.start s) m [] = some r ∧
    1+r.probes = publisherRate R ∧ r.events.length+1 = publisherCap R := by
  intro r
  obtain ⟨hl,hp,_⟩ := RowRecipe.report_cost R.recipe p s m
  refine ⟨RowRecipe.execute_row R.recipe p s m [] _ (Nat.lt_succ_self _),?_,?_⟩
  · change 1+(R.recipe.report p s m).probes = _
    rw [hp]; unfold publisherRate; omega
  · change (R.recipe.report p s m).events.length+1 = _
    rw [hl,publisherCap,RowRecipe.code_length]

/-- Sum the traffic rates of the two scalar publishers and the successor incidence and
table-head publisher for one substep. -/
def headerRate {a b : ℕ} (F : Shape) (p : Scalars.Pass a b) :=
  publisherRate (Scalars.advanceRow (.terminal a) p) + publisherRate (Scalars.advanceRow p
    (.terminal b)) +
    publisherRate (DescriptorHeads.publisher F)

/-- Maximum fuel needed by any of the three header publishers at a substep. -/
def headerCap {a b : ℕ} (F : Shape) (p : Scalars.Pass a b) :=
  max (publisherCap (Scalars.advanceRow (.terminal a) p))
    (max (publisherCap (Scalars.advanceRow p (.terminal b)))
    (publisherCap (DescriptorHeads.publisher F)))

/-- Three actual publisher reports, in chronological order and with a clock fixed by
the compiled formulas. The incoming memories may include scheduler frame writes. -/
theorem substepHeaderCounts {a b : ℕ} (F : Shape) (p : Scalars.Pass a b) (pub : Fin 3 → Fin 5 →
    Word w)
    (state : Fin 3 → Word w) (m : Fin 3 → Memory w) :
    let first := Scalars.advanceRow (.terminal a) p
    let next := Scalars.advanceRow p (.terminal b)
    let heads := DescriptorHeads.publisher F
    let r₀ := first.recipe.report (pub 0) (state 0) (m 0)
    let r₁ := next.recipe.report (pub 1) (state 1) (m 1)
    let r₂ := heads.recipe.report (pub 2) (state 2) (m 2)
    let run (g : ℕ) (R : FormulaRow g) (j : Fin 3) (rep : Report w) :=
      let M := (R.recipe.table.instantiate w (pub j)).program
      execute M (publisherCap R) (M.start (state j)) (m j) [] = some rep
    run 3 first 0 r₀ ∧ run 3 next 1 r₁ ∧ run (F.tables+3) heads 2 r₂ ∧
      RAMBuckets.cost Report.probes [r₀,r₁,r₂] = headerRate F p ∧
      ∀ rep ∈ [r₀,r₁,r₂], rep.events.length+1 ≤ headerCap F p := by
  intro first next heads r₀ r₁ r₂ run
  obtain ⟨ha,ca,ta⟩ := publisherCounts first (pub 0) (state 0) (m 0)
  obtain ⟨hb,cb,tb⟩ := publisherCounts next (pub 1) (state 1) (m 1)
  obtain ⟨hc,cc,tc⟩ := publisherCounts heads (pub 2) (state 2) (m 2)
  change 1+r₀.probes = _ at ca; change 1+r₁.probes = _ at cb; change 1+r₂.probes = _ at cc
  refine ⟨ha,hb,hc,?_,?_⟩
  · change _ + (_ + (_ + 0)) = publisherRate first + publisherRate next + publisherRate heads
    rw [ca,cb,cc]; omega
  · intro rep h
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact ta.le.trans (le_max_left ..)
    · exact tb.le.trans ((le_max_left ..).trans (le_max_right ..))
    · exact tc.le.trans ((le_max_right ..).trans (le_max_right ..))

end CompressorRecords.ScheduledRates

end VPVNP
end Computability
end OAI
