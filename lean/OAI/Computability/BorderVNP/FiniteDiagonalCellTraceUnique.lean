import OAI.Computability.BorderVNP.FiniteDiagonalCellTracePositive
import OAI.Computability.BorderVNP.FiniteDiagonalCellTrace

/-! # Unique returning native field-cell choices and scalar product

For every interior assignment, the returning typed validator has one genuine
private residual tape and one joint count report. The bit-major scalar burst
on this report returns exactly the product of all original local entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Copied

open Crossing CellSparse CellMacro FieldDirectory RoutingISA RoutingISA.CompactMachine
open scoped Classical BigOperators
open private idFacts from OAI.Computability.BorderVNP.FiniteCellCounts

variable {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network d P bits) {F : Type*} [Fintype F]

/-- The charged clock of the actual typed private generator, decoder,
interpreter and burst load. -/
def FitsClock (D : Directory) (w n k : ℕ) (ext : List Bool) : Prop :=
  let ops := (withExternal ext (D.program k)).expand []
  2*(3*((CompactFrame.pack w (Packet.input D k ext)).length*w)+
    CompactPacket.generationCost 8 (Packet.bits D k) ext (D.program k) (CellPrivate.translateClock D k)+
    (2*(stream ops).length+1)+budget ops) ≤ n^25

/-- Actual membership of a prefixed returning choice tape in the fixed typed
cell macro, with the indicated terminal sign. -/
def Accepted {k : ℕ} (D : Directory) (w n : ℕ) (g : Fin k → Bool) (ext tail : List Bool) (sg : Bool) : Prop :=
  ((List.ofFn g).reverse ++ tail,TeamPrivateCall.sign (some sg)) ∈
    choices (CompactPacket.driver CellPrivate.translate 8 3) n (CompactFrame.pack w (Packet.input D k ext))

private theorem widths {copies w : ℕ} (sites : List N.Site) (table : N.Tables F) :
    (directory N sites table copies w).ProfileWidths := by
  simp [Directory.ProfileWidths,directory,Copies.directory,Record.ProfileWidthOK]

/-- Check the actual count word for every scalar ID, across all copies. -/
def CorrectReport {copies w : ℕ} (sites : List N.Site) (table : N.Tables F) (a : Fin copies → N.Assignment)
    (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) : Prop :=
  countsValid (Copies.bank N a x (Copies.claimBits w c)) (Copies.directory N sites table copies w).reportedCounts
    ((Copies.ids N sites table a x).map fun j => (false,some j))

private theorem entry {copies w : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    (Copies.directory N sites table copies w).weight (Copies.bank N a x (Copies.claimBits w c)) =
      if CorrectReport N sites table a x c then 1 else 0 := by
  let D := Copies.directory N sites table copies w
  let b := Copies.bank N a x (Copies.claimBits w c)
  have hr : ∀ r ∈ D.records, r.Valid D.boxes b := by simp [D,Copies.directory,Record.Valid]
  rw [Directory.weight,Copies.observations]
  change (if (∀ r ∈ D.records, r.Valid D.boxes b) ∧ CorrectReport N sites table a x c then _ else 0) = _
  simp only [and_iff_right hr,(idFacts _).2,Bool.false_eq_true,ite_false]

/-- A complete per-report classification of the true physical native outcomes.
An aligned wire prefix and correct report have a single returning tape, with
positive sign. Every other prefix/report pair has no returning tape. -/
theorem classify {copies width w n : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (y x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin width → Bool)
    (hw : 0 < w) (time : FitsClock (directory N sites table copies width) w n (Copies.width N copies) (external x c)) :
    let D := directory N sites table copies width
    let g := guessedEquiv N copies (a,y)
    let ext := external x c
    if y = x ∧ CorrectReport N sites table a x c then
      ∃! p : List Bool × Bool, Accepted D w n g ext p.1 p.2 ∧ p.2 = false
    else ∀ tail sg, ¬ Accepted D w n g ext tail sg := by
  intro D g ext
  let T := Compact.assignmentTails D [] (List.ofFn g) ext
  have iffMem (p : List Bool × Bool) : Accepted D w n g ext p.1 p.2 ↔ p ∈ T :=
    Compact.typed_native_assignment D _ ext hw (widths N sites table) time g p.1 p.2
  have count := residual_card N sites table a y x c
  change (T.card : ℤ) = _ at count
  rw [entry] at count
  split
  · rename_i good
    rw [ite_eq_left good.1,ite_eq_left good.2] at count
    have one : T.card = 1 := by exact_mod_cast count
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp one
    have hmem : p ∈ T := hp ▸ Finset.mem_singleton_self _
    refine ⟨p,⟨(iffMem p).mpr hmem,residual_positive N sites table g x c p.1 p.2 hmem⟩,?_⟩
    intro u hu
    simpa only [hp,Finset.mem_singleton] using (iffMem u).mp hu.1
  · rename_i bad
    have empty : T = ∅ := by
      apply Finset.card_eq_zero.mp
      by_cases hy : y = x
      · rw [ite_eq_left hy,ite_eq_right (fun h => bad ⟨hy,h⟩)] at count
        exact_mod_cast count
      · rw [ite_eq_right hy] at count
        exact_mod_cast count
    intro tail sg ha
    have h := (iffMem (tail,sg)).mp ha
    simp [empty] at h

/-- For each fixed true wire assignment there is precisely one joint count
report and one genuine auxiliary native tape. The scalar macro reads the
same report bits and returns the original product on every actual fetched event. -/
theorem unique_native {copies width w n : ℕ} [Field F] (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (hw : 0 < w) (fits : copies*sites.length < 2^width)
    (time : ∀ c : Fin (Fintype.card F) → Fin width → Bool,
      FitsClock (directory N sites table copies width) w n (Copies.width N copies) (external x c)) :
    let D := directory N sites table copies width
    let g := guessedEquiv N copies (a,x)
    ∃! pair : (Fin (Fintype.card F) → Fin width → Bool) × List Bool,
      Accepted D w n g (external x pair.1) pair.2 false ∧
      ∀ (ev : TeamRAM.Event w) fuel, 2*((2*Fintype.card F+1)*width+2) ≤ fuel →
        ev.old = CompactFrame.pack w (reportBits pair.1) →
        ∀ z : F, FieldProcessor.returned (Burst.macroFor (Fintype.equivFin F).symm)
          (terminalOutput Burst.result) fuel ev = some z ↔
          ev.choices = [] ∧ z = ∏ i : Fin copies, (sites.map (N.read table (a i) (x i))).prod := by
  intro D g
  obtain ⟨c,hc,uc⟩ := unique_report_native N sites table a x hw fits
  have good : CorrectReport N sites table a x c := hc.1
  have cl := classify N sites table a x x c hw (time c)
  rw [ite_eq_left (And.intro rfl good)] at cl
  obtain ⟨⟨tail,sg⟩,ht,ut⟩ := cl
  obtain rfl : sg = false := ht.2
  refine ⟨(c,tail),⟨ht.1,hc.2⟩,?_⟩
  rintro ⟨c',tail'⟩ h
  have good' : CorrectReport N sites table a x c' := by
    by_contra hn
    have absent := classify N sites table a x x c' hw (time c')
    rw [ite_eq_right (fun hg => hn hg.2)] at absent
    exact absent tail' false h.1
  have ce : c' = c := uc c' ⟨good',h.2⟩
  subst c'
  exact congrArg (fun p : List Bool × Bool => (c,p.1)) (ut (tail',false) ⟨h.1,rfl⟩)

end FiniteDiagonal.CellTrace.Copied

end BorderVNP
end Computability
end OAI
