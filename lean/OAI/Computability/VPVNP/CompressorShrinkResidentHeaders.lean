import OAI.Computability.VPVNP.CompressorShrinkResidentsPlan
import OAI.Computability.VPVNP.CompressorSourceWalk

/-! # Publishing the six resident-directory heads of a shrinking level -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentsPlan

open BurstRAM BlockPlanner PhaseRecipe ShrinkResidentLayout
open scoped Fin.CommRing

variable {w : ℕ}

/-- The six directory pointers in header order, owner, count and row bases for hidden fields
followed by the corresponding bases for party maps. -/
def headValues (L : Layout) : Fin 6 → ℕ :=
  ![L.owner false,L.counts false,L.rows false,L.owner true,L.counts true,L.rows true]

/-- The two publisher operands for head `i`, its destination at old-level offset `30 + i` and
the corresponding directory pointer. -/
def headerBank (level : ℕ) (L : Layout) (w : ℕ) (i : Fin 6) : Fin 2 → Word w :=
  ![((level+(30+i.val) : ℕ) : Word w),(headValues L i : Word w)]

/-- The single-head publication trace, including the pointer write at the designated header
offset and the return of cursor one. -/
def headerReport (level : ℕ) (L : Layout) (w : ℕ) (i : Fin 6) : Report w :=
  ⟨[.tick,.tick,.tick,.write (headerBank level L w i 0) (headerBank level L w i 1),.tick,.tick],some 1⟩

/-- Plan the one-word publication of the chosen resident directory pointer at offset `30 + i`
of the old level. -/
def headerVisit (I : SelectedPlan.Inputs) (first oldLevel : Expr) (i : Fin 6) :=
  publish (oldLevel.add (.lit (30+i.val))) (heads I first i)

theorem header_bank_eq (I : SelectedPlan.Inputs) (first oldLevel : Expr) (pub : Fin 5 → Word w)
    (st : Word w) (m : Memory w) (level : ℕ) (L : Layout) (h : Ready I first pub st m L)
    (levelWord : Expr.eval pub st m oldLevel = (level : Word w)) (i : Fin 6) :
    (fun j => Expr.eval pub st m ((headerVisit I first oldLevel i).params j)) = headerBank level L w i := by
  funext j
  fin_cases j
  · change Expr.eval pub st m oldLevel + ((30+i.val : ℕ) : Word w) = ((level+(30+i.val) : ℕ) : Word w)
    simp only [levelWord,Nat.cast_add]
  · change Expr.eval pub st m (heads I first i) = (headValues L i : Word w)
    fin_cases i
    · exact owner_val I first pub st m L h false
    · exact counts_val I first pub st m L h false
    · exact rows_val I first pub st m L h false
    · exact owner_val I first pub st m L h true
    · exact counts_val I first pub st m L h true
    · exact rows_val I first pub st m L h true

/-- A successful single publication call from cursor zero with the concrete head operands,
seven units of fuel and an empty branch stream. -/
def headerSource (I : SelectedPlan.Inputs) (first oldLevel : Expr) (level : ℕ) (L : Layout)
    (i : Fin 6) (m : Memory w) (rs : List (Report w)) :=
  let M := ((headerVisit I first oldLevel i).worker.table.instantiate w (headerBank level L w i)).program
  runSegment M 7 (some 0) m [[]] = some rs

theorem header_source (I : SelectedPlan.Inputs) (first oldLevel : Expr) (level : ℕ) (L : Layout)
    (i : Fin 6) (m : Memory w) :
    headerSource I first oldLevel level L i m [headerReport level L w i] := by
  have run := (publish_native (oldLevel.add (.lit (30+i.val))) (heads I first i) (headerBank level L w i) 0 m).1
  dsimp only [headerSource,runSegment,headerVisit]
  rw [run,zero_add]
  rfl

theorem header_walk (I : SelectedPlan.Inputs) (first oldLevel : Expr) (level : ℕ) (L : Layout)
    (m : Memory w) :
    SourceWalk (headerSource I first oldLevel level L) (List.finRange 6) m (List.ofFn (headerReport level L w)) := by
  have go (is : List (Fin 6)) (mem : Memory w) :
      SourceWalk (headerSource I first oldLevel level L) is mem (is.map (headerReport level L w)) := by
    induction is generalizing mem with
    | nil => exact .done _
    | cons i is ih => exact SourceWalk.next (header_source I first oldLevel level L i mem) (ih _)
  simpa only [List.ofFn_eq_map] using go (List.finRange 6) m

private theorem addr_word (level : ℕ) (L : Layout) (fit : level+36 ≤ 2^w) (i : Fin 6) :
    (headerBank level L w i 0).val = level+(30+i.val) := Nat.mod_eq_of_lt (by have := i.isLt; omega)

/-- A list of successful publishers sets exactly its addressed head cells. -/
private theorem publish_effect (level : ℕ) (L : Layout) (fit : level+36 ≤ 2^w)
    (is : List (Fin 6)) (m : Memory w) :
    let out := after m (eventLog (is.map (headerReport level L w)))
    (∀ i ∈ is, out (level+(30+i.val)) = (headValues L i : Word w)) ∧
      (∀ x, (∀ i ∈ is, x ≠ level+(30+i.val)) → out x = m x) := by
  induction is generalizing m with
  | nil => exact ⟨fun _ hi => False.elim (List.not_mem_nil hi),fun _ _ => rfl⟩
  | cons i is ih =>
    let one := writeMemory m (headerBank level L w i 0) (headerBank level L w i 1)
    have frame : after m (eventLog ((i::is).map (headerReport level L w))) =
        after one (eventLog (is.map (headerReport level L w))) := by
      change after m ((headerReport level L w i).events ++ eventLog _) = _
      rw [after,List.foldl_append]; rfl
    obtain ⟨written,kept⟩ := ih one
    dsimp only
    rw [frame]
    constructor
    · intro j hj
      by_cases found : j ∈ is
      · exact written j found
      · have same : j=i := (List.mem_cons.mp hj).resolve_right found
        subst j
        have unique (k : Fin 6) (hk : k ∈ is) : level+(30+i.val) ≠ level+(30+k.val) := by
          intro eq
          have same : i=k := Fin.ext (by omega)
          exact found (same.symm ▸ hk)
        rw [kept _ unique]
        change (if _ then _ else _) = _
        rw [addr_word level L fit,ite_eq_left rfl]; rfl
    · intro x hx
      rw [kept x (fun j hj => hx j (List.mem_cons_of_mem _ hj))]
      change (if _ then _ else _) = _
      rw [addr_word level L fit,ite_eq_right (hx i (List.mem_cons_self ..))]

/-- The six heads are available at fixed offsets 30 through 35, and
other addresses retain their contents after these one-write calls. -/
theorem published (level : ℕ) (L : Layout) (fit : level+36 ≤ 2^w) (m : Memory w) :
    let out := after m (eventLog (List.ofFn (headerReport level L w)))
    (∀ i : Fin 6, out (level+(30+i.val)) = (headValues L i : Word w)) ∧
      (∀ x, x<level+30 ∨ level+36≤x → out x = m x) := by
  obtain ⟨stored,frame⟩ := publish_effect level L fit (List.finRange 6) m
  rw [← List.ofFn_eq_map] at stored frame
  exact ⟨fun i => stored i (List.mem_finRange i),fun x hx => frame x (fun i _ => by have := i.isLt; omega)⟩

end CompressorRecords.ShrinkResidentsPlan

end VPVNP
end Computability
end OAI
