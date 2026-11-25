import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineRoute
import OAI.Computability.NearSquareRoot.ScheduleGeneratorNumberedTable

/-! # Effective transition rows under a fixed physical tape route

A routed read vector is restricted to its active coordinates. Each action
on an inactive tape writes back that coordinate's read symbol and keeps its
head still. Both operations on tuple ranks are fixed finite tables, also
when the original control varies with the candidate index.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Routing

open CommonAlphabet IntegerMultiplication TM

variable {G H A I J : Type}

/-- Look up a natural number indexed by a ranked element of a fixed finite type. -/
def lookup (n : Numbering G) (f : G → ℕ) (x : ℕ) : ℕ :=
  (List.ofFn fun k => f (n.equiv.symm k)).getD x 0

theorem lookup_rank (n : Numbering G) (f : G → ℕ) (x : G) :
    lookup n f (n.equiv x).val = f x := by
  simp [lookup,List.getD_eq_getElem?_getD]

theorem primrec_lookup (n : Numbering G) (f : G → ℕ) : Primrec (lookup n f) :=
  (Primrec.list_getD 0).comp (Primrec.const _) Primrec.id

/-- A fixed numeric table with independent row and column numberings. -/
def lookup₂ (g : Numbering G) (h : Numbering H) (f : G → H → ℕ) (x y : ℕ) : ℕ :=
  ((List.ofFn fun i => List.ofFn fun j => f (g.equiv.symm i) (h.equiv.symm j)).getD x []).getD y 0

theorem lookup₂_rank (g : Numbering G) (h : Numbering H) (f : G → H → ℕ) (x : G) (y : H) :
    lookup₂ g h f (g.equiv x).val (h.equiv y).val = f x y := by
  simp [lookup₂,List.getD_eq_getElem?_getD]

theorem primrec_lookup₂ (g : Numbering G) (h : Numbering H) (f : G → H → ℕ) :
    Primrec₂ (lookup₂ g h f) :=
  (Primrec.list_getD 0).comp ((Primrec.list_getD []).comp (Primrec.const _) Primrec.fst) Primrec.snd

variable (r : Pipeline.Route I J) (a : Numbering A) (i : Numbering I) (k : Numbering J)

/-- Rank of the tuple of symbols seen by the local rule. -/
def restrictRead : ℕ → ℕ := lookup (k.arrow a) fun read => ((i.arrow a).equiv (read ∘ r.index)).val

/-- Rank of the full physical action, holding inactive tapes on their symbols. -/
def extendAction : ℕ → ℕ → ℕ :=
  lookup₂ (k.arrow a) (i.arrow (a.prod Numbering.move)) fun read op =>
    ((k.arrow (a.prod Numbering.move)).equiv (r.put op (fun j => (read j,Move.stay)))).val

abbrev Rows := ℕ → ℕ × ℕ → Option (ℕ × ℕ)

/-- Route an indexed family of ranked transitions through fixed physical tape coordinates. -/
def rows (localRows : Rows) : Rows := fun j p =>
  (localRows j (p.1,restrictRead r a i k p.2)).map
    (fun op => (op.1,extendAction r a i k p.2 op.2))

theorem computable_rows (localRows : Rows) (h : Computable₂ localRows) :
    Computable₂ (rows r a i k localRows) := by
  have restricted : Computable (restrictRead r a i k) := (primrec_lookup _ _).to_comp
  have extended : Computable₂ (extendAction r a i k) := (primrec_lookup₂ _ _ _).to_comp
  exact Computable.option_map (h.comp Computable.fst
    ((Computable.fst.comp Computable.snd).pair (restricted.comp (Computable.snd.comp Computable.snd))))
    ((Computable.fst.comp Computable.snd).pair (extended.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) (Computable.snd.comp Computable.snd)))

/-- The computed row is exactly the action emitted by the physical routed
machine at every legal state and tuple of head symbols. -/
theorem rows_correct {Q : ℕ → Type} (localRows : Rows) (q : ∀ j, Numbering (Q j))
    (m : ∀ j, Rule A (Q j) I)
    (correct : ∀ j s read, localRows j (((q j).equiv s).val, ((i.arrow a).equiv read).val) =
      (m j s read).map fun p => (((q j).equiv p.1).val, ((i.arrow (a.prod Numbering.move)).equiv p.2).val))
    (j : ℕ) (s : Q j) (read : J → A) :
    rows r a i k localRows j (((q j).equiv s).val,((k.arrow a).equiv read).val) =
      (r.rule (m j) s read).map fun p =>
        (((q j).equiv p.1).val, ((k.arrow (a.prod Numbering.move)).equiv p.2).val) := by
  simp only [rows,restrictRead,lookup_rank,correct,Pipeline.Route.rule,Option.map_map]
  cases v : m j s (read ∘ r.index) with
  | none => rfl
  | some cmd =>
    obtain ⟨state,op⟩ := cmd
    simp [extendAction,lookup₂_rank]

end Generator.Routing

end NearSquareRoot
end Computability
end OAI
