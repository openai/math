import OAI.Computability.MultitapeWeakETH.MotifArguments
import OAI.Computability.MultitapeWeakETH.TerminalProgram

/-! # A fixed polynomial-time tape program for the grouped motif lookup -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP MotifSelector StackInterpreter
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical
noncomputable section

abbrev MapInput := (List Bits.Word × SupplyInput) × List Tally
abbrev Ready (S : Type) := MapInput × List (Label S)
private abbrev Position (S : Type) := Ready S × Tally

variable {D J E S V : Type} [Fintype D] [DecidableEq J] [Fintype E] [Fintype S] [Fintype V]
  (src dst : D → J) (G : Supply J E) (a : D → ℕ) (w : S → E → ℕ) (j : J)
  (lookup : ∀ s, MotifDemandPadding.HalfBits src dst a j → Half G (fun e => Word (w s e)) j → V)

private def name (s : S) (q : Position S) : Label V :=
  ⟨lookup s (demand src dst j a (q.1.1.1.1,q.2)).val
    (supply j G w s ((q.1.1.1.2,q.1.2),q.2)).val⟩

private theorem name_poly (s : S) : Poly (name src dst G a w j lookup s) := by
  have demandQ : Poly (fun q : Position S => (q.1.1.1.1,q.2)) := by fun_prop
  have supplyQ : Poly (fun q : Position S => ((q.1.1.1.2,q.1.2),q.2)) := by fun_prop
  exact ((demandQ.compose (demand_poly src dst j a)).pair (supplyQ.compose (supply_poly j G w s))).compose
    (Easy.finite (fun p => Label.mk (lookup s p.1.val p.2.val))).poly

variable (s₀ : S) {bits : ℕ} (table : List S) (code : S ↪ Word bits)

private def selectedName (q : Position S) :=
  name src dst G a w j lookup (Iter.pick (Label.mk s₀) (q.1.2,q.2)).val q

private theorem selectedName_poly : Poly (selectedName src dst G a w j lookup s₀) := by
  have index : Poly (fun q : Position S => (q.1.2,q.2)) := by fun_prop
  exact select_poly _ (index.compose (Iter.facile (Label.mk s₀)).poly) _ (name_poly src dst G a w j lookup) _ (name_poly src dst G a w j lookup s₀)

private def emit (q : Ready S) :=
  bif totals w (q.1.2,q.2) then
    some ((Iter.lineup q.1.1.2.2).map fun i => selectedName src dst G a w j lookup s₀ (q,i)) else none

private theorem emit_poly : Poly (emit src dst G a w j lookup s₀) := by
  have test : Poly (fun q : Ready S => (q.1.2,q.2)) := by fun_prop
  have num : Poly (fun q : Ready S => q.1.1.2.2) := by fun_prop
  have rows := (Poly.identity.pair (num.compose Iter.poly_line)).compose
    (Poly.push ((([],([],[])),[]),[]) [] (selectedName_poly src dst G a w j lookup s₀))
  exact Poly.choose (test.compose (totals_poly w)) (rows.compose Easy.some.poly) (Code.Poly.const _)

/-- The tapes contain incident demand bits, incident supply fields and their low payload
lengths, the copy count, and the declared payload lengths on all supply edges. -/
def entry (q : MapInput) := (selectors G j bits table code q.1.2).bind
  (fun seq => emit src dst G a w j lookup s₀ (q,seq))

theorem entry_poly : Poly (entry src dst G a w j lookup s₀ table code) := by
  have sq : Poly (fun q : MapInput => q.1.2) := by fun_prop
  exact bind_poly [] (sq.compose (selectors_poly G j bits table code)) (emit_poly src dst G a w j lookup s₀)

variable {u : ℕ} (b : D → ℕ) (v : E → ℕ) (d : MotifEntry.DemandBits src dst b j)
  (x : Half G (fun e => Fin (v e+u*bits) → Bool) j)

def mapInput : MapInput :=
  ((bank (fun p : Ends src dst j => match p with
    | .inl e => List.ofFn (d.1 e.val e.prop)
    | .inr e => List.ofFn (d.2 e.val e.prop)),supplyInput G j v x),bank (fun e => tally (v e)))

omit [Fintype S] [Fintype V] in
private theorem name_eq (seq : Fin u → S) (i : Fin u) :
    selectedName src dst G a w j lookup s₀ ((mapInput src dst G j b v d x,List.ofFn fun l => Label.mk (seq l)),tally i.val) =
      Label.mk (lookup (seq i) (MotifEntry.demandFields src dst a i j d)
        (mapHalf G (fun e y => MotifEntry.fieldIndex (MotifEntry.payloadBits y)
          (MotifEntry.offset (fun l => w (seq l) e) i) (w (seq i) e)) x)) := by
  let q : Position S := ((mapInput src dst G j b v d x,List.ofFn fun l => Label.mk (seq l)),tally i.val)
  have idx : Iter.pick (Label.mk s₀) (q.1.2,q.2) = Label.mk (seq i) :=
    Iter.entry (fun l : Fin u => Label.mk (seq l)) i (Label.mk s₀)
  refine (congrArg (fun s : Label S => name src dst G a w j lookup s.val q) idx).trans ?_
  change Label.mk (lookup (seq i) (demand src dst j a (demandInput src dst j d i)).val
    (supply j G w (seq i) ((supplyInput G j v x,List.ofFn fun l => Label.mk (seq l)),tally i.val)).val) = _
  rw [demand_eq,supply_eq]

omit [Fintype S] [Fintype V] in
theorem entry_eq (F : ∀ s j, MotifDemandPadding.HalfBits src dst a j → Half G (fun e => Word (w s e)) j → V) :
    entry src dst G a w j (fun s => F s j) s₀ table code (mapInput src dst G j b v d x) =
      (MotifEntry.run src dst a b G w F table code v j d x).1.map (List.map Label.mk) := by
  rw [MotifEntry.run_value]
  let t := mapHalf G (fun _ => MotifEntry.readTag) x
  have stages := selectors_eq G j bits table code v x
  unfold entry
  rw [show (mapInput src dst G j b v d x).1.2 = supplyInput G j v x by rfl,stages]
  unfold MotifEntry.describe MotifEntry.labels MotifEntry.indices
  by_cases ok : MotifEntry.consistent G j t = true
  · simp only [show MotifEntry.consistent G j (mapHalf G (fun _ => MotifEntry.readTag) x) = true from ok,ite_true]
    cases h : MotifEntry.selectors? table code (MotifEntry.anchor G j t) with
    | none => simp only [Option.map_none,Option.bind_none]
    | some seq =>
      dsimp only [t] at h
      simp only [Option.map_some,Option.bind_some]
      unfold emit MotifEntry.extract
      have cost := totals_eq w seq v
      change (bif totals w (bank (fun e => tally (v e)),_) then _ else _) = _
      rw [cost]
      by_cases good : ∀ e, v e = totalWidth w seq e
      · rw [ite_eq_left good,decide_eq_true good]
        simp only [Bool.cond_true,Option.map_some,Option.some.injEq]
        change (Iter.lineup (tally u)).map _ = _
        simp only [Iter.lined,List.map_ofFn,Function.comp_def]
        exact congrArg List.ofFn (funext (name_eq src dst G a w j (fun s => F s j) s₀ b v d x seq))
      · rw [ite_eq_right good,decide_eq_false good]
        rfl
  · simp only [show ¬ MotifEntry.consistent G j (mapHalf G (fun _ => MotifEntry.readTag) x) = true from ok,
      Bool.false_eq_true,ite_false,Option.map_none,Option.bind_none]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
