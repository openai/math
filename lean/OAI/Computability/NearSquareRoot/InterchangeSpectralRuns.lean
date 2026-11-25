import OAI.Computability.NearSquareRoot.InterchangeSignRuns
import OAI.Computability.IntegerMultiplication.Strip.Cars

/-!
# Interchange comparison masks in physical record order

A later field of length `d` is compared with the retained rank of an earlier
field. The innermost suffix has arbitrary shape. One P192 program expands the
three runs directly in the product-series order. Its charge is the number of
output records, including every copy on the suffix.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SpectralRuns
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open IntegerMultiplication.Bits IntegerMultiplication.Carry NearSquareRoot.InterchangeSignRuns

noncomputable section

/-- Classify a later-field position by its rank in the physical series. -/
def mask {A F : Type} (s : Series F) (h : Fin s.count) (before equal after : A) (x : F) :=
  if s.index x < h then before else if s.index x = h then equal else after

private theorem tab_mask {A F : Type} (s : Series F) (h : Fin s.count) (before equal after : A) :
    s.tab (mask s h before equal after) =
      List.replicate h.val before ++ [equal] ++ List.replicate (s.count-h.val-1) after := by
  let f : Fibre := ⟨s.count,1,h,by decide⟩
  apply List.ext_getElem
  · simp only [Series.card, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate]
    omega
  intro i hi hj
  let r : Fin s.count := ⟨i, by simpa only [Series.card] using hi⟩
  have hp := tags_at before equal after f r (0 : Fin 1)
  change (tags before equal after f)[r.val * 1 + (0 : ℕ)]? = _ at hp
  simp only [tags, f, Nat.mul_one, Nat.add_zero, List.replicate_one] at hp
  have hget := List.getElem?_eq_getElem hj
  rw [hget] at hp
  rw [s.get _ r]
  simpa only [mask, Equiv.apply_symm_apply] using (Option.some.inj hp).symm

private theorem tab_fibre {A F U : Type} (s : Series F) (t : Series U) (ht : 0 < t.count)
    (h : Fin s.count) (before equal after : A) :
    (s.cart t).tab (fun x => mask s h before equal after x.1) =
      tags before equal after ⟨s.count,t.count,h,ht⟩ := by
  rw [Series.grouped]
  have hp (x : F) : t.tab (fun _ => mask s h before equal after x) =
      List.replicate t.count (mask s h before equal after x) := by
    simp [Series.tab, Series.count]
  simp_rw [hp]
  change (s.tab ((List.replicate t.count) ∘ (mask s h before equal after))).flatten = _
  rw [← Series.map_tab, tab_mask]
  simp [tags]

/-- Generate the actual mask in tape order from binary `(h,d,s)`.
 Both the field series and its suffix can vary with the input. -/
theorem fibre_stripe {I A : Type} [Codec A] {F U : I → Type}
    (s : (i : I) → Series (F i)) (t : (i : I) → Series (U i)) (ht : ∀ i, 0 < (t i).count)
    (h : (i : I) → Fin (s i).count) (before equal after : A) :
    Carries (fun i => ((s i).count * (t i).count : ℕ))
      (fun i => send (born (h i), born (s i).count, born (t i).count))
      (fun i => stripe ((s i).cart (t i)) (fun x => send (mask (s i) (h i) before equal after x.1))) := by
  let g (i : I) : Fibre := ⟨(s i).count, (t i).count, h i, ht i⟩
  have hg := (comparison_program before equal after).slide g
  simpa only [Function.comp_def, stripe_eq', tab_fibre (ht := ht _), header, g] using hg

/-- Duplicate only the current ruler. Leave the previously emitted rows parked
 behind it while incrementing the working ruler and appending its old value. -/
private theorem emitRuler {X : Type} (cur rest : X → Tree) :
    Task (fun x => (cur x).count) (fun x => Tree.fork (cur x) (rest x))
      (fun x => .fork (.fork (.atom false) (cur x)) (.fork (cur x) (rest x))) := by
  let c : Cmd := (clone 0 1 2).join ((pack 0).join ((move 1 0 2).join
    ((give 0 false).join ((pack 0).join (pack 0)))))
  refine ⟨splitRoot 0 (fun _ => .pass) c, 100, fun x env r => ?_⟩
  let u := cur x
  let v := rest x
  have h₁ := fits_clone (i:=0) (j:=1) (u:=2) (by decide) (by decide) (by decide) u env (pile 0 v r)
  rw [pile_comm 1 u r 0 v (by decide)] at h₁
  have h₂ := fits_pack u v (pile 1 u r) 0 env
  rw [pile_comm 0 (.fork u v) r 1 u (by decide)] at h₂
  have h₃ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) u env (pile 0 (.fork u v) r)
  have h₄ := fits_give false (pile 0 u (pile 0 (.fork u v) r)) 0 env
  have h₅ := fits_pack (.atom false) u (pile 0 (.fork u v) r) 0 env
  have h₆ := fits_pack (.fork (.atom false) u) (.fork u v) r 0 env
  exact (fits_pair (h₁.join (h₂.join (h₃.join (h₄.join (h₅.join h₆)))))).mono (by dsimp [u]; omega)

private def down : Tally → List Tally
  | [] => []
  | _ :: t => t :: down t

private theorem down_ranks (l : Tally) : (down l).reverse = Iter.lineup l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [down, List.reverse_cons, ih, Iter.lineup, List.length_cons,
      List.ofFn_succ', Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    rw [recover_tally l]

/-- Enumerate the ascending field ranks as unary rulers. The spent work and
 the stored list are quadratic in the field range. -/
theorem enumerate_ranks : Computes (fun l : Tally => (l.length+1)^2) Iter.lineup := by
  let rep (l : Tally) (_ : Unit) := Tree.fork (send l) (send (down l))
  let seed (_ : Unit) := Tree.fork (send ([] : Tally)) (send ([] : List Tally))
  let D (_ : Tally) (_ : Unit) := True
  let I := {s : Unit × Tally × Unit // D (s.1::s.2.1) s.2.2}
  have step : Task (fun i : I => size i.val.2.1) (fun i => .fork (send i.val.1) (rep i.val.2.1 i.val.2.2))
      (fun i => rep (i.val.1::i.val.2.1) i.val.2.2) := by
    have clip := Task.dropLeft (fun i : I => send i.val.1) (fun i => rep i.val.2.1 i.val.2.2)
    refine (clip.compose (emitRuler (fun i : I => send i.val.2.1) (fun i => send (down i.val.2.1)))).bound 2 ?_
    intro i
    change 1 + size i.val.2.1 + 1 ≤ 2 * (size i.val.2.1 + 1)
    omega
  have fold := Task.foldRight (p:=fun _ (x : Unit) => send x) (f:=rep) (seed:=seed) (D:=D)
    (a:=fun _ l _ => size l) (b:=fun _ => 0) (fun _ _ _ _ => trivial) Task.self step
  have body := fold.on (fun l : Tally => ⟨(l,()),trivial⟩)
  simp only [Task.forest_send] at body
  have begin_ : Easy (fun l : Tally => (l,([] : Tally),([] : List Tally))) := by fun_prop
  have run := (Task.compose begin_ body).compose (Task.dropLeft (fun l : Tally => send l) (fun l => send (down l)))
  have spend (l : Tally) : Task.foldCost (fun _ (t : Tally) => size t + (send ()).count) l = (l.length+1)^2 := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      change size l + 1 + 1 + Task.foldCost _ l = _
      rw [ih, size_tally, List.length_cons]
      ring
  have rev := Easy.reverse (X:=Tally)
  have cost (l : Tally) : size (down l) ≤ 5*(l.length+1)^2 := by
    induction l with
    | nil => decide
    | cons a l ih => simp only [down, size_cons, size_tally, List.length_cons]; nlinarith
  refine ((run.compose (rev.on down)).bound 15 (fun l => ?_)).conform (fun _ => rfl) (fun _ => rfl) (fun l => congrArg send (down_ranks l))
  change size l + (0 + Task.foldCost _ l) + size l + size (down l) + 1 ≤ _
  rw [spend, size_tally]
  nlinarith [cost l]

end
end SpectralRuns

end NearSquareRoot
end Computability
end OAI
