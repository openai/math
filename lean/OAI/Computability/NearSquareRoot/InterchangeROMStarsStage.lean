import OAI.Computability.NearSquareRoot.InterchangeROMStarsPrice

/-! # Priced reserve stage for the recursive native request controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStars

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeAddress InterchangeROMAddress InterchangeROMRecursion
  InterchangeROMExpose InterchangeBatch

abbrev coefficient (C degree b a m cell : ℕ) := cell + C*(a+m+b+(a+m+a)+1)^degree + 3
abbrev reserve (b a : ℕ) := (2*a)*(2*b+9)+1

theorem computable_coefficient {X : Type} [Primcodable X] (C k : ℕ) {b a m cell : X → ℕ}
    (hb : Computable b) (ha : Computable a) (hm : Computable m) (hc : Computable cell) :
    Computable (fun x => coefficient C k (b x) (a x) (m x) (cell x)) := by
  have am := Primrec.nat_add.to_comp.comp ha hm
  have n := Primrec.nat_add.to_comp.comp am ha
  have bnd := Primrec.succ.to_comp.comp (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp am hb) n)
  have power (k : ℕ) : Computable fun x => (a x+m x+b x+(a x+m x+a x)+1)^k := by
    induction k with
    | zero => simpa only [pow_zero] using (Computable.const (α:=X) 1)
    | succ k ih => simpa only [pow_succ] using Primrec.nat_mul.to_comp.comp ih bnd
  exact Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp hc (Primrec.nat_mul.to_comp.comp
    (.const C) (power k))) (.const 3)

/-- A uniform degree and fixed numerical constant suffice for every reserve
template. Each record has physical size at most `cell*(recordWidth+1)`.
The two resource caps adjacent to a full child are independent of that size. -/
theorem run_priced : ∃ k C : ℕ, ∀ {b a m : ℕ} (q : Request b) (hb : 2≤b) (hn : 0<a+m+a)
    (hw : a+m+a < q.width) (ok : q.Admissible)
    (good : Tree → Prop) (_ : ∀ j, good (q.contents j))
    (cell : ℕ) (_ : ∀ j, (q.contents j).count≤cell*(q.recordWidth+1)),
    let i := frame a m q hb hn hw ok
    let src := afterMain a m q hb hn hw ok
    let h := centerHeader i
    ∃ qs : List (Request b), qs.length=2*a ∧
      (∀ x∈qs, x.Admissible ∧ x.width = Request.lanes (a+m+a) q.width ∧
        x.recordWidth=q.recordWidth ∧ x.rows.count=q.rows.count ∧ ∀ j, good (x.contents j)) ∧
      ∀ parent, At parent (command b a m) (Request.job b) [] qs (.fork (send h) src)
        ((Request.job b).reply q) (coefficient C k b a m cell*(localMass q k+1))
        (reserve b a*(Nat.log 2 q.recordVolume+1)) 1 := by
  obtain ⟨K,e,run⟩ := run_native
  obtain ⟨k,C,estimate⟩ := admin_bound K e
  refine ⟨k,C,?_⟩
  intro b a m q hb hn hw ok good hg cell hcell
  obtain ⟨qs,len,valid,park,physical⟩ := run q hb hn hw ok good hg
  refine ⟨qs,len,valid,fun parent => ?_⟩
  apply (physical parent).mono _ park le_rfl
  exact local_price q hb ok k cell _ _ hcell (estimate a m (frame a m q hb hn hw ok))

end InterchangeROMStars

end NearSquareRoot
end Computability
end OAI
