import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTestMachine

/-! # Compiled expert data for price-game transshipment

The market reads its bid and availability matrices directly from a serialized
expert and the ancestor-price table. Mixed-radix ancestry is computed by a
bounded binary shift, even on malformed or excessively deep indices.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Trial Wire States.Mass
open Learning.BitMachine

abbrev originCode := prodCode Nat.bits (prodCode Nat.bits Nat.bits)

theorem origin_shift (N l j : ℕ) :
    origin N l j = if j >>> l < N then j >>> l else 0 := by
  have hc : (j >>> l < N) ↔ j < N * 2 ^ l := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  by_cases hj : j < N * 2 ^ l
  · have hh := root_address N l ((vertexEquivFin N l).symm ⟨j,hj⟩)
    simpa [origin, hj, hc] using hh.symm
  · simp [origin, hj, hc]

noncomputable def originP : Procedure originCode Nat.bits (fun p => origin p.1 p.2.1 p.2.2) := by
  let dim := first Nat.bits (prodCode Nat.bits Nat.bits)
  let pair := second Nat.bits (prodCode Nat.bits Nat.bits)
  let root := rootAddressP.comp ((swap Nat.bits Nat.bits).comp pair)
  let inside := binaryLt.comp (root.pair dim)
  exact (conditional inside root (constant originCode Nat.bits 0)).congrFun (by
    intro x
    change (if decide (x.2.2 >>> x.2.1 < x.1) = true then x.2.2 >>> x.2.1 else 0) = _
    simpa only [decide_eq_true_eq] using (origin_shift x.1 x.2.1 x.2.2).symm)

private abbrev expertRest := prodCode pivotCode (listCode ratCode)
private abbrev tupleRest := prodCode (listCode Nat.bits) expertRest
private abbrev signRest := prodCode boolCode tupleRest

/-- The remaining expert field accessor, matching the existing public tuple,
sign, level and pivot projections. -/
noncomputable def expertRawP : Procedure packedExpertCode (listCode ratCode) PackedExpert.raw := by
  let fields (x : PackedExpert) := (x.level,x.positive,x.tuple,x.pivot,x.raw)
  let t1 := (second Nat.bits signRest).precompose fields
  let t2 := (second boolCode tupleRest).comp t1
  let t3 := (second (listCode Nat.bits) expertRest).comp t2
  exact (second pivotCode (listCode ratCode)).comp t3

private def containsStep (p : ℕ × ℕ × Bool) : ℕ × Bool :=
  (p.2.1, p.2.2 || decide (p.1 = p.2.1))

private theorem contains_fold (xs : List ℕ) (j : ℕ) (b : Bool) :
    xs.foldl (fun acc x => containsStep (x,acc)) (j,b) = (j,b || xs.contains j) := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    change xs.foldl _ (j,b || decide (x=j)) = _
    rw [ih]
    by_cases h : x=j
    · subst x; simp
    · simp [h, Ne.symm h]

private noncomputable def containsStepP : Procedure (prodCode Nat.bits (prodCode Nat.bits boolCode))
    (prodCode Nat.bits boolCode) containsStep := by
  let incoming := first Nat.bits (prodCode Nat.bits boolCode)
  let acc := second Nat.bits (prodCode Nat.bits boolCode)
  let target := (first Nat.bits boolCode).comp acc
  let old := (second Nat.bits boolCode).comp acc
  exact target.pair (boolOr.comp (old.pair (natEqP.comp (incoming.pair target))))

noncomputable def containsAddressP : Procedure (prodCode (listCode Nat.bits) Nat.bits) boolCode
    (fun p => p.1.contains p.2) := by
  let st := prodCode Nat.bits boolCode
  let scan := foldList 0 containsStepP Polynomial.X (by
    rintro xs ⟨j,b⟩ i
    change (st ((xs.take i).foldl (fun acc x => containsStep (x,acc)) (j,b))).length ≤ _
    rw [contains_fold, Polynomial.eval_X]
    simp [st, prodCode, pairBits_length, boolCode])
  let ec := prodCode (listCode Nat.bits) Nat.bits
  let init := (second (listCode Nat.bits) Nat.bits).pair (constant ec boolCode false)
  let rows := first (listCode Nat.bits) Nat.bits
  exact ((second Nat.bits boolCode).comp (scan.comp (rows.pair init))).congrFun (by
    rintro ⟨xs,j⟩
    change (xs.foldl _ (j,false)).2 = _
    simp [contains_fold])

abbrev acceptanceCode := prodCode Nat.bits (prodCode packedExpertCode Nat.bits)

noncomputable def acceptsRawP : Procedure acceptanceCode boolCode
    (fun p => acceptsRaw p.1 p.2.1 p.2.2) := by
  let level := first Nat.bits (prodCode packedExpertCode Nat.bits)
  let tail := second Nat.bits (prodCode packedExpertCode Nat.bits)
  let e := (first packedExpertCode Nat.bits).comp tail
  let i := (second packedExpertCode Nat.bits).comp tail
  let localTest := natEqP.comp ((expertLevelP.comp e).pair level)
  let tupleTest := containsAddressP.comp ((expertTupleP.comp e).pair i)
  exact (boolAnd.comp (localTest.pair tupleTest)).congrFun (by
    rintro ⟨l,e,j⟩
    change (decide (e.level=l) && e.tuple.contains j) = _
    have h : decide (e.level=l) = (e.level == l) := by
      apply Bool.eq_iff_iff.mpr
      simp
    rw [h]; rfl)

abbrev marketHistoryCode := listCode (listCode ratCode)
abbrev expertContextCode := prodCode Nat.bits (prodCode marketHistoryCode packedExpertCode)

noncomputable def shiftRawP : Procedure expertContextCode ratCode
    (fun p => shiftRaw p.1 p.2.1 p.2.2) := by
  let dim := first Nat.bits (prodCode marketHistoryCode packedExpertCode)
  let rest := second Nat.bits (prodCode marketHistoryCode packedExpertCode)
  let e := (second marketHistoryCode packedExpertCode).comp rest
  let H := (first marketHistoryCode packedExpertCode).comp rest
  let pivot := expertPivotP.comp e
  let two := prodCode Nat.bits Nat.bits
  let present := (optionCasesP false (constant two boolCode true)).comp pivot
  let address := (optionCasesP (0,0) (identity two)).comp pivot
  let level := (first Nat.bits Nat.bits).comp address
  let i := (second Nat.bits Nat.bits).comp address
  let value := (atDP ratCode).comp ((originP.comp (dim.pair address)).pair (expertRawP.comp e))
  let parentRow := (atDP (listCode ratCode)).comp (level.pair H)
  let parentPrice := (atDP ratCode).comp (i.pair parentRow)
  let signedPrice := (choose ratNeg (identity ratCode)).comp ((expertPositiveP.comp e).pair parentPrice)
  let moved := ratSub.comp (value.pair signedPrice)
  exact (conditional present moved (constant expertContextCode ratCode 0)).congrFun (by
    rintro ⟨N,H,e⟩
    change (if e.pivot.elim false (fun _ => true) then _ else 0) = shiftRaw N H e
    cases hp : e.pivot with
    | none => simp [hp, shiftRaw]
    | some q =>
      obtain ⟨k,i⟩ := q
      cases hs : e.positive <;> simp [shiftRaw, States.signed, hp, hs, Function.comp_def])

abbrev bidInputCode := prodCode (prodCode Nat.bits Nat.bits) expertContextCode

/-- Input consists of a level and good address, followed by the market context. -/
noncomputable def bidRawP : Procedure bidInputCode ratCode
    (fun p => bidRaw p.2.1 p.1.1 p.2.2.1 p.2.2.2 p.1.2) := by
  let addr := first (prodCode Nat.bits Nat.bits) expertContextCode
  let ctx := second (prodCode Nat.bits Nat.bits) expertContextCode
  let dim := (first Nat.bits (prodCode marketHistoryCode packedExpertCode)).comp ctx
  let tail := (second Nat.bits (prodCode marketHistoryCode packedExpertCode)).comp ctx
  let e := (second marketHistoryCode packedExpertCode).comp tail
  let raw := (atDP ratCode).comp ((originP.comp (dim.pair addr)).pair (expertRawP.comp e))
  exact ratSub.comp (raw.pair (shiftRawP.comp ctx))

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
