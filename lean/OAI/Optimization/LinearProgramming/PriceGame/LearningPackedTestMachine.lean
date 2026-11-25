import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTests
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.PriceGame.LearningFoldMachine

/-! # A polynomial binary program for extracting comparisons from trial logs -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram Control Control.Wire
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

private abbrev histCode := listCode (listCode ratCode)
private abbrev pTail := prodCode (listCode ratCode) histCode
private abbrev eBase := prodCode pivotCode (listCode ratCode)
private abbrev eTail := prodCode (listCode Nat.bits) eBase
private abbrev eMiddle := prodCode boolCode eTail

private def pWordFields (p : PackedProbe) := (p.level,p.prices,p.history)
private def eWordFields (e : PackedExpert) := (e.level,e.positive,e.tuple,e.pivot,e.raw)

noncomputable def probeLevelP : Procedure packedProbeCode Nat.bits PackedProbe.level :=
  (Procedure.first Nat.bits pTail).precompose pWordFields
private noncomputable def pFields := (Procedure.second Nat.bits pTail).precompose pWordFields
noncomputable def probePricesP : Procedure packedProbeCode (listCode ratCode) PackedProbe.prices :=
  (Procedure.first (listCode ratCode) histCode).comp pFields
noncomputable def probeHistoryP : Procedure packedProbeCode histCode PackedProbe.history :=
  (Procedure.second (listCode ratCode) histCode).comp pFields

noncomputable def expertLevelP : Procedure packedExpertCode Nat.bits PackedExpert.level :=
  (Procedure.first Nat.bits eMiddle).precompose eWordFields
private noncomputable def fields1 := (Procedure.second Nat.bits eMiddle).precompose eWordFields
private noncomputable def fields2 := (Procedure.second boolCode eTail).comp fields1
private noncomputable def fields3 := (Procedure.second (listCode Nat.bits) eBase).comp fields2
noncomputable def expertPositiveP : Procedure packedExpertCode boolCode PackedExpert.positive :=
  (Procedure.first boolCode eTail).comp fields1
noncomputable def expertTupleP : Procedure packedExpertCode (listCode Nat.bits) PackedExpert.tuple :=
  (Procedure.first (listCode Nat.bits) eBase).comp fields2
noncomputable def expertPivotP : Procedure packedExpertCode pivotCode PackedExpert.pivot :=
  (Procedure.first pivotCode (listCode ratCode)).comp fields3

private noncomputable def eqNatWordP {ρ : Type} {er : ρ → List Bool} {f g : ρ → ℕ}
    (p : Procedure er Nat.bits f) (q : Procedure er Nat.bits g) :
    Procedure er boolCode (fun x => decide (f x = g x)) := by
  apply (Procedure.boolAnd.comp ((Procedure.binaryLe.comp (p.pair q)).pair
    (Procedure.binaryLe.comp (q.pair p)))).congrFun
  intro x; apply Bool.eq_iff_iff.mpr; simp [le_antisymm_iff]

private noncomputable def orientedP {ρ : Type} {er : ρ → List Bool} {s : ρ → Bool} {f : ρ → ℚ}
    (sgn : Procedure er boolCode s) (p : Procedure er ratCode f) :
    Procedure er ratCode (fun x => oriented (s x) (f x)) :=
  Procedure.conditional sgn p (Procedure.ratNeg.comp p)

private noncomputable def priceP {ρ : Type} {er : ρ → List Bool} {p : ρ → PackedProbe} {ix : ρ → ℕ}
    (pp : Procedure er packedProbeCode p) (i : Procedure er Nat.bits ix) :
    Procedure er ratCode (fun z => priceAt (p z) (ix z)) :=
  (Procedure.listGet ratCode 0).comp (i.pair (probePricesP.comp pp))

private noncomputable def pairAtP {ρ : Type} {er : ρ → List Bool} {e : ρ → PackedExpert}
    {p : ρ → PackedProbe} {ix jx : ρ → ℕ} (ep : Procedure er packedExpertCode e)
    (pp : Procedure er packedProbeCode p) (ip : Procedure er Nat.bits ix)
    (jp : Procedure er Nat.bits jx) :
    Procedure er packedTestCode (fun x => pairPacked (e x) (p x) (ix x) (jx x)) := by
  let lev := expertLevelP.comp ep
  let a := rootAddressP.comp (ip.pair lev)
  let b := (someP Nat.bits).comp (rootAddressP.comp (jp.pair lev))
  let delta := Procedure.ratSub.comp ((priceP pp ip).pair (priceP pp jp))
  exact (a.pair b).pair (orientedP (expertPositiveP.comp ep) delta)

private noncomputable def outsideAtP {ρ : Type} {er : ρ → List Bool} {e : ρ → PackedExpert}
    {p : ρ → PackedProbe} {ix : ρ → ℕ} (ep : Procedure er packedExpertCode e)
    (pp : Procedure er packedProbeCode p) (ip : Procedure er Nat.bits ix) :
    Procedure er packedTestCode (fun x => outsidePacked (e x) (p x) (ix x)) := by
  let sgn := expertPositiveP.comp ep
  let lev := expertLevelP.comp ep
  let a := rootAddressP.comp (ip.pair lev)
  let px := priceP pp ip
  let ij := prodCode Nat.bits Nat.bits
  let piv := expertPivotP.comp ep
  let existsPiv := (optionCasesP false (Procedure.constant ij boolCode true)).comp piv
  let coord := (optionCasesP (0,0) (Procedure.identity ij)).comp piv
  let lv := (Procedure.first Nat.bits Nat.bits).comp coord
  let j := (Procedure.second Nat.bits Nat.bits).comp coord
  let pr := (Procedure.listGet (listCode ratCode) []).comp (lv.pair (probeHistoryP.comp pp))
  let prev := (Procedure.listGet ratCode 0).comp (j.pair pr)
  let pj := (someP Nat.bits).comp (rootAddressP.comp (j.pair lv))
  let withPivot := (a.pair pj).pair (orientedP sgn (Procedure.ratSub.comp (px.pair prev)))
  let withoutPivot := (a.pair (Procedure.constant er (optionCode Nat.bits) none)).pair (orientedP sgn px)
  apply (Procedure.conditional existsPiv withPivot withoutPivot).congrFun
  intro x
  cases hp : (e x).pivot with
  | none => simp [outsidePacked,hp]
  | some v => obtain ⟨k,j⟩ := v; simp [outsidePacked,hp,ancestorAt,atAddress]

/-- Produce one probe's concrete comparisons in the public tuple order. The implementation
uses charged list walks and explicit signed rational subtraction. -/
noncomputable def packedTestsP : Procedure (prodCode packedExpertCode packedProbeCode)
    (listCode packedTestCode) (fun x => packedTests x.1 x.2) := by
  let env := prodCode packedExpertCode packedProbeCode
  let ienv := prodCode Nat.bits env
  let jenv := prodCode Nat.bits ienv
  let e := Procedure.first packedExpertCode packedProbeCode
  let p := Procedure.second packedExpertCode packedProbeCode
  let i := Procedure.first Nat.bits env
  let ie := Procedure.second Nat.bits env
  let j := Procedure.first Nat.bits ienv
  let je := Procedure.second Nat.bits ienv
  let test := pairAtP (e.comp (ie.comp je)) (p.comp (ie.comp je)) (i.comp je) j
  let defTest : PackedTest := ((0,none),0)
  let inside := (GenerationCost.mapContextP 0 defTest test).comp
    (((expertTupleP.comp e).comp ie).pair (Procedure.identity ienv))
  let line := (Procedure.listCons packedTestCode).comp ((outsideAtP (e.comp ie) (p.comp ie) i).pair inside)
  let lines := (GenerationCost.mapContextP 0 ([] : List PackedTest) line).comp
    ((expertTupleP.comp e).pair (Procedure.identity env))
  let total := (GenerationCost.flattenP packedTestCode defTest).comp lines
  let matchLevel := eqNatWordP (probeLevelP.comp p) (expertLevelP.comp e)
  apply (Procedure.conditional matchLevel total (Procedure.constant env (listCode packedTestCode) [])).congrFun
  intro x
  change (if decide (x.2.level = x.1.level) then _ else _) = _
  simp [packedTests]

def packedHistoryTests (e : PackedExpert) (ps : List PackedProbe) : List PackedTest :=
  ps.flatMap (packedTests e)

noncomputable def packedHistoryTestsP : Procedure (prodCode packedExpertCode (listCode packedProbeCode))
    (listCode packedTestCode) (fun x => packedHistoryTests x.1 x.2) := by
  let env := prodCode packedExpertCode (listCode packedProbeCode)
  let body := packedTestsP.comp (Procedure.swap packedProbeCode packedExpertCode)
  let parts := (GenerationCost.mapContextP (default : PackedProbe) ([] : List PackedTest) body).comp
    (Procedure.swap packedExpertCode (listCode packedProbeCode))
  exact ((GenerationCost.flattenP packedTestCode ((0,none),0)).comp parts).congrFun (by
    intro x; rfl)

theorem packedHistoryTests_correct {N} (e : Expert N) (ps : List (Probe N)) :
    packedHistoryTests (packExpert e) (ps.map packProbe) = (ps.flatMap e.skeleton.testsAt).map packTest := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [packedHistoryTests, List.map_cons, List.flatMap_cons, List.map_append, packedTests_correct]
    exact congrArg _ ih

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
