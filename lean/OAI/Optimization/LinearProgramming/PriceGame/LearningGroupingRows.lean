import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSupport
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCostHistorical

/-! Compile compact feature-key remapping, exact sort/deduplication, and threshold rows
in the product enumeration consumed by the historical-cell generator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

private abbrev RowKey := ℕ × ℕ
private abbrev IndexedTest := RowKey × ℚ
private abbrev keyCode := prodCode Nat.bits Nat.bits
private abbrev indexedCode := prodCode keyCode ratCode

def indexedTest (keys : List ℕ) (t : PackedTest) : IndexedTest :=
  ((supportIndex (t.1.1,keys), (t.1.2.map fun a => supportIndex (a,keys)).getD 0), t.2)

private noncomputable def indexedP :
    Procedure (prodCode (listCode Nat.bits) packedTestCode) indexedCode
      (fun x => indexedTest x.1 x.2) := by
  let out := listCode Nat.bits
  let ko := prodCode Nat.bits (optionCode Nat.bits)
  let env := prodCode out packedTestCode
  let keys := Procedure.first out packedTestCode
  let test := Procedure.second out packedTestCode
  let feature := (Procedure.first ko ratCode).comp test
  let idx := (Procedure.first Nat.bits (optionCode Nat.bits)).comp feature
  let opt := (Procedure.second Nat.bits (optionCode Nat.bits)).comp feature
  let price := (Procedure.second ko ratCode).comp test
  let someIdx := (optionCasesP 0 (Procedure.identity Nat.bits)).comp opt
  let has := (optionCasesP false (Procedure.constant Nat.bits boolCode true)).comp opt
  let r₀ := supportIndexP.comp (idx.pair keys)
  let r₁ := Procedure.conditional has (supportIndexP.comp (someIdx.pair keys))
    (Procedure.constant env Nat.bits 0)
  apply ((r₀.pair r₁).pair price).congrFun
  rintro ⟨ks,⟨⟨i,oi⟩,q⟩⟩
  cases oi <;> rfl

private def rowSet (k : RowKey) (ts : List IndexedTest) : Finset ℚ :=
  ((ts.filter (fun t => decide (t.1 = k))).map Prod.snd).toFinset

def rowForKey (k : RowKey) (ts : List IndexedTest) : List ℚ := (rowSet k ts).sort

private theorem mem_rowSet (k : RowKey) (ts : List IndexedTest) (q : ℚ) :
    q ∈ rowSet k ts ↔ ∃ t ∈ ts, t.1 = k ∧ t.2 = q := by
  simp only [rowSet,List.mem_toFinset,List.mem_map,List.mem_filter,decide_eq_true_eq]
  aesop

private noncomputable def matchesKeyP : Procedure (prodCode keyCode indexedCode) boolCode
    (fun x => decide (x.2.1 = x.1)) := by
  let ctx := Procedure.first keyCode indexedCode
  let t := Procedure.second keyCode indexedCode
  let k := (Procedure.first keyCode ratCode).comp t
  let a := Procedure.first Nat.bits Nat.bits
  let b := Procedure.second Nat.bits Nat.bits
  let same := Procedure.boolAnd.comp
    ((equalIndexP.comp ((a.comp k).pair (a.comp ctx))).pair
     (equalIndexP.comp ((b.comp k).pair (b.comp ctx))))
  apply same.congrFun
  intro x
  apply Bool.eq_iff_iff.mpr
  simp [Prod.ext_iff]

private noncomputable def rowP : Procedure (prodCode (listCode indexedCode) keyCode) (listCode ratCode)
    (fun x => rowForKey x.2 x.1) := by
  let filtered := filterWithP ((0,0),(0:ℚ)) matchesKeyP
  let proj := Procedure.listMap ((0,0),0) (0:ℚ) (Procedure.second keyCode ratCode)
  exact sortRationalP.comp (proj.comp filtered)

/-- Use exactly the finite product order used by the generator for `p` compact variables.
Their dummy coordinate is included at index zero. -/
def featureKeys (p : ℕ) : List RowKey :=
  (FinEnum.toList (Experts.Feature (p+1))).map fun ij => (ij.1.val, ij.2.val)

private def rowOrderTable : List (List RowKey) :=
  List.ofFn fun p : Fin 66 => featureKeys p.val

def orderForWidth (n : ℕ) : List RowKey := (rowOrderTable.drop n).headD []

theorem orderForWidth_eq {n : ℕ} (hn : n ≤ 65) : orderForWidth n = featureKeys n := by
  have h : n < 66 := by omega
  simp only [orderForWidth, rowOrderTable, List.headD_eq_head?_getD, List.head?_drop,
    List.getElem?_ofFn, dite_eq_left h, Option.getD_some]

def groupRows (keys : List ℕ) (ts : List PackedTest) : List (List ℚ) :=
  (orderForWidth keys.length).map fun ij => rowForKey ij (ts.map (indexedTest keys))

noncomputable def groupRowsP : Procedure (prodCode (listCode Nat.bits) (listCode packedTestCode))
    (listCode (listCode ratCode)) (fun x => groupRows x.1 x.2) := by
  let env := prodCode (listCode Nat.bits) (listCode packedTestCode)
  let keys := Procedure.first (listCode Nat.bits) (listCode packedTestCode)
  let cnt := (Procedure.listLength Nat.bits 0).comp keys
  let table := Procedure.constant env (listCode (listCode keyCode)) rowOrderTable
  let order := (Procedure.listGet (listCode keyCode) []).comp (cnt.pair table)
  let remap := (Market.GridMachine.mapWithContext ((0,none),0) ((0,0),0) indexedP).comp
    (Procedure.swap (listCode Nat.bits) (listCode packedTestCode))
  exact (Market.GridMachine.mapWithContext (0,0) ([] : List ℚ) rowP).comp (order.pair remap)

private theorem indexedTest_pack {N : ℕ} (s : Skeleton N) (t : Test N) :
    indexedTest (canonicalSupport s) (packTest t) =
      (((Compact.endpoints s t.feature).1.val,(Compact.endpoints s t.feature).2.val),t.threshold) := by
  obtain ⟨⟨i,j⟩,q⟩ := t
  cases j <;> simp [indexedTest,packTest,Compact.endpoints,supportIndex_canonical]

theorem groupRows_correct {N : ℕ} (s : Skeleton N) (ps : List (Probe N)) :
    groupRows (canonicalSupport s) ((ps.flatMap s.testsAt).map packTest) =
      GenerationCost.historyRows (Compact.thresholds s ps) := by
  have hlen : (canonicalSupport s).length = s.sources.card := by simp [canonicalSupport]
  rw [groupRows, hlen, orderForWidth_eq (Skeleton.card_sources_le s)]
  unfold featureKeys GenerationCost.historyRows
  rw [List.map_map]
  apply List.map_congr_left
  intro ij _
  change (rowSet (ij.1.val, ij.2.val) _).sort (· ≤ ·) = _
  apply congrArg (fun cut : Finset ℚ => cut.sort (· ≤ ·))
  ext q
  rw [mem_rowSet, Compact.threshold_mem_iff]
  constructor
  · rintro ⟨t,ht,hij,hq⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    rw [indexedTest_pack] at hij hq
    refine ⟨a,ha,?_,hq⟩
    exact Prod.ext (Fin.ext (congrArg Prod.fst hij)) (Fin.ext (congrArg Prod.snd hij))
  · rintro ⟨a,ha,he,hq⟩
    refine ⟨indexedTest (canonicalSupport s) (packTest a),List.mem_map_of_mem (List.mem_map_of_mem ha),?_,?_⟩
    · simp only [indexedTest_pack,he]
    · rw [indexedTest_pack]
      exact hq

noncomputable def packedThresholdRowsP :
    Procedure (prodCode Control.Wire.packedExpertCode (listCode Control.Wire.packedProbeCode))
      (listCode (listCode ratCode)) (fun x =>
        groupRows (packedSupport x.1) (packedHistoryTests x.1 x.2)) :=
  groupRowsP.comp
    ((packedSupportP.comp (Procedure.first Control.Wire.packedExpertCode
      (listCode Control.Wire.packedProbeCode))).pair packedHistoryTestsP)

theorem packedThresholdRows_correct {N : ℕ} (e : Expert N) (ps : List (Probe N)) :
    groupRows (packedSupport (Control.packExpert e))
      (packedHistoryTests (Control.packExpert e) (ps.map Control.packProbe)) =
        GenerationCost.historyRows (Compact.thresholds e.skeleton ps) := by
  rw [packedSupport_pack, packedHistoryTests_correct, groupRows_correct]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
