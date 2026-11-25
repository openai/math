import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingIndex
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTestMachine

/-! # Expanding compact expert assignments on the actual tape

The dimension is given in unary, materialized by the campaign prelude. Positions absent
from the sorted support receive value one; otherwise the compact coordinate begins at one.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram Control Control.Wire

private def rawEntry (roots : List ℕ) (v : List ℚ) (i : ℕ) : ℚ :=
  let k := supportIndex (i,roots)
  if k = 0 then 1 else atAddress 1 v k

/-- Physical-bit-order raw assignments for all root coordinates. -/
def expandRaw (N : ℕ) (roots : List ℕ) (v : List ℚ) : List ℚ :=
  (List.range N).map (rawEntry roots v)

noncomputable def expandRawP :
    Procedure (prodCode unaryCode (prodCode (listCode Nat.bits) (listCode ratCode))) (listCode ratCode)
      (fun x => expandRaw x.1 x.2.1 x.2.2) := by
  let env := prodCode (listCode Nat.bits) (listCode ratCode)
  let task := prodCode unaryCode env
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode env)
  let g := Procedure.second unaryCode env
  let roots := (Procedure.first (listCode Nat.bits) (listCode ratCode)).comp g
  let v := (Procedure.second (listCode Nat.bits) (listCode ratCode)).comp g
  let k := supportIndexP.comp (i.pair roots)
  let out := Procedure.conditional (Procedure.binaryZero.comp k) (Procedure.constant task ratCode 1)
    ((Procedure.listGet ratCode 1).comp (k.pair v))
  have one : Procedure task ratCode (fun x => rawEntry x.2.1 x.2.2 x.1) :=
    out.congrFun (by intro x; simp [rawEntry,atAddress])
  exact Procedure.tabulate (ea := env) (eb := ratCode)
    (f := fun z i => rawEntry z.1 z.2 i) 1 one

theorem expandRaw_correct {N} (s : Skeleton N) (v : Compact.Coord s → ℚ) :
    expandRaw N (canonicalSupport s) (List.ofFn v) = List.ofFn (Compact.unpack s v) := by
  apply List.ext_getElem
  · simp [expandRaw]
  · intro i hi _
    have hN : i < N := by simpa [expandRaw] using hi
    let j : Fin N := ⟨i,hN⟩
    simp only [expandRaw,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change rawEntry (canonicalSupport s) (List.ofFn v) j.val = Compact.unpack s v j
    rw [rawEntry,supportIndex_canonical]
    by_cases hj : j ∈ s.sources
    · have hn := Compact.index_ne_zero s hj
      have hv : (Compact.index s j).val ≠ 0 := fun z => hn (Fin.ext z)
      rw [ite_eq_right hv,Compact.unpack_index s v hj]
      simp only [atAddress,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,
        dite_eq_left (Compact.index s j).isLt,Option.getD_some]
    · simp [Compact.index,Compact.unpack,hj]

/-- Put the new full raw array on the wire while retaining the public skeleton fields. -/
def withRaw (e : PackedExpert) (raw : List ℚ) : PackedExpert := {e with raw}

noncomputable def withRawP : Procedure (prodCode packedExpertCode (listCode ratCode)) packedExpertCode
    (fun x => withRaw x.1 x.2) := by
  let e := Procedure.first packedExpertCode (listCode ratCode)
  let raw := Procedure.second packedExpertCode (listCode ratCode)
  let full := (expertLevelP.comp e).pair ((expertPositiveP.comp e).pair
    ((expertTupleP.comp e).pair ((expertPivotP.comp e).pair raw)))
  exact full.result (fun _ => rfl)

@[simp] theorem withRaw_packExpert {N} (e : Expert N) (v : Fin N → ℚ) :
    withRaw (packExpert e) (List.ofFn v) = packExpert ⟨e.skeleton,v⟩ := rfl

/-- A template with an empty raw data field is sufficient for all extraction and expansion. -/
@[simp] theorem withRaw_twice (e : PackedExpert) (v w : List ℚ) :
    withRaw (withRaw e v) w = withRaw e w := rfl

@[simp] theorem packedHistoryTests_withRaw (e : PackedExpert) (ps : List PackedProbe) (v : List ℚ) :
    packedHistoryTests (withRaw e v) ps = packedHistoryTests e ps := rfl

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
