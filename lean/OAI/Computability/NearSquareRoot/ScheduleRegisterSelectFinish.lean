import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectEffective
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyMapping
import OAI.Computability.NearSquareRoot.KernelEffectiveMixScalar
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelectSpectator
import OAI.Computability.NearSquareRoot.KernelScaleBank

/-! # Compiled scalar coefficient tables on address-tagged row banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveScale
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelEffectiveFamily RegisterSelect Filter
open KernelComputableDyadic (coefficient)
abbrev Coeff := KernelComputableDyadic.Code
abbrev Packet := List Tally × List (List Dusk.Pair)

def finish (values : List Coeff) (p : Packet) : List (List Dusk.Pair) :=
  [(zipFair (tally 0) ([],[]) (p.1,p.2.headD [])).map fun t =>
    KernelScaleRecord.applyCoeff (coefficient (values.getD t.1.length KernelComputableDyadic.zero)) t.2]

/-- Every table is compiled into real branches. The generated action on a
scalar row is run once for every address in the dynamically sized bank. -/
theorem finish_family : ∀ᶠ R in atTop, Family R finish := by
  have gather : Code.Easy (fun p : Packet =>
      zipFair (tally 0) (([],[]) : Dusk.Pair) (p.1,p.2.headD [])) :=
    (Code.Easy.fst.pair (Code.Easy.snd.compose (Iter.leader []))).compose (easy_zip _ _)
  have box : Code.Easy (fun xs : List Dusk.Pair => [xs]) := by fun_prop
  filter_upwards [eventually_ge_atTop 4,easy_eventually gather,easy_eventually box,EffectiveMix.scalarFamily]
    with R hR g b s
  exact ((Family.fixed g).comp ((EffectiveSelect.table (by omega) KernelComputableDyadic.zero s).mapping hR)).comp
    (Family.fixed b)

def unaryTag {n : ℕ} (k : Fin n) : Tally := tally k.val

theorem tag_erase {n : ℕ} (l : List (Fin n)) : send (l.map unaryTag) = send l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,send_cons,ih]; rfl

/-- On the input used by the scale grammar, the compiled nonlinear branch
selection returns exactly the address-dependent mathematical output. -/
theorem finish_rows {q : ℕ} {F : Type} (values : List Coeff) (rows : List F)
    (sig : F → Fin q → ZMod 2) (x y : F → Dusk.Pair)
    (he : ∀ z ∈ rows, KernelScaleRecord.applyCoeff (KernelComputableSelector.table values (sig z)) (x z) = y z) :
    finish values ((rows.map fun z => unaryTag (KernelComputableAddress.packSig q (sig z))),[rows.map x]) = [rows.map y] := by
  unfold finish
  simp only [List.headD_cons,fair,List.map_map,Function.comp_def]
  apply congrArg (fun l => [l])
  apply List.map_congr_left
  intro z hz
  change KernelScaleRecord.applyCoeff (coefficient (values.getD (tally _).length _)) _ = _
  rw [tally_length]
  exact he z hz

end EffectiveScale

end NearSquareRoot
end Computability
end OAI
