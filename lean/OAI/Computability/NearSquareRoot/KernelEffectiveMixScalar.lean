import OAI.Computability.NearSquareRoot.KernelEffectiveMix

/-! # Emitting the one-by-one marked dyadic product -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveMix

open IntegerMultiplication Code KernelPass KernelPass.ComputableSyntax KernelPassMix
open KernelEffectiveFamily RegisterSelect Filter

def singleton (c : KernelComputableDyadic.Code) : Op := (0,[1,1],[c])

theorem primrec_singleton : Primrec singleton :=
  (Primrec.const 0).pair ((Primrec.const [1,1]).pair (Primrec.list_cons.comp Primrec.id (.const [])))

private theorem singleton_table (c : KernelComputableDyadic.Code) :
    coeff (singleton c) = fun _ _ => KernelComputableDyadic.coefficient c := by
  funext b a
  change Fin 1 at a b
  simp [coeff,raw,singleton,arg,List.getD]

/-- Using a one-by-one emitted row gives the physical dyadic leaf used by the
address-dependent based-on-signature scaling program. -/
theorem scalarFamily :
    ∀ᶠ R in atTop, Family R (fun c => KernelScaleRecord.applyCoeff (KernelComputableDyadic.coefficient c)) := by
  have prep : Code.Easy (fun x : Dusk.Pair => (ruler x.1,[x])) := by fun_prop
  filter_upwards [markedFamily, easy_eventually prep, easy_eventually (Iter.leader (([],[]) : Dusk.Pair))] with
    R mx hp hi
  have core := ((Family.fixed hp).comp (mx.reindex singleton primrec_singleton.to_comp)).comp (Family.fixed hi)
  apply core.congr
  intro c x
  rw [singleton_table]
  rfl

end EffectiveMix

end NearSquareRoot
end Computability
end OAI
