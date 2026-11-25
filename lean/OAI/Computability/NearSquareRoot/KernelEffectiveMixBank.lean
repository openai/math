import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankCompile
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyIterate
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyMapping

/-! # Effective bank-level mixing for variable instruction dimensions

Compilation uses the input and output arities to repeat two fixed bank
commands. The per-address arithmetic command is mapped across the gathered
columns. The same set of registers suffices for every instruction.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication IntegerMultiplication.Code CommonRegisters GeneratorSyntax
open KernelEffectiveFamily RegisterSelect Filter

variable {P H : Type} [Primcodable P] [Codec H]

theorem collect_family : ∀ᶠ R in atTop, Family R collect := by
  filter_upwards [easy_eventually easy_gatherInit, easy_eventually easy_gatherStep,
    easy_eventually (Easy.snd : Code.Easy (@Prod.snd Bank Bank))] with R init step done
  exact ((Family.fixed init).comp (Family.iterate_fixed step)).comp (Family.fixed done)

theorem distribute_family : ∀ᶠ R in atTop, Family R distribute := by
  filter_upwards [easy_eventually easy_scatterInit, easy_eventually easy_scatterStep,
    easy_eventually easy_scatterDone] with R init step done
  exact ((Family.fixed init).comp (Family.iterate_fixed step)).comp (Family.fixed done)

theorem finish_family (i o : P → ℕ) (hi : Computable i) (ho : Computable o) (f : P → RowFunction)
    (hf : ∀ᶠ R in atTop, Family R f) : ∀ᶠ R in atTop, Family R (fun p => finish (i p) (o p) (f p)) := by
  let shape (z : List Tally × Bank) := (ruler z.1,z.2)
  have hs : Code.Easy shape := (Easy.ruler Easy.fst).pair Easy.snd
  have fstE : Code.Easy (fun z : List Tally × Bank => z.1) := Easy.fst
  have zipE := easy_zip ([] : Tally) ([] : List Record)
  filter_upwards [eventually_ge_atTop 4,collect_family,distribute_family,hf,
    easy_eventually hs,easy_eventually fstE,easy_eventually zipE] with R hR collect' dist row shape' fst' zip'
  have g := (Family.fixed shape').comp (collect'.reindex i hi)
  exact ((((Family.pair (by omega) (Family.fixed fst') g).comp (Family.fixed zip')).comp
    (Family.mapping hR row)).comp (dist.reindex o ho))

/-- A single effective syntax generator for all arities and coefficient
tables. Its witnesses run on the actual P192 packet and restore its header. -/
theorem compile (key : H → Rulers) (hk : Code.Easy key) (i o : P → ℕ) (hi : Computable i)
    (ho : Computable o) (f : P → RowFunction) (hf : ∀ᶠ R in atTop, Family R f) :
    ∀ᶠ R in atTop, ∃ c : P → Cmd, Effective ltr c ∧
      ∀ p, Within R (c p) ∧ Sound (c p) key (i p) (o p) (f p) :=
  assemble key hk i o f (finish_family i o hi ho f hf)

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
