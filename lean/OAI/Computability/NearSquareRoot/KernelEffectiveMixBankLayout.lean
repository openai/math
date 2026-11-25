import OAI.Computability.NearSquareRoot.KernelEffectiveTranspose

/-! # The effective transpose on Walsh record banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication IntegerMultiplication.Code MixBankLayout

abbrev Record := Dusk.Pair
abbrev Bank := List (List Record)
abbrev Rulers := Tally × Tally

private abbrev blank : Record := ([],[])

abbrev prepend := KernelEffectiveTranspose.prepend blank
abbrev gatherInit := KernelEffectiveTranspose.gatherInit (X := Record)
abbrev gatherStep := KernelEffectiveTranspose.gatherStep blank
abbrev collect := KernelEffectiveTranspose.collect blank
abbrev scatterInit := KernelEffectiveTranspose.scatterInit (X := Record)
abbrev scatterStep := KernelEffectiveTranspose.scatterStep blank
abbrev scatterDone := KernelEffectiveTranspose.scatterDone (X := Record)
abbrev distribute := KernelEffectiveTranspose.distribute blank

theorem easy_gatherInit : Code.Easy gatherInit := KernelEffectiveTranspose.easy_gatherInit

theorem easy_gatherStep : Code.Easy gatherStep := KernelEffectiveTranspose.easy_gatherStep blank

theorem collect_exact (r : Tally) (rows : Bank) :
    collect rows.length (r,rows) = align rows.length blank (r,rows) :=
  KernelEffectiveTranspose.collect_exact blank r rows

theorem easy_scatterInit : Code.Easy scatterInit := KernelEffectiveTranspose.easy_scatterInit

theorem easy_scatterStep : Code.Easy scatterStep := KernelEffectiveTranspose.easy_scatterStep blank

theorem easy_scatterDone : Code.Easy scatterDone := KernelEffectiveTranspose.easy_scatterDone

theorem distribute_exact (n : ℕ) (columns : Bank) : distribute n columns = scatter n blank columns :=
  KernelEffectiveTranspose.distribute_exact blank n columns

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
