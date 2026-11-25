import OAI.Hierarchy.DescentRetainedSevenBits
import OAI.Hierarchy.DescentDatedLocalScale
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! # Uniform calendar rates for the retained reset program -/
namespace Hierarchy.DescentRetainedSeven
open DescentCompiler DescentCompiler.TerminalScale DescentPlacedInvoiceVolume DescentResetRetainedSetup
noncomputable section
open DescentDatedAddressBook
variable {ι : ℕ→Type*} {J : ℕ→ℕ}

local infixl:65 " +ₛ " => SmallAt.add
local infixl:70 " *ₛ " => SmallAt.mul

theorem scaled_movement (L : ∀h,ι h→DescentResetRetainedSetup.Layout)
    (dimension : SmallAt J (fun h i=>(L h i).high+(L h i).low))
    (previousNodes : SmallAt J (fun h i=>(L h i).previousNodes))
    (previousArgs : SmallAt J (fun h i=>(L h i).previousArgs))
    (blocks : SmallAt J (fun h i=>(L h i).blocks)) :
    SmallAt J (fun h i=>(L h i).movementUnits) := by
  have switches : SmallAt J (fun h i=>(DescentGLNielsen.schedule ((L h i).high+(L h i).low)).length):=
    SmallAt.of_le (((SmallAt.const J 3).mul dimension).mul dimension) (fun h i=>DescentGLNielsen.length_le _)
  let num (n : ℕ) := SmallAt.const (ι := ι) J n
  have fieldCount := num 2 +ₛ num 7 *ₛ previousArgs
  have sourceCount := fieldCount *ₛ blocks
  have channels := fieldCount *ₛ previousNodes
  have readCost := num 1 +ₛ blocks *ₛ num 23
  have literal :=
    num 4 *ₛ ((num 1 +ₛ switches) *ₛ num 1 +ₛ switches *ₛ num 1 +ₛ dimension *ₛ num 1 +ₛ num 1)
      +ₛ num 2 *ₛ (channels *ₛ num 1 +ₛ num 1) +ₛ switches *ₛ num 1 +ₛ (num 7 *ₛ switches +ₛ num
      1) *ₛ (num 2 *ₛ (channels *ₛ num 1 +ₛ num 1) +ₛ num 1)
  have compute :=
    num 8 +ₛ num 10 *ₛ literal +ₛ (num 4 +ₛ channels *ₛ (num 4 +ₛ num 1 *ₛ (num 2 *ₛ readCost +ₛ
      num 4)) +ₛ (num 4 +ₛ switches *ₛ num 42 *ₛ num 1 +ₛ (num 4 +ₛ switches *ₛ (num 4 +ₛ
      channels *ₛ num 1 *ₛ num 224)))) +ₛ num 7 *ₛ (num 15 *ₛ (literal +ₛ num 2) +ₛ (num 15 +ₛ
      channels *ₛ (num 11 +ₛ num 4 *ₛ readCost) *ₛ num 1 +ₛ (num 87 +ₛ (num 15 +ₛ switches *ₛ num
      451 *ₛ num 1))))
  have oldMount := num 4 +ₛ num 10 *ₛ previousNodes +ₛ num 7 *ₛ (num 15 *ₛ (previousNodes +ₛ num 1))
  have blockMount :=
    num 4 +ₛ num 10 *ₛ (num 2 *ₛ blocks) +ₛ num 7 *ₛ (num 15 *ₛ (num 2 *ₛ blocks +ₛ num 1))
  exact
    num 109 +ₛ sourceCount *ₛ num 8192 +ₛ oldMount +ₛ blockMount +ₛ compute +ₛ (num 109 +ₛ
      channels *ₛ num 8192)

theorem scaled_tariff {N X Q K W : ∀h,ι h→ℕ} (outputs : SmallAt J N) (sheets : SmallAt J X)
    (query : SmallAt J Q) (shapes : SmallAt J K) (work : SmallAt J W) :
    SmallAt J (fun h i=>controlFactor (K h i) (W h i)) ∧
    SmallAt J (fun h i=>stemFactor (N h i*K h i) (X h i) (Q h i)+suffixFactor (K h i) (N h i) (X h i)) := by
  let num (n : ℕ) := SmallAt.const (ι := ι) J n
  have printed :=
    num 4 +ₛ num 10 *ₛ (shapes *ₛ num 2) +ₛ num 7 *ₛ (num 15 *ₛ (shapes *ₛ num 2 +ₛ num 1))
  have doublePrint :=
    num 4 +ₛ num 10 *ₛ (num 2 *ₛ shapes *ₛ num 2) +ₛ num 7 *ₛ (num 15 *ₛ (num 2 *ₛ shapes *ₛ num
      2 +ₛ num 1))
  have control :=
    printed +ₛ (num 4 +ₛ shapes *ₛ (num 4 +ₛ num 2 *ₛ (work +ₛ num 12) +ₛ num 4) +ₛ num 7 *ₛ (num
      15 +ₛ shapes *ₛ (num 11 +ₛ num 4 *ₛ (work +ₛ num 12)))) +ₛ (num 109 +ₛ shapes *ₛ num 2048
      *ₛ num 5) +ₛ doublePrint
  have nodes := outputs *ₛ shapes
  have volume := num 5 +ₛ num 3 *ₛ nodes +ₛ sheets +ₛ nodes *ₛ sheets
  have stem :=
    num 4096 *ₛ volume +ₛ num 4 +ₛ nodes *ₛ (num 4 +ₛ (num 2 *ₛ query +ₛ num 4)) +ₛ num 7 *ₛ (num
      15 +ₛ nodes *ₛ (num 11 +ₛ num 4 *ₛ query))
  have suffix :=
    num 2 *ₛ (num 4 +ₛ num 10 *ₛ (num 6 +ₛ num 2 *ₛ shapes) +ₛ num 7 *ₛ (num 15 *ₛ (num 7 +ₛ num
      2 *ₛ shapes))) +ₛ num 4 +ₛ outputs *ₛ sheets *ₛ num 1294 +ₛ num 7 *ₛ (num 15 +ₛ outputs *ₛ
      sheets *ₛ num 2583)
  exact ⟨control,stem +ₛ suffix⟩

/-- Bounds the genuine native multiplier by calibrating the scalar dimensions of
the dated input. The matrix contributes at most three times its dimension squared. -/
theorem Chart.scaled_units (C : ∀h,ι h→Chart) (U : ∀h,ι h→ℕ) (work : SmallAt J U)
    (dimension : SmallAt J (fun h i=>(C h i).retained.high+(C h i).retained.low))
    (previousNodes : SmallAt J (fun h i=>(C h i).retained.previousNodes))
    (previousArgs : SmallAt J (fun h i=>(C h i).retained.previousArgs))
    (issuedNodes : SmallAt J (fun h i=>(C h i).retained.nodes))
    (issuedArgs : SmallAt J (fun h i=>(C h i).retained.args))
    (blocks : SmallAt J (fun h i=>(C h i).retained.blocks))
    (sheets : SmallAt J (fun h i=>(C h i).placement.blocks))
    (shapes : SmallAt J (fun h i=>(C h i).placement.shapes)) :
    SmallAt J (fun h i=>(C h i).units (U h i)) :=by
  let num (n : ℕ) := SmallAt.const (ι := ι) J n
  have motion := scaled_movement (fun h i=>(C h i).retained) dimension previousNodes previousArgs blocks
  have channels := (num 2 +ₛ num 7 *ₛ previousArgs) *ₛ previousNodes
  have outputs := num 14 *ₛ issuedArgs *ₛ issuedNodes +ₛ issuedNodes
  have query := num 64 +ₛ channels *ₛ num 36
  have factors := scaled_tariff outputs sheets query shapes work
  have channelMount :=
    num 4 +ₛ num 10 *ₛ (channels +ₛ num 1) +ₛ num 7 *ₛ (num 15 *ₛ (channels +ₛ num 1 +ₛ num 1))
  have outputMount := num 4 +ₛ num 10 *ₛ outputs +ₛ num 7 *ₛ (num 15 *ₛ (outputs +ₛ num 1))
  exact motion +ₛ factors.1 +ₛ channelMount +ₛ outputMount +ₛ factors.2

end
end Hierarchy.DescentRetainedSeven

end OAI
