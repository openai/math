import OAI.Hierarchy.TaggedWideReportedBonds
import OAI.Hierarchy.TaggedWideLeafFiniteSums

namespace OAI
/-! # Reported bonds under the caller's label, private-port and word enumerations -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {T F : Type*} [Fintype T] [CommSemiring F] {N : ℕ}
    (groups : T → ℕ) (w m : ℕ) (key : T ↪ ℕ × ℕ)
    (raw : Fin N → ProtocolRAMEmit.Row) (positive : Fin N → Prop) (stage : Fin N → ℕ)

set_option quotPrecheck false in
local notation "reported" => fun t : T => atScale positive stage (key t).1 raw
set_option quotPrecheck false in
local notation "classIndex" => fun t : T => (key t).2
set_option quotPrecheck false in
local notation "privateRows" => {i : Fin N // ¬positive i}
set_option quotPrecheck false in
local notation "privateWidth" => fun e : privateRows => (raw e.val).width

/-- Sum over the three enumerations supplied by the physical contraction.
The summands use the original positive row placement and the original paired
private endpoint bits. -/
theorem reported_bonds_fintypes (hw : 0 < w)
    (unique : ∀ t, Function.Injective fun i => (reported t i).link)
    (capacity : privateRows → ℕ) (room : ∀ i, privateWidth i ≤ capacity i)
    (cover : ∀ i, positive i → 0 < (raw i).width →
      ∃ t, key t = (stage i, widthIndex m ((raw i).width / (w : ℝ))) ∧ (raw i).group < groups t)
    (φ : Lanes groups classIndex reported w m → PrivatePorts capacity → F)
    (labelEnum : Fintype (Lanes groups classIndex reported w m))
    (portEnum : Fintype (PrivatePorts capacity))
    (wordEnum : Fintype ((i : Fin N) → Fin (2 ^ (raw i).width))) :
    Leaf.sumWith labelEnum (fun z =>
      if ∀ t e j, z t e j = true → originalPrefix groups classIndex reported w m unique t e j then
        Leaf.sumWith portEnum (fun y =>
          (∏ e, if ∀ j : Fin (capacity e), j.val < privateWidth e → y false e j = y true e j
            then (1 : F) else 0) *
            (if EndsPadded privateWidth capacity y then φ z y else 0))
      else 0) =
      Leaf.sumWith wordEnum (fun a =>
        φ (expandedLabels groups classIndex reported w m unique (fun p =>
              let q := edgeBit key groups raw positive stage w m p
              (a q.1.val).val.testBit q.2.val))
          (privateEncode privateWidth capacity (fun e j => (a e.val).val.testBit j.val))) := by
  revert labelEnum portEnum wordEnum
  let nativeLabels : Fintype (Lanes groups classIndex reported w m) := inferInstance
  let nativePorts : Fintype (PrivatePorts capacity) := inferInstance
  let nativeWords : Fintype ((i : Fin N) → Fin (2 ^ (raw i).width)) := inferInstance
  intro labelEnum portEnum wordEnum
  have hl : labelEnum = nativeLabels := Subsingleton.elim _ _
  have hp : portEnum = nativePorts := Subsingleton.elim _ _
  have hw' : wordEnum = nativeWords := Subsingleton.elim _ _
  subst labelEnum
  subst portEnum
  subst wordEnum
  exact reported_bonds groups w m key raw positive stage hw unique capacity room cover φ

end Hierarchy.Tagged.WideStack

end
end OAI
