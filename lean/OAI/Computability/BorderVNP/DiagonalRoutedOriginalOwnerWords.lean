import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports

/-! # Original row ownership under a registered change of owner representation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

/-- The owner word read at every address is determined by its selector,
cell label and owner function. This also covers addresses outside the real
cells when the two routed assignments have differently typed payloads. -/
theorem routedOwnerWord_of_original {a : CubeArena.Layout} {R : ℕ}
    {packetOwner residentOwner :
      (Packet a.n a.header.d a.header.blocks → Selector a.n a.K a.h) → Fin a.header.d → Fin (R+1)}
    {packetLabel residentLabel : Fin a.cells → Label (a.n+1) a.header.d}
    {packet : NativeAssignments.Routed (b:=a.b) (s:=a.s) packetOwner}
    {resident : NativeAssignments.Routed (b:=a.b) (s:=a.s) residentOwner}
    (ownerNames : packetOwner=residentOwner) (labelNames : packetLabel=residentLabel)
    (selector : packet.1=resident.1) :
    routedOwnerWord a packetOwner packetLabel packet=routedOwnerWord a residentOwner residentLabel resident := by
  subst residentOwner
  subst residentLabel
  funext c
  unfold routedOwnerWord
  rw [selector]

/-- Original host observations on the installed owner-word array apply to
the same physical cells when the registered packet uses those owner words. -/
theorem hostedAtOwnerWords {cells sites team : ℕ} {chart : ReportLayout}
    {home : Fin sites → Fin cells} {bundle : Fin sites → ReportBundle}
    {packet resident bank supply width : ℕ → ℕ} {digits : ℕ → Fin chart.gadgets → Fin chart.countWidth → Bool}
    {outcome : Fin sites → Prop}
    (served : ∀ j, (∃ c ∈ sourceCells chart home bundle team resident bank supply width digits,
      c.number=(home j).val) → outcome j) (same : packet=resident) :
    ∀ j, (∃ c ∈ sourceCells chart home bundle team packet bank supply width digits,
      c.number=(home j).val) → outcome j := by
  subst packet
  exact served

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
