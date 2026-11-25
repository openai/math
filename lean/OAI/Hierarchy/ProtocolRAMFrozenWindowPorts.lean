import OAI.Hierarchy.ProtocolRAMFrozenWindowRun

namespace OAI
/-! # Executing one priced format at its original immutable pair of physical socket numbers -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterGroups TaggedShorterReportAdvice TaggedShorterSupergroups
open ProtocolRAMPackedPlacement
open scoped Fin.CommRing Classical

variable {G : Type*} {portCount : G→ℕ} {H : ℕ}

/-- The input directory determines the number of output supergroups. The two receipts may use
different socket numbers inside their owner and need only exist at positive-width pieces. -/
def Format.withDirectory (format : Format) (dir : Directory portCount H) : Format :=
  {format with groups:=dir.groups}

variable (setup : Format) (dir : Directory portCount H)
local notation "f" => setup.withDirectory dir

theorem Format.run_of_ports (W r lanes : ℕ) (a : Inputs) (old : Fin (f).N→ProtocolRAMEmit.Row) (m : Memory W)
    (ready : (f).Ready W r a) (data : (f).InputWords r a old m) (limits : (f).Limits W old)
    (positive : 0<H) (socket : Receipt ((f).rows a m old) (f).w portCount)
    (groupAt : ∀s (i : Live ((f).rows a m old) (f).w),(dir.group (socket s i).1).val=((f).rows a m old i.val).group)
    (lanesFit : ∀i,pieces old (f).w i≤lanes) (widthFit : H*lanes≤(f).D)
    (slotAt : ∀s (i : Live ((f).rows a m old) (f).w),
      (f).starts a m s i.val=(dir.slot (socket s i).1 (socket s i).2).val*lanes) :
    let rows:=(f).rows a m old
    let s:=(f).window
    let addr:=TaggedShorterScatter.layout s.C (f).D (s.base r) (s.boardFit r W ready.room)
    let counts:=TaggedShorterReportedPublish.size (groups:=(f).groups) rows (f).w (f).menu (f).γ
    let pl (g : Fin (f).groups) (b : Bool) := placement (menu:=(f).menu) (γ:=(f).γ) dir positive rows
      limits.order.injective socket groupAt lanesFit widthFit g b
    let bound:=ProtocolRAMPackedPlacement.bound (menu:=(f).menu) (γ:=(f).γ) dir positive rows
      limits.order.injective socket groupAt lanesFit widthFit
    ∃ out,((f).phase W r a).Exec m out ((f).clock r a) ∧
      (∀x : TaggedShorterSlotWidth.Slot (f).groups (f).D,out (TaggedShorterSlotWidth.index (s.widthBase r) x)=
        (TaggedShorterSlotWidth.value pl (TaggedShorterSlotWidth.reportWidth rows (f).w (f).menu (f).γ limits.order.injective) x:Word W)) ∧
      (∀x : TaggedShorterScatter.Field s.C (f).D,out (addr x).val=
        (TaggedShorterScatter.contents counts bound limits.batch limits.idFits pl x:Word W)) ∧
      ∀u,u<r → out u=m u := by
  intro rows s addr counts pl bound
  exact (f).run W r a old m ready data limits
    (group_fit dir rows socket groupAt) bound pl
    (publish_located dir positive rows limits.order.injective socket groupAt lanesFit widthFit ((f).starts a m) slotAt)

end Hierarchy.ProtocolRAMFrozenWindow
end

end OAI
