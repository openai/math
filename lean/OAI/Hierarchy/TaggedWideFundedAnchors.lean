import OAI.Hierarchy.TaggedWideFrozenSlots
import OAI.Hierarchy.TaggedWideFrozenSeries
import OAI.Hierarchy.ProtocolRAMFrozenWindowPorts
import OAI.Hierarchy.TaggedWideFundedCutPins

namespace OAI
/-! # Linking original socket receipts to the three control fields of a purchased cut -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing CallPool
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterGroups TaggedShorterReportAdvice TaggedShorterSupergroups
open ProtocolRAMPackedPlacement Tagged.WideStack
open scoped Fin.CommRing Classical
set_option quotPrecheck false

variable {G : Type*} {portCount : G→ℕ} {H W lanes : ℕ}

section DirectoryAnchor
variable (setup : Format) (dir : Directory portCount H)
variable (a : Inputs) (old : Fin (setup.withDirectory dir).N→ProtocolRAMEmit.Row) (m : Memory W)
variable (limits : (setup.withDirectory dir).Limits W old) (positive : 0<H)
    (socket : Receipt ((setup.withDirectory dir).rows a m old) (setup.withDirectory dir).w portCount)
    (groupAt : ∀s (i : Live ((setup.withDirectory dir).rows a m old) (setup.withDirectory dir).w),
      (dir.group (socket s i).1).val=((setup.withDirectory dir).rows a m old i.val).group)
    (lanesFit : ∀i,pieces old (setup.withDirectory dir).w i≤lanes)
    (widthFit : H*lanes≤(setup.withDirectory dir).D)
    (slotAt : ∀s (i : Live ((setup.withDirectory dir).rows a m old) (setup.withDirectory dir).w),
      (setup.withDirectory dir).starts a m s i.val=(dir.slot (socket s i).1 (socket s i).2).val*lanes)

local notation "f" => setup.withDirectory dir

include positive socket groupAt lanesFit widthFit slotAt in
/-- Both sides' physical port numbers come from the original live row receipt.
The same translated rows and placement construct the masks read by the cut. -/
def Format.anchorOfPorts : (f).Anchored a m old limits :=
  ⟨group_fit dir ((f).rows a m old) socket groupAt,
   ProtocolRAMPackedPlacement.bound dir positive ((f).rows a m old) limits.order.injective
     socket groupAt lanesFit widthFit,
   placement dir positive ((f).rows a m old) limits.order.injective socket groupAt lanesFit widthFit,
   publish_located dir positive ((f).rows a m old) limits.order.injective socket groupAt lanesFit widthFit
     ((f).starts a m) slotAt⟩

include slotAt in
theorem Format.anchorOfPorts_place (g : Fin dir.groups) (b : Bool) :
    (setup.anchorOfPorts dir a old m limits positive socket groupAt lanesFit widthFit slotAt).pl g b =
    (common ((f).rows a m old) (f).w (f).menu (f).γ g.val limits.order.injective).symm.toEmbedding.trans
      (staticUnit ((f).rows a m old) g (fun side => dir.livePort positive ((f).rows a m old) (f).w (socket side))
        (fun side => dir.live_distinct positive ((f).rows a m old) (socket side) (groupAt side) g)
        lanesFit widthFit b) := rfl

end DirectoryAnchor

/-- An original reported group and socket have already been next-fit packed by the
role publisher. The frozen lookup tables store the packed group and zero offset. -/
def packedDirectory (groups ports : ℕ) : Directory (fun _ : Fin groups=>ports) ports where
  groups := groups
  group := id
  base := fun _=>0
  fits := fun _=>by omega
  separate := fun _ _ _ _ h _ _ eq=>⟨h,Nat.add_left_cancel eq⟩

@[simp] theorem packedDirectory_slot (groups ports : ℕ) (g : Fin groups) (p : Fin ports) :
    (packedDirectory groups ports).slot g p=p := by apply Fin.ext; exact Nat.zero_add _

section Installed
variable {F : Type*} [Field F] (s : Format) (ports lanes : ℕ)
variable (src : Inputs) (prior : Fin (s.withSlots ports lanes).N→ProtocolRAMEmit.Row) (before : Memory W)
    (fit : (s.withSlots ports lanes).Limits W prior)
variable (installed : Leaf.Installed F (s.withSlots ports lanes).groups ports lanes
      (s.withSlots ports lanes).w (s.withSlots ports lanes).menu (s.withSlots ports lanes).γ
      ((s.withSlots ports lanes).rows src before prior))
    (groupsRead : ∀i,0<pieces prior (s.withSlots ports lanes).w i →
      ((s.withSlots ports lanes).rows src before prior i).group<(s.withSlots ports lanes).groups)
    (slotsRead : ∀b (i : Live ((s.withSlots ports lanes).rows src before prior) (s.withSlots ports lanes).w),
      (s.withSlots ports lanes).starts src before b i.val=(installed.port b i.val).val*lanes)

local notation "fmt" => s.withSlots ports lanes
local notation "records" => (s.withSlots ports lanes).rows src before prior

include installed groupsRead slotsRead in
/-- At a positive socket, the original controller printed the port times the lane
pitch. Hence the RAM and the two installed compactors use exactly the same embedding. -/
def Format.anchorInstalled : (fmt).Anchored src before prior fit where
  groupFit := groupsRead
  bound := installed.bank.bound
  pl := installed.bank.place
  located := by
    intro side g u
    change ((staticUnit records g installed.port (installed.distinct g) installed.room le_rfl side)
      ((common records (fmt).w (fmt).menu (fmt).γ g.val installed.unique).symm
        ((common records (fmt).w (fmt).menu (fmt).γ g.val fit.order.injective) u))).val=_
    rw [Equiv.symm_apply_apply]
    rcases u with ⟨i,j⟩
    let live : Live records (fmt).w := ⟨i.val,Nat.zero_lt_of_lt j.isLt⟩
    change j.val+lanes*(installed.port side live.val).val=(fmt).starts src before side live.val+j.val
    rw [slotsRead side live,Nat.mul_comm lanes,Nat.add_comm]

/-- Each control word in the returned numeric image is a field of the same
installed placement, including positions absent from the sparse writes. -/
theorem Format.anchorInstalled_field (q : TaggedShorterScatter.Field (fmt).window.C (fmt).D) :
    (s.anchorInstalled ports lanes src prior before fit installed groupsRead slotsRead).word prior (.inr q) =
      (TaggedShorterScatter.contents installed.bank.counts installed.bank.bound fit.batch fit.idFits
        installed.bank.place q : Word W) := rfl

end Installed

/-- The first address after the scatter is the width array in the same native window. -/
theorem Format.scatter_end (s : Format) (start : ℕ) :
    s.window.base start+(s.window.C+2*(s.window.C*2*s.D))≤ s.window.stop start := by
  change s.window.widthBase start≤ s.window.widthSrc start+s.window.tape
  unfold Size.widthSrc Size.src
  omega

/-- On a dense observation, the very same source address is the offset used by
the fixed external pin. This holds after all later windows and the final sweep. -/
theorem Format.scatter_observed {s : Format} {U : ℕ} (r : ℕ)
    (word : U≤2^W) (extent : s.window.stop r≤U) (out : Memory W) {a : Inputs}
    (old : Fin s.N→ProtocolRAMEmit.Row) {m : Memory W} {limits : s.Limits W old}
    (A : s.Anchored a m old limits)
    (stored : ∀p,out (s.address r p)=A.word old p)
    (f : TaggedShorterScatter.Field s.window.C s.D) :
    out (Tagged.WideControlJoin.Gate.denseAddr word
      (frozenRow (s.window.base r) ((s.scatter_end r).trans extent) f)).val =
      (TaggedShorterScatter.contents _ A.bound limits.batch limits.idFits A.pl f : Word W) :=
  stored (.inr f)

end Hierarchy.ProtocolRAMFrozenWindow

end
end OAI
