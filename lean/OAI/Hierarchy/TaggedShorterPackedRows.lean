import OAI.Hierarchy.TaggedShorterSupergroups
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Unique immutable row ports after merging whole protocol groups -/

noncomputable section
namespace Hierarchy.TaggedShorterSupergroups.Directory
open Tagged.WideStack ProtocolRAMReportedPorts
open scoped Classical

variable {G : Type*} {size : G → ℕ} {H N w scale γ : ℕ}

/-- The actual physical port of an original row. It is independent of the
activity of every other group in the same next-fit bin. -/
def packedPort (d : Directory size H) (owner : Fin N → G) (port : (i : Fin N) → Fin (size (owner i))) :
    Fin N → Fin H := fun i=>d.slot (owner i) (port i)

/-- On a fixed reported group and width class, equal frozen coordinates
identify the same old group and then the same original incident row. Only
the occupied rows need a valid group label. -/
theorem packed_distinct (d : Directory size H) (rows : Fin N → ProtocolRAMEmit.Row)
    (owner : Fin N → G) (port : (i : Fin N) → Fin (size (owner i)))
    (numbered : ∀ i j, 0<pieces rows w i → 0<pieces rows w j → owner i=owner j →
      (port i).val=(port j).val → i=j)
    (groupRead : ∀ i,0<pieces rows w i → (d.group (owner i)).val=(rows i).group)
    (g : Fin d.groups) : PortDistinct rows w scale γ g.val (d.packedPort owner port) := by
  intro i hi j hj same
  have groupEq : d.group (owner i.val)=d.group (owner j.val) := Fin.ext
    ((groupRead i.val hi).trans (i.property.1.trans (j.property.1.symm.trans (groupRead j.val hj).symm)))
  obtain ⟨labels,addresses⟩ := d.separate (owner i.val) (owner j.val) _ _ groupEq
    (port i.val).isLt (port j.val).isLt (congrArg Fin.val same)
  exact Subtype.ext (numbered i.val j.val hi hj labels addresses)

/-- Reuse the concrete injection of live path records into old group/socket
pairs to obtain the premise of the packed-board matcher on every bin. -/
theorem packed_of_receipts (d : Directory size H) (rows : Fin N → ProtocolRAMEmit.Row)
    (owner : Fin N → G) (port : (i : Fin N) → Fin (size (owner i)))
    (receipt : {i : Fin N // 0<pieces rows w i} ↪ (Σ g,Fin (size g)))
    (named : ∀ i,receipt i=⟨owner i.val,port i.val⟩)
    (groupRead : ∀ i,0<pieces rows w i → (d.group (owner i)).val=(rows i).group)
    (g : Fin d.groups) : PortDistinct rows w scale γ g.val (d.packedPort owner port) := by
  apply packed_distinct d rows owner port _ groupRead g
  intro i j hi hj own eq
  let x : {i : Fin N // 0<pieces rows w i} := ⟨i,hi⟩
  let y : {i : Fin N // 0<pieces rows w i} := ⟨j,hj⟩
  change x.val=y.val
  apply congrArg Subtype.val
  apply receipt.injective
  rw [named x,named y]
  apply Sigma.ext own
  exact (Fin.heq_ext_iff (congrArg size own)).mpr eq

/-- A foreign-stage or dormant input has no source group. The positive
supergroup capacity provides a harmless default physical port in that case. -/
def livePort (d : Directory size H) (hH : 0<H) (rows : Fin N → ProtocolRAMEmit.Row) (w : ℕ)
    (receipt : {i : Fin N // 0<pieces rows w i} ↪ (Σ g,Fin (size g))) (i : Fin N) : Fin H :=
  if hi : 0<pieces rows w i then (d.place (receipt ⟨i,hi⟩)).2 else ⟨0,hH⟩

theorem livePort_at (d : Directory size H) (hH : 0<H) (rows : Fin N → ProtocolRAMEmit.Row)
    (receipt : {i : Fin N // 0<pieces rows w i} ↪ (Σ g,Fin (size g)))
    (i : {i : Fin N // 0<pieces rows w i}) :
    d.livePort hH rows w receipt i.val=d.slot (receipt i).1 (receipt i).2 := by
  exact dite_eq_left i.property

/-- This version also applies to an empty collection of original groups.
Rows without pieces require neither an owner nor an old socket. -/
theorem live_distinct (d : Directory size H) (hH : 0<H) (rows : Fin N → ProtocolRAMEmit.Row)
    (receipt : {i : Fin N // 0<pieces rows w i} ↪ (Σ g,Fin (size g)))
    (groupRead : ∀ i,(d.group (receipt i).1).val=(rows i.val).group) (g : Fin d.groups) :
    PortDistinct rows w scale γ g.val (d.livePort hH rows w receipt) := by
  apply portDistinct_of_grouped rows w scale γ (d.livePort hH rows w receipt)
    (receipt.trans d.place) groupRead _ g
  intro i
  exact (d.livePort_at hH rows receipt i).symm

end Hierarchy.TaggedShorterSupergroups.Directory

end
end OAI
