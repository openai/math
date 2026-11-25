import OAI.Hierarchy.DescentTerminalWidthRun
import OAI.Hierarchy.DescentTerminalRoleChannel
import OAI.Hierarchy.DescentTerminalMaskAllocation
import OAI.Hierarchy.DescentTerminalBundleRows
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.DescentLivePrivateWords

namespace OAI
/-! # A literal scan supplies the widths of the live private terminal words -/
namespace Hierarchy.DescentTerminalIssuedWidths
open DescentSIMDLookup DescentTerminalVertexFields DescentTerminalChronologicalBooks
open ProtocolRAM ProtocolRAMGeneratedWrite Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

section Mask
variable {q t H N A p groups blocks shops bw : ℕ} (out : ℕ) (m : Memory bw) (machine : MaskedShelf blocks)
    (room : out+blocks*shops<2^bw) (fit : groups*span q t H N A p≤bw)
    (b : Fin blocks) (placed : (machine.channel (finProdFinEquiv (b,(4:Fin 8).succ))).base=out+b.val*shops)
    (capacity : shops≤(machine.channel (finProdFinEquiv (b,(4:Fin 8).succ))).size)
local notation "done" => final out blocks shops H groups p m
local notation "meas" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)
local notation "wd" => Nat.clog 2 (p+1)

include room fit placed capacity in
theorem width_read (h : Fin shops) (g : Fin groups) (j : Fin H) :
    venueField (cellAt (meas machine done h) (finProdFinEquiv (g,b))) (hiddenWidth j)=p := by
  have hosts:shops≤blocks*shops:=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have index:h.val<2^bw:=by have:=h.isLt;omega
  have bits:= (within_span q t H N A p groups).trans fit
  have address:out+b.val*shops+h.val=out+(finProdFinEquiv (b,h)).val := by
    change _=out+(h.val+shops*b.val)
    ring
  rw [venue_digit]
  change digit wd j.val ((cellAt (meas machine done h) (finProdFinEquiv (g,b))) 4).val=_
  rw [cell_digit,measured_channel]
  change digit wd j.val (digit (H*wd) g.val
    (((machine.channel (finProdFinEquiv (b,(4:Fin 8).succ))).read done (h.val:Word bw)).val%2^(H*wd*groups)))=_
  rw [digit_clip,Nat.mul_comm H wd,Bank.read,Fin.val_cast_of_lt index,
    Nat.mod_eq_of_lt (h.isLt.trans_le capacity),placed,address]
  exact issued_digit out blocks shops H groups p m room bits (finProdFinEquiv (b,h)) g j
end Mask

open Computability.BorderVNP.Crossing DescentKernelHistory DescentBundleHistory DescentTerminalGraphPositions
open ThreeFlat.Routing

section Homed
variable {P U : Type} [Fintype P] {d S p q t H N A blocks shops groups bw : ℕ} {bits:P→ℕ}
    (G:Network d P bits) (hp:0<p) (L:Order G S p)
    (r:∀v:G.Site,BitRecipe U (Boundary G v) (boundaryWidth G v))
    (s:∀v,Shape p (r v)) (code:U×List (List SliceCode)→Fin t)
variable (birth : ∀ v : G.Site, ((s v).recipe hp).restricted.Node ↪ ℕ)
local notation "rs" => DescentTerminalBundleRows.recipes L
  (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code

theorem homed_width (i : Fin S) (v : Fin (L.site i).nodes) (u : (rs i v).Hidden) : (rs i v).width u=p := rfl

variable (out maskBase : ℕ) (m:Memory bw) (channels:MaskAllocation.Channels blocks)
    (room:out+blocks*shops<2^bw) (fit:groups*span q t H N A p≤bw)
    (b:Fin blocks) (placed:(channels.primitive b 4).base=out+b.val*shops)
    (capacity:shops≤(channels.primitive b 4).size)
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "done" => final out blocks shops H groups p m
local notation "meas" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)

include room fit placed capacity in
/-- Field four of the physical masked channels gives `PrimitiveReceipts.width` at
the actual numbered site, with its chronological injection on the restricted private words. -/
theorem primitive_width (h:Fin shops) (g:Fin groups) (i:Fin S) (v:Fin (L.site i).nodes)
    (hidden:(rs i v).Hidden↪ℕ) (used:Fintype.card (rs i v).Hidden≤H) :
    (program bw out blocks shops H groups p).Exec m done (4+(blocks*shops)*6) ∧
    CheapCode (program bw out blocks shops H groups p) ∧
    (∀u:(rs i v).Hidden,
      venueField (cellAt (meas machine done h) (finProdFinEquiv (g,b)))
        (hiddenWidth ((ordinal hidden u).castLE used))=(rs i v).width u) ∧
    ∀a,a<out ∨ out+blocks*shops≤a→done a=m a := by
  have run:=issued out blocks shops H groups p m room
  refine ⟨run.1,run.2.1,?_,run.2.2.2⟩
  intro u
  rw [homed_width G hp L r s code birth i v u]
  apply width_read out m machine room fit b _ _ h g _
  · simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using placed
  · simpa only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at] using capacity

end Homed
end
end Hierarchy.DescentTerminalIssuedWidths

end OAI
