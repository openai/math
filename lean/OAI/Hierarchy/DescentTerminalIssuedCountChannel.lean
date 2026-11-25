import OAI.Hierarchy.DescentTerminalIssuedPrivateCount
import OAI.Hierarchy.DescentTerminalMaskAllocation

namespace OAI
/-! # Reading the installed private-count word in the actual restricted terminal scalar record -/
namespace Hierarchy.DescentTerminalIssuedPrivateCount
open DescentKernelHistory DescentSIMDLookup DescentTerminalVertexFields DescentTerminalRecipeRows
open DescentTerminalChronologicalBooks DescentTerminalPointerFrame DescentTerminalSiteShelves
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {t q hid N A p groups blocks shops wb d : ℕ}
variable (site:Site) (r:∀v:Fin site.nodes,Recipe (Fin t) (Fin (site.arity v))) (birth:Birth r)
    (hH:∀v,Fintype.card (r v).Hidden≤hid) (hN:∀v,Fintype.card (r v).Node≤N)
    (hA:∀v u,(r v).arity u≤A) (hw:∀v j,(r v).width j≤p) (short:∀v,site.arity v≤q) (v:Fin site.nodes)
    (base maskBase:ℕ) (config:Fin 3→Bank) (channels:MaskAllocation.Channels blocks) (m:Memory wb)
    (ok:Room config base d (blocks*shops) wb) (fit : groups*span q t hid N A p≤wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups)
    (placed:(channels.primitive b 2).base=base+size 3 d+b.val*shops) (capacity:shops≤(channels.primitive b 2).size)
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "done" => result base config (blocks*shops) (panel (d:=d) q hid N A groups) m
local notation "meas" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups)
local notation "wd" => Nat.clog 2 (hid+1)
include hH hw short ok fit placed capacity in
theorem channel_count (seen:Receipts (q:=q) (hid:=hid) site r birth hN hA v (observed (d:=d) config m (finProdFinEquiv (b,i)).val) g.val) :
    venueField (cellAt (meas machine done i) (finProdFinEquiv (g,b))) hiddenCount=Fintype.card (r v).UsedWord := by
  have hBits:wd≤ span q t hid N A p:=by rw [DescentTerminalVertexFields.size];omega
  have needed:wd*groups≤wb:=by simpa only [Nat.mul_comm wd groups] using (Nat.mul_le_mul_left groups hBits).trans fit
  have run:=written site r birth hH hN hA hw short v config base m ok i b g needed seen
  have hosts:shops≤blocks*shops:=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have index:i.val<2^wb:=by have:=i.isLt;have:=ok.limit;omega
  have addr:base+size 3 d+b.val*shops+i.val=base+size 3 d+(finProdFinEquiv (b,i)).val:=by
    change _=base+size 3 d+(i.val+shops*b.val);ring
  rw [venue_digit]
  change digit wd 0 ((cellAt (meas machine done i) (finProdFinEquiv (g,b))) 2).val=_
  rw [cell_digit,measured_channel]
  change digit wd 0 (digit (1*wd) g.val
    ((((machine).channel (finProdFinEquiv (b,(2:Fin 8).succ))).read done (i.val:Computability.VPVNP.BurstRAM.Word wb)).val%2^(1*wd*groups)))=_
  simp only [Nat.one_mul,MaskAllocation.shelf,MaskAllocation.Channels.primitive_at]
  rw [digit_clip,Bank.read,Fin.val_cast_of_lt index]
  rw [Nat.mod_eq_of_lt (i.isLt.trans_le capacity),placed,addr,run.2.2]
  have small: Fintype.card (r v).UsedWord<2^wd:=(Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans (hH v))).trans_le
    (Nat.le_pow_clog (by decide) (hid+1))
  simp [digit,Nat.mod_eq_of_lt small]

open Computability.BorderVNP.Crossing DescentTerminalGraphPositions
open ThreeFlat.Routing
theorem restricted_count {P U:Type} [Fintype P] {D S p t:ℕ} {bw:P→ℕ} (G:Network D P bw) (L:Order G S p) (hp:0<p)
    (rs:∀v:G.Site,Recipe U (DescentTerminalBoundaryBasis.SiteRef (p:=p) G v))
    (order:∀v,(rs v).restricted.Node↪ℕ) (code:U→Fin t) (i:Fin S) (v:Fin (L.site i).nodes) :
    let s:=DescentTerminalBundleRows.recipes L (fun v=>(rs v).restricted) hp order code i v
    Fintype.card s.UsedWord=Fintype.card s.Hidden :=
  (DescentTerminalBundleRows.numbered_words G hp _ _ _ code).trans (restricted_words (rs (L.node i v)))

/-- A single installed dictionary (including shift tables) is shared by every home and block. -/
theorem advice {d h:ℕ} (fits:3*d+2≤h/2) : size 3 d≤2^(h/2) := by
  have one : 2^d≤2^(d*3):=Nat.pow_le_pow_right (by decide) (by omega)
  have four : 4*2^(d*3)=2^(d*3+2):=by rw [pow_add];ring
  calc
    size 3 d≤4*2^(d*3):=by unfold DescentTerminalPointerFrame.size;omega
    _=2^(d*3+2):=four
    _≤_:=Nat.pow_le_pow_right (by decide) (by omega)

end
end Hierarchy.DescentTerminalIssuedPrivateCount

end OAI
