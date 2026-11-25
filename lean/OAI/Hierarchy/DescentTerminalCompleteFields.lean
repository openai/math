import OAI.Hierarchy.DescentTerminalCountWidthPair
import OAI.Hierarchy.DescentTerminalPrimitiveFrames

namespace OAI
/-! # Reading a complete numbered scalar record after the last private-count and width scans -/
namespace Hierarchy.DescentTerminalCountWidthPair
open DescentTerminalVertexFields DescentTerminalChronologicalBooks DescentKernelHistory
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalIssuedPrivateCount
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
section Physical
open Computability.BorderVNP.Crossing DescentBundleHistory DescentTerminalGraphPositions
open ThreeFlat.Routing
variable {P U : Type} [Fintype P] {D S p q t hid N A blocks shops groups wb d : ℕ} {bits:P→ℕ}
    (G:Network D P bits) (hp:0<p) (L:Order G S p)
    (r:∀v:G.Site,BitRecipe U (Boundary G v) (boundaryWidth G v))
    (s:∀v,Shape p (r v)) (code:U×List (List SliceCode)→Fin t)
variable (birth : ∀ v : G.Site, ((s v).recipe hp).restricted.Node ↪ ℕ) (host : Fin S)
local notation "rs" => DescentTerminalBundleRows.recipes L
  (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host
local notation "site" => L.site host
variable (names : Birth (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host))
    (hH : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).Hidden ≤ hid)
    (hN : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).Node ≤ N)
    (hA : ∀ z u, (DescentTerminalBundleRows.recipes L
      (fun v => Recipe.restricted (Shape.recipe (hp := hp) (s v))) hp birth code host z).arity u ≤ A)
    (short : ∀ z, (L.site host).arity z ≤ q) (z : Fin (L.site host).nodes)
    (source:Fin 3→Bank) (base out maskBase:ℕ) (channels:MaskAllocation.Channels blocks) (m:Memory wb)
local notation "nRows" => blocks*shops
local notation "price" => DescentTerminalPointerFrame.size 3 d
local notation "warm" => counted d q hid N A groups blocks shops base source m
local notation "done" => final d q hid N A groups blocks shops p base out source m
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "meas" => measured (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p) (groups:=groups) machine
variable (ok : DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (apart : base + DescentTerminalPointerFrame.size 3 d + blocks*shops ≤ out)
    (room : out + blocks*shops < 2^wb) (fit:groups*span q t hid N A p≤wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups)
    (fromBase:∀f,(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).base=(source f).base+b.val*shops)
    (fromSize:∀f,shops≤(channels.primitive b (DescentTerminalPrivateSourceChannels.family f)).size)
    (covers : ∀ f : Fin 3, familySize (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (w:=p)
      (DescentTerminalPrivateSourceChannels.family f) * groups ≤ d)
    (countBase:(channels.primitive b 2).base=base+DescentTerminalPointerFrame.size 3 d+b.val*shops)
    (countSize:shops≤(channels.primitive b 2).size)
    (widthBase:(channels.primitive b 4).base=out+b.val*shops)
    (widthSize:shops≤(channels.primitive b 4).size)
local notation "position" => finProdFinEquiv (g,b)
local notation "node" => fun u=>(ordinal (names.atom z) u).castLE (hN z)
local notation "rowAt" => fun mem k=>venueField (cellAt (meas mem i) position) k

attribute [local irreducible] DescentTerminalBundleRows.recipes program final measured MaskAllocation.shelf
attribute [local irreducible] cellAt venueField blankAt

set_option maxHeartbeats 350000 in
include short ok apart room fit fromBase fromSize covers countBase countSize widthBase widthSize in
theorem primitive_receipts
    (ports:rowAt m publicArity= (site).arity z)
    (occupied:(blankAt (meas m i) position).val=1) (alias_:channels.primitive b 1=channels.occupied b)
    (population:rowAt m nodeCount=Fintype.card (rs z).Node)
    (roles:∀u,rowAt m (nodeRole (node u))=((rs z).tag u).val+1)
    (lengths:∀u,rowAt m (nodeArity (node u))=(rs z).arity u)
    (refs:∀u (j:Fin ((rs z).arity u)),rowAt m (nodeArg (node u) (j.castLE (hA z u)))=
      ((rs z).operand u j).elim (fun x=>x.val+1) (fun x=>q+(ordinal (names.hidden z) x).val+1))
    (early:∀f:Fin 8,f≠2→f≠4→(channels.primitive b f).base+(channels.primitive b f).size≤base) :
    (program wb d q hid N A groups blocks shops p base out source).Exec m done (clocks d blocks shops) ∧
    CheapCode (program wb d q hid N A groups blocks shops p base out source) ∧
    PrimitiveReceipts (q:=q) site rs names hH hN hA z (rowAt done) ∧
    ∀j,j<base ∨ out+nRows≤j→done j=m j := by
  have h:=issued (q:=q) (t:=t) (hid:=hid) (N:=N) (A:=A)
    (blocks:=blocks) (shops:=shops) (groups:=groups) (wb:=wb) (d:=d) G hp L r s code birth host names hH hN hA short z source base out maskBase channels m
    ok apart room fit b i g fromBase fromSize covers countBase countSize widthBase widthSize population lengths refs
  have live:=DescentTerminalPrimitiveFrames.live_at (groups:=groups) (blocks:=blocks) (shops:=shops) (q:=q) (t:=t) (H:=hid) (N:=N) (A:=A) (p:=p)
    channels maskBase m b i g alias_
  have prev (k:Key hid N A) (two:group k≠2) (four:group k≠4) : rowAt done k=rowAt m k :=
    h.2.2.2.2.1 k (early (group k) two four)
  refine ⟨h.1,h.2.1,?_,h.2.2.2.2.2.2⟩
  exact {
    ports := (prev publicArity (by decide : (0 : Fin 8) ≠ 2) (by decide : (0 : Fin 8) ≠ 4)).trans ports
    live := (prev (.inr (.inl ())) (by decide : (1 : Fin 8) ≠ 2) (by decide : (1 : Fin 8) ≠ 4)).trans (live.trans occupied)
    hidden := h.2.2.1
    nodes := (prev nodeCount (by decide : (3 : Fin 8) ≠ 2) (by decide : (3 : Fin 8) ≠ 4)).trans population
    width := h.2.2.2.1
    role := fun u=>(prev (nodeRole (node u)) (by decide : (5 : Fin 8) ≠ 2) (by decide : (5 : Fin 8) ≠ 4)).trans (roles u)
    arity := fun u=>(prev (nodeArity (node u)) (by decide : (6 : Fin 8) ≠ 2) (by decide : (6 : Fin 8) ≠ 4)).trans (lengths u)
    operand := fun u j=>(prev (nodeArg (node u) (j.castLE (hA z u))) (by decide : (7 : Fin 8) ≠ 2) (by decide : (7 : Fin 8) ≠ 4)).trans (refs u j) }

end Physical
end
end Hierarchy.DescentTerminalCountWidthPair

end OAI
