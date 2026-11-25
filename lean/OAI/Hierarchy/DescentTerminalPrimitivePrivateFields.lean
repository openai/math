import OAI.Hierarchy.DescentTerminalPrimitiveAny
import OAI.Hierarchy.DescentTerminalCountWidthPair

namespace OAI
/-! The private count and widths at the actual primitive output are determined by its three live operand banks. -/
namespace Hierarchy.DescentTerminalPrimitiveArena.Shape
open DescentKernelHistory DescentBundleHistory DescentTerminalGraphPositions DescentTerminalChronologicalBooks
open DescentTerminalSiteShelves DescentTerminalVertexFields DescentTerminalLeafDigits DescentTerminalRecipeRows
open DescentTerminalCombinedRole DescentTerminalPointerDigits DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
open ThreeFlat.RAM PhysicalProcedure
variable (s:DescentTerminalPrimitiveArena.Shape) (start pop:ℕ) (actor:Fin s.blocks→Bank) (first second:DescentTerminalCombinedRole.Shelf)
    (chart:Fin s.columns→Fin s.blocks→Gather.Address) {bits0 bits7:ℕ}
    (f0:(Fin s.columns→Cell s.pointerBits)→Cell bits0) (f7:(Fin s.columns→Cell s.pointerBits)→Cell bits7)
    {D S p q t H N A M w:ℕ} {P U:Type} [Fintype P] {bits:P→ℕ}
    (G:Network D P bits) (hp:0<p) (L:Order G S p)
    (r:∀v:G.Site,BitRecipe U (Boundary G v) (boundaryWidth G v))
    (sh:∀v,DescentBundleHistory.Shape p (r v)) (code:U×List (List SliceCode)→Fin t)
variable (birth : ∀ v : G.Site, ((sh v).recipe hp).restricted.Node ↪ ℕ) (home : Fin S)
local notation "recipes" => DescentTerminalBundleRows.recipes L (fun v => Recipe.restricted (DescentBundleHistory.Shape.recipe (hp := hp) (sh v))) hp birth code home
variable (names : Birth (DescentTerminalBundleRows.recipes L (fun v => Recipe.restricted (DescentBundleHistory.Shape.recipe (hp := hp) (sh v))) hp birth code home))
    (hH : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L (fun v => Recipe.restricted (DescentBundleHistory.Shape.recipe (hp := hp) (sh v))) hp birth code home z).Hidden ≤ H)
    (hN : ∀ z, Fintype.card (DescentTerminalBundleRows.recipes L (fun v => Recipe.restricted (DescentBundleHistory.Shape.recipe (hp := hp) (sh v))) hp birth code home z).Node ≤ N)
    (hA : ∀ z u, (DescentTerminalBundleRows.recipes L (fun v => Recipe.restricted (DescentBundleHistory.Shape.recipe (hp := hp) (sh v))) hp birth code home z).arity u ≤ A)
    (short : ∀ z, (L.site home).arity z ≤ q) (z : Fin (L.site home).nodes)
    (maskBase:ℕ) (m:Memory w) (b:Fin s.blocks) (i:Fin s.shops) (g:Fin M)
local notation "ch" => s.channels start pop actor
local notation "image_" => s.primitiveImage start pop first second chart f0 f7 q H N A M p m
local notation "gathered" => ProtocolRAM.result (Gather.dropOff (s.gather start) s.blocks s.shops s.columns chart)
  (memory first second start s.rows m)
local notation "sources" => Gather.banks (L:=s.columns) (s.gather start) s.rows
local notation "public_" => DescentTerminalPointerFrame.result (s.rom start) sources s.rows f0 gathered
local notation "refs_" => DescentTerminalPointerFrame.result (s.public start+s.rows) sources s.rows f7 public_
local notation "size_" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p)
local notation "family" => DescentTerminalPrivateSourceChannels.family
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=M) ch maskBase
local notation "rowAt" => fun mem k => venueField (cellAt (measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A)
    (w:=p) (groups:=M) machine mem i) (finProdFinEquiv (g,b))) k
local notation "node" => fun u => (ordinal (names.atom z) u).castLE (hN z)
local notation "hd" => fun u => (ordinal (names.hidden z) u).castLE (hH z)

/-- The counting pass has three literal input dictionaries of this width in its own allocation. -/
theorem count_word_fits (room:s.finish start<2^w) : s.countBits≤w:=by
  have shelf : 2^s.countBits ≤ DescentTerminalPrimitiveArena.fee 3 s.countBits :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 3)).trans (Nat.le_add_right ..)
  rw [s.exact_end] at room
  exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    ((shelf.trans (Nat.le_add_left ..)).trans_lt room)).le

attribute [local irreducible] DescentTerminalBundleRows.recipes

include short in
theorem private_fields (kit:s.Realized (wb:=w) start pop actor) (fit:M*span q t H N A p≤w)
    (covers:∀f,size_ (family f)*M≤ s.countBits)
    (population:rowAt image_ nodeCount=Fintype.card (recipes z).Node)
    (arity:∀u,rowAt image_ (nodeArity (node u))=(recipes z).arity u)
    (args:∀u (j:Fin ((recipes z).arity u)),rowAt image_ (nodeArg (node u) (j.castLE (hA z u)))=
      ((recipes z).operand u j).elim (fun x=>x.val+1) (fun x=>q+(ordinal (names.hidden z) x).val+1)) :
    rowAt image_ hiddenCount=Fintype.card (recipes z).Hidden ∧
    ∀u,rowAt image_ (hiddenWidth (hd u))=(recipes z).width u:=by
  have frame:=DescentTerminalCountWidthPair.run (q:=q) (hid:=H) (N:=N) (A:=A) (p:=p) (groups:=M)
    (blocks:=s.blocks) (shops:=s.shops) (s.sources start pop) (s.counting start) (s.widths start)
    refs_ kit.source_room kit.count_later kit.width_limit
  have held (k:Key H N A) (two:group k≠2) (four:group k≠4):rowAt refs_ k=rowAt image_ k:=by
    symm
    apply DescentTerminalCountWidthPair.venue_same machine refs_ image_ b i g k
    simp only [MaskAllocation.shelf,MaskAllocation.Channels.primitive_at]
    exact DescentTerminalCountWidthPair.bank_before refs_ image_ (s.counting start)
      (fun a low=>frame.2.2 a (.inl low)) _ (kit.count_prior b _ two four) _
  have receipt:=DescentTerminalCountWidthPair.issued G hp L r sh code birth home names hH hN hA short z
    (s.sources start pop) (s.counting start) (s.widths start) maskBase ch refs_
    kit.source_room kit.count_later kit.width_limit fit b i g (kit.from_base b)
    (fun f=>kit.keep_family b (family f)) covers rfl (kit.keep_family b 2) rfl (kit.keep_family b 4)
    ((held nodeCount (by decide : (3 : Fin 8) ≠ 2) (by decide : (3 : Fin 8) ≠ 4)).trans population)
    (fun u=>(held (nodeArity (node u)) (by decide : (6 : Fin 8) ≠ 2) (by decide : (6 : Fin 8) ≠ 4)).trans (arity u))
    (fun u j=>(held (nodeArg (node u) (j.castLE (hA z u))) (by decide : (7 : Fin 8) ≠ 2) (by decide : (7 : Fin 8) ≠ 4)).trans (args u j))
  exact ⟨receipt.2.2.1,receipt.2.2.2.1⟩

end
end Hierarchy.DescentTerminalPrimitiveArena.Shape

end OAI
