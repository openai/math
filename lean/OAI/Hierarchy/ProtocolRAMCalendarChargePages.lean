import OAI.Hierarchy.ProtocolRAMSelectorChargeTable
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame

namespace OAI
/-! # Original charge words for the two authentic packet catalogues -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripDirectory DiscrepancyROM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical


namespace StripChart
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z d k q depth) (t : TreeCosts)

def charges (base : ℕ) : MenuROM.Charges :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,s.positive⟩⟩
  letI : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) ⟨0,s.positive⟩⟩
  let a:=payloadMenu F N k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    t.payload t.payload_nonneg s.minimum
  let b:=purchasedMenu F depth k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    t.purchase t.purchase_nonneg s.minimum
  let left:=MenuROM.selectorCharges a base
  ⟨left,MenuROM.selectorCharges b left.stop⟩

def withCharges (base : ℕ) : Boards z d k q depth :=
  let h:=charges F s t base
  { s with
    outer := fun p a => { s.outer p a with cash := h.payload.bank 0 }
    inner := fun p a j b => { s.inner p a j b with cash := h.purchase.bank 0 } }

def outerReserve {phases U V steps : ℕ} (H : EconomicHeader phases U V steps) : Bank :=
  ⟨(charges F s t H.stop).stop,ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint z N k)⟩

def chargedSlab {phases U V steps : ℕ} (H : EconomicHeader phases U V steps) (extra : ℕ) : Slab :=
  let b:=outerReserve F s t H
  -- The physical score banks use padded native indices even on their final
  -- public page. Keep their complete read footprints before private rows.
  ⟨b.base+b.size+2^(GlobalTests.bits z N k),extra⟩

def reserveWords {w : ℕ} (b : Bank) (rest : Memory w) : Memory w :=
  ThreeFlat.RAM.fillSegment b.base b.size (fun _=>0) rest

theorem reserveWords_read {w : ℕ} (b : Bank) (m : Memory w) (u : Word w) : b.read (reserveWords b m) u=0 := by
  have range : b.base≤b.base+u.val%b.size ∧ b.base+u.val%b.size<b.base+b.size :=
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _⟩
  exact ite_eq_left range

theorem chargedSlab_size {phases U V steps : ℕ} (H : EconomicHeader phases U V steps) (extra : ℕ) :
    (chargedSlab F s t H extra).headerEnd≤(charges F s t H.stop).stop+
      2*(PurchaseInventory.footprint z N k+1)+2^z*2^(GlobalTests.kinds N k) := by
  have pad:=ProtocolRAMPurchaseSampler.span_le (PurchaseInventory.footprint z N k)
  change (charges F s t H.stop).stop+_+2^(z+GlobalTests.kinds N k)≤_
  rw [Nat.pow_add]
  exact Nat.add_le_add_right (Nat.add_le_add_left pad _) _

theorem charge_size (base : ℕ) :
    (charges F s t base).stop=base+(charges F s t base).payload.size+(charges F s t base).purchase.size := by
  have layout (p : MenuROM.Charges) (first : p.payload.base=base)
      (second : p.purchase.base=p.payload.stop) : p.stop=base+p.payload.size+p.purchase.size := by
    change p.purchase.base+1*p.purchase.size=_
    rw [second,Table.stop,first,one_mul,one_mul]
  exact layout (charges F s t base) rfl rfl

namespace EconomicHeader
variable {phases U V steps jobs w : ℕ}

theorem vector_above (H : EconomicHeader phases U V steps) (order : H.Ordered) (rest : Memory w)
    (x : ℕ) (later : H.stop≤x) : H.vectorMemory rest x=rest x := by
  have bought : H.boughtTree.stop≤x:=later
  have tree : H.payloadTree.stop≤x:=order.boughtTreeBase.le.trans ((Nat.le_add_right ..).trans bought)
  have low : H.payloadTree.base≤x:=(Nat.le_add_right ..).trans tree
  rw [H.tree_origin order rest x low]
  exact (H.boughtTree.frame _ x (.inr bought)).trans (H.payloadTree.frame _ x (.inr tree))

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
theorem original_tail (H : EconomicHeader phases U V steps) (ord : H.Ordered) (b : JointHeader.Board)
    (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z d)
    (markets : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout markets size)
    (hd : 1≤d) (first : 2^z≤b.initial) (score : JointHeader.stop b z N k phases≤H.ports.base)
    (heap : heapEnd z d copies≤H.ports.base) (x : ℕ) (lo : H.stop≤x)
    (before : ∀i,x<Boot.low (markets i)) (length : x<size)
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x) :
    let high:=H.scalar.words (H.vectorMemory rest)
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    Boot.booted markets size mixed x=rest x := by
  intro high mixed
  have s₀ : H.scalar.stop≤H.stop := by
    have c:=Ordered.menu_bounds H ord
    obtain ⟨_,f,g,h,_,i,j⟩:=ord
    have a : H.payload.base≤H.payload.stop:=Nat.le_add_right ..
    have b : H.bought.base≤H.bought.stop:=Nat.le_add_right ..
    have d : H.payloadTree.base≤H.payloadTree.stop:=Nat.le_add_right ..
    have e : H.boughtTree.base≤H.stop:=Nat.le_add_right ..
    omega
  have scal : H.scalar.stop≤x:=s₀.trans lo
  have port : H.ports.stop≤x:=ord.scalarBase.le.trans ((Nat.le_add_right ..).trans scal)
  have base : H.ports.base≤x:=(Nat.le_add_right ..).trans port
  have started:=(Boot.start markets layout hd π mixed (JointHeader.authentic («N» := N) (k:=k) b phase π stock _ first)).2
  have keep:=started.kept x (heap.trans base) (fun i reach=>Nat.not_lt_of_ge reach.1 ((before i)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left length] at keep
  exact keep.trans ((JointHeader.tail_words b phase π stock _ x first (score.trans base)).trans
    ((H.ports.frame _ x (.inr port)).trans ((above high x ((Nat.le_add_right ..).trans scal)).trans
    ((H.scalar.frame _ x (.inr scal)).trans (H.vector_above ord _ x lo)))))

omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
/-- Extend the same economic/permutation tape with two small static pages
without changing any price, tree, route, or private counter field. -/
theorem charged_origin (H : EconomicHeader phases U V steps) (ord : H.Ordered) (p : MenuROM.Charges)
    (placed : p.payload.base=H.stop) (next : p.purchase.base=p.payload.stop)
    (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ)
    (rest : Boot.Tape z d) (markets : Fin jobs→Market z d k) {size : ℕ}
    (layout : Boot.Layout markets size) (hd : 1≤d) (first : 2^z≤b.initial)
    (score : JointHeader.stop b z N k phases≤H.ports.base) (heap : heapEnd z d copies≤H.ports.base)
    (fits : p.payload.entries≤2^(wordBits z d copies) ∧ p.purchase.entries≤2^(wordBits z d copies))
    (before : ∀i,p.stop≤Boot.low (markets i)) (length : p.stop≤ size)
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x) :
    let high:=H.scalar.words (H.vectorMemory (p.words rest))
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    p.Resident (Boot.booted markets size mixed) := by
  intro high mixed
  have a:=resident_both p.payload p.purchase rest next.ge fits.1 fits.2
  have actual (x : ℕ) (lo : H.stop≤x) (hi : x<p.stop) : Boot.booted markets size mixed x=p.words rest x :=
    H.original_tail ord b phase π stock _ markets layout hd first score heap x lo
      (fun i=>hi.trans_le (before i)) (hi.trans_le length) low above
  have bridge : p.payload.stop≤p.stop:=next.ge.trans (Nat.le_add_right ..)
  exact ⟨a.1.frame (fun x lo hi=>actual x (placed.ge.trans lo) (hi.trans_le bridge)),
    a.2.frame (fun x lo hi=>actual x (placed.ge.trans ((Nat.le_add_right ..).trans (next.ge.trans lo))) hi)⟩
omit [SiteNaming (ColumnSite (PayloadStrip.Columns (permutationFabric z d).shapes.length) k)] in
/-- The complete padded zero reserve bank from the original header is
observed after the same compiled boot, even on malformed private selectors. -/
theorem reserve_origin (H : EconomicHeader phases U V steps) (ord : H.Ordered) (p : MenuROM.Charges)
    (placed : p.payload.base=H.stop) (next : p.purchase.base=p.payload.stop)
    (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ)
    (empty : Bank) (atEnd : empty.base=p.stop) (rest : Boot.Tape z d) (markets : Fin jobs→Market z d k)
    {size : ℕ} (layout : Boot.Layout markets size) (hd : 1≤d) (first : 2^z≤b.initial)
    (score : JointHeader.stop b z N k phases≤H.ports.base) (heap : heapEnd z d copies≤H.ports.base)
    (before : ∀i,empty.base+empty.size≤Boot.low (markets i)) (length : empty.base+empty.size≤ size)
    (low : Boot.Tape z d→Boot.Tape z d) (above : ∀m x,H.scalar.base≤x→low m x=m x)
    (u : Word (wordBits z d copies)) :
    let high:=H.scalar.words (H.vectorMemory (p.words (reserveWords empty rest)))
    let mixed:=JointHeader.words b z d N k phase π stock (H.ports.words (low high))
    empty.read (Boot.booted markets size mixed) u=0 := by
  intro high mixed
  let x:=empty.base+u.val%empty.size
  have ex : empty.base≤x:=Nat.le_add_right ..
  have last : x<empty.base+empty.size:=Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
  have pay : p.payload.stop≤p.purchase.stop:=next.ge.trans (Nat.le_add_right ..)
  have origin : H.stop≤x:=placed.ge.trans ((Nat.le_add_right ..).trans (pay.trans (atEnd.ge.trans ex)))
  change Boot.booted markets size mixed x=0
  rw [H.original_tail ord b phase π stock _ markets layout hd first score heap x origin
    (fun i=>last.trans_le (before i)) (last.trans_le length) low above]
  exact (p.purchase.outside _ (.inr (atEnd.ge.trans ex))).trans
    ((p.payload.outside _ (.inr (pay.trans (atEnd.ge.trans ex)))).trans (reserveWords_read empty rest u))

end EconomicHeader

end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
