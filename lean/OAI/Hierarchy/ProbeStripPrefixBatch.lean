import OAI.Hierarchy.ProtocolRAMBatchInputEnd
import OAI.Hierarchy.ProbeStripInputEnd
import OAI.Hierarchy.ProtocolRAMPortPadding

namespace OAI
/-! # Input spans of the genuine strip quotation, occurrence and padded port expressions -/
noncomputable section
namespace Hierarchy.ProtocolRAM
variable {cut : ℕ}

namespace PortPadding
theorem before_extend {n D : ℕ} (xs : Fin n → Expr) (dead : Expr)
    (hx : ∀ i, (xs i).inputEnd≤cut) (hd : dead.inputEnd≤cut) (i : Fin D) :
    (extend xs dead i).inputEnd≤cut := by
  unfold extend
  split
  · exact hx _
  · exact hd

theorem before_batch {q n : ℕ} (D : ℕ) {b : Batch q n} (h : b.Before cut) : (batch D b).Before cut :=
  ⟨h.menu,h.termCount,h.enabled,h.owner,h.field,
    before_extend b.stock _ h.stock (Nat.zero_le _),
    before_extend b.perCopy _ h.perCopy (Nat.zero_le _),h.quotes⟩
end PortPadding

namespace StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage PurchaseFrozen
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N q goods digits : ℕ}

omit [Nonempty E] [Fintype A] in
theorem Channels.Before.slot_before {c : Channels A E} (fit : c.Before cut)
    (i : Fin (Fintype.card E)) (e : Expr) (atSlot : c.slot i=some e) : e.inputEnd≤cut := by
  unfold Channels.slot at atSlot
  cases ha : c.account ((Fintype.equivFin E).symm i) with
  | none => simp [ha] at atSlot
  | some a =>
    have same : c.address a=e := by simpa [ha] using atSlot
    exact same ▸ fit.address a

omit [Fintype E] [Nonempty E] in
theorem Channels.Before.digit_before {c : Channels A E} (fit : c.Before cut) (i : Fin (Fintype.card A)) :
    (c.digit i).inputEnd≤cut := fit.address _

theorem quoted_before (price offsets stocks : Bank) (addr : Fin digits → Expr)
    (priceEnd : price.base+price.size≤cut) (offsetsEnd : offsets.base+offsets.size≤cut)
    (stocksEnd : stocks.base+stocks.size≤cut) (addrEnd : ∀j,(addr j).inputEnd≤cut) (j : Fin digits) :
    (quoted price offsets stocks addr j).inputEnd≤cut :=
  InputEnd.atRow _ _ (max_le priceEnd (max_le (max_le offsetsEnd (Nat.zero_le _))
    (max_le stocksEnd (Nat.zero_le _)))) (addrEnd j)

theorem entry_before (m : Probe.FixedMenu F edge req box ε tree N) (packet : Expr) (menu : m.index → ℕ)
    (hp : packet.inputEnd≤cut) : (entry m packet menu).inputEnd≤cut :=
  InputEnd.choose _ _ _ _ (fun _ => Nat.zero_le _) hp

theorem batch_before (m : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms menu enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods → E) (slot : Fin goods → Option Expr)
    (termsEnd : terms.base+terms.size≤cut) (menuEnd : menu.base+menu.size≤cut)
    (enabledEnd : enabled.base+enabled.size≤cut) (selectorsEnd : selectors.base+selectors.size≤cut)
    (stocksEnd : stocks.base+stocks.size≤cut) (ownerEnd : owner.inputEnd≤cut)
    (quotesEnd : ∀j,(test.quoted j).inputEnd≤cut)
    (slotsEnd : ∀i e,slot i=some e→e.inputEnd≤cut) :
    (batch (q:=q) m test terms menu enabled selectors stocks owner copies maxWidth ports slot).Before cut := by
  have quotes : ∀e∈List.ofFn test.quoted,e.inputEnd≤cut := by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact quotesEnd j
  have hp : (menuLookup menu test.radix (List.ofFn test.quoted)).inputEnd≤cut :=
    max_le menuEnd (InputEnd.menuKey _ _ quotes)
  refine ⟨menuEnd,termsEnd,enabledEnd,ownerEnd,?_,?_,?_,quotes⟩
  · intro j
    exact max_le selectorsEnd (max_le (InputEnd.scale q .row (Nat.zero_le _)) (Nat.zero_le _))
  · intro i
    change (inventory stocks _ (slot i)).inputEnd≤cut
    cases hs : slot i with
    | some e => exact max_le stocksEnd (slotsEnd i e hs)
    | none => exact InputEnd.boundedMul _ _ _ (Nat.zero_le _) (entry_before m _ _ hp)
  · intro i
    exact entry_before m (menuLookup menu test.radix (List.ofFn test.quoted))
      (fun index => useBits m index (ports i)) hp

theorem wires_before (m : Probe.FixedMenu F edge req box ε tree N) (b : Batch q goods)
    (ports : Fin goods → E) (fit : b.Before cut) (e : Fin goods) (j : Fin q) :
    (wires m b ports e j).inputEnd≤cut := entry_before m _ _ fit.packet

theorem destination_before (h : Calendar.StockCommit.PortHeader) (global : ℕ)
    (slot : Fin h.ports → Option Expr)
    (ball : h.ball.base+h.ball.size≤cut) (field : h.field.base+h.field.size≤cut)
    (slotsEnd : ∀i e,slot i=some e→e.inputEnd≤cut) : (destination h global slot).inputEnd≤cut := by
  apply InputEnd.choose _ _ _ _ _ (max_le field (Nat.zero_le _))
  intro i
  apply InputEnd.atRow _ _ _ (max_le ball (Nat.zero_le _))
  cases hs : slot i with
  | none => exact Nat.zero_le _
  | some e => exact slotsEnd i e hs

end StripDirectory
end Hierarchy.ProtocolRAM
end

end OAI
