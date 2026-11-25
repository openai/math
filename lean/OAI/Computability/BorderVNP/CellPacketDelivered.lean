import OAI.Computability.BorderVNP.CellPacketSources
import OAI.Computability.BorderVNP.TransmissionHistoryReadback
import OAI.Computability.BorderVNP.TransmissionSenderStable

/-! # Original-site bits in the cell initializer's physical RAM

A native local copy or checked remote transmission is the last writer of a designated
consumer slot. Protecting the literal source against earlier writes connects that
consumer to the prepared processor inputs. The transmitted strings are the actual
one-copy factor encodings, including the private length headers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Source

open VPVNP.BurstRAM
open BorderVNP.RoutingISA
open BorderVNP.RoutingISA.Transmission
open BorderVNP.Packing.Directory (Layout Row)

/-- A concrete scheduled transfer, with a protected literal source and a last writer
at the destination. A remote transfer also checks the two real relay endpoints. -/
inductive Receipt {w : ℕ} : TeamHistory w → TeamHistory w → ℕ → ℕ → Prop
  | localCopy (h : TeamHistory w) (i j dst : ℕ)
      (write : LastWrite h.rows h.team h.count i .dataHere j dst)
      (room : (h.rows i).source.val + j < 2^w)
      (protect : ∀ k ≤ i, (h.rows k).protectsCell h.team ((h.rows i).source.val+j)) :
      Receipt h h ((h.rows i).source.val+j) dst
  | relay (sender receiver : TeamHistory w) (i j dst : ℕ)
      (row : i < sender.count) (offset : j < (sender.rows i).width.val)
      (sending : (sender.rows i).selected sender.team = some (some .sendData))
      (received : LastWrite receiver.rows receiver.team receiver.count i .receiveB j dst)
      (wire : sender.before i ((sender.rows i).senderAddress sender.pub (sender.before i) j) =
        receiver.linkWord i .receiveB 9 j)
      (protect : ∀ k < i, (sender.rows k).protectsCell sender.team ((sender.rows i).source.val+j)) :
      Receipt sender receiver ((sender.rows i).source.val+j) dst

/-- The checked slot contains exactly the original source word for either delivery role. -/
theorem Receipt.read {w : ℕ} {sender receiver : TeamHistory w} {src dst : ℕ}
    (receipt : Receipt sender receiver src dst) : receiver.history.val.2.2 dst = sender.initial src := by
  cases receipt
  case localCopy =>
    rename_i i j room protect write
    rw [sender.local_data write,Fin.val_add,Fin.val_ofNat,
      Nat.mod_eq_of_lt (write.slot_lt.trans (sender.rows i).width.isLt),Nat.mod_eq_of_lt room]
    unfold bitMemory
    rw [rangeMemory_eq_of_outside]
    · apply tableMemory_protected
      exact fun k hk => protect k hk.le
    · intro d hd
      have fit := (protect i le_rfl .dataHere write.selected d hd).1
      have := write.slot_lt
      omega
    · intro d hd
      have out := (protect i le_rfl .dataHere write.selected d hd).2
      have := write.slot_lt
      omega
  case relay =>
    rename_i i j row offset sending protect wire received
    rw [sender.remote_data receiver row offset sending received wire]
    exact tableMemory_protected sender.rows sender.team sender.pub sender.initial sender.bits i _ protect

/-- Readback of every original site from the actual team histories. The directory uses
the common padded description width. Each original bit has its own physical source
row and arrives at the slot of its cell, including when a site straddles two tails. -/
theorem delivered_strings {w : ℕ} (hw : 0 < w) (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (literalHead : ℕ → ℕ → ℕ → Bool) (strings : Fin d.entries → Fin d.description → Bool)
    (hp : 0 < d.processors) (ht : 0 < d.literal/2) (short : d.description ≤ d.literal/2)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (L : ℕ → Pins.Layout) (P : ∀ t, Pins.ProcessorFields (L t))
    (hlit : ∀ t, d.literal = (L t).literal) (hproc : ∀ t, d.processors = (L t).processors)
    (guess : ℕ → ℕ → Bool) (mem : ℕ → Memory w) (loaded : ∀ t, (P t).ContainsInput (mem t))
    (scratchI : ∀ t, (L t).processors*(L t).stride ≤ (L t).ibase)
    (scratchH : ∀ t, (L t).processors*(L t).stride ≤ (L t).hbase)
    (literals : ∀ t p, (P t).literal p = List.ofFn (fun i : Fin d.literal =>
      d.literalBit literalHead strings t p.val i.val))
    (history : ℕ → TeamHistory w) (owner cellBase : ℕ → ℕ)
    (initial : ∀ t, (history t).initial = Pins.preparedMemory (L t) (guess t) (mem t) (L t).count)
    (routes : ∀ r ∈ d.directory pp lp, r.team < d.teams → ∀ e < r.width,
      Receipt (history r.team) (history (owner r.cell)) (r.sourceBase (L r.team)+e)
        (cellBase r.cell+r.slot+e)) (j : Fin d.entries) :
    ∀ b : Fin d.description, readings (history (owner (pp j).1)).history.val.2.2
      (cellBase (pp j).1 + (pp j).2 + b.val) = (strings j b).toNat := by
  intro b
  obtain ⟨r,hr,e,he,team,cell,slot,source⟩ := d.private_source_word pp lp literalHead
    strings j b hp ht short fits L P hlit hproc guess mem loaded
    scratchI scratchH literals
  have route := (routes r hr team e he).read
  have right := congrFun (initial r.team) (r.sourceBase (L r.team)+e)
  have eqWord := route.trans (right.trans source)
  rw [cell,Nat.add_assoc,slot,← Nat.add_assoc] at eqWord
  have cap : 1 < 2^w := Nat.one_lt_pow hw.ne' (by decide)
  change ((history _).history.val.2.2 _).val = _
  rw [eqWord,Fin.val_ofNat,Nat.mod_eq_of_lt]
  cases strings j b <;> simp_all

/-- Original factor bytes in the physically received single-box reservation. -/
theorem delivered_sites {w : ℕ} (hw : 0 < w) (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (literalHead : ℕ → ℕ → ℕ → Bool) (width : ℕ) (fs : Fin d.entries → List Factor)
    (hp : 0 < d.processors) (ht : 0 < d.literal/2) (short : d.description ≤ d.literal/2)
    (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (L : ℕ → Pins.Layout) (P : ∀ t, Pins.ProcessorFields (L t))
    (hlit : ∀ t, d.literal = (L t).literal) (hproc : ∀ t, d.processors = (L t).processors)
    (guess : ℕ → ℕ → Bool) (mem : ℕ → Memory w) (loaded : ∀ t, (P t).ContainsInput (mem t))
    (scratchI : ∀ t, (L t).processors*(L t).stride ≤ (L t).ibase)
    (scratchH : ∀ t, (L t).processors*(L t).stride ≤ (L t).hbase)
    (literals : ∀ t p, (P t).literal p = List.ofFn (fun i : Fin d.literal =>
      d.literalBit literalHead (fun j => siteString width (fs j)) t p.val i.val))
    (history : ℕ → TeamHistory w) (owner cellBase : ℕ → ℕ)
    (initial : ∀ t, (history t).initial = Pins.preparedMemory (L t) (guess t) (mem t) (L t).count)
    (routes : ∀ r ∈ d.directory pp lp, r.team < d.teams → ∀ e < r.width,
      Receipt (history r.team) (history (owner r.cell)) (r.sourceBase (L r.team)+e)
        (cellBase r.cell+r.slot+e)) (j : Fin d.entries) :
    Delivered (description := d.description) (readings (history (owner (pp j).1)).history.val.2.2)
      (cellBase (pp j).1 + (pp j).2) width (fs j) := by
  intro b _
  exact delivered_strings hw d pp lp literalHead (fun j => siteString width (fs j)) hp ht short fits
    L P hlit hproc guess mem loaded scratchI scratchH literals history owner cellBase initial routes j b

end CellSparse.Packet.Source

end BorderVNP
end Computability
end OAI
