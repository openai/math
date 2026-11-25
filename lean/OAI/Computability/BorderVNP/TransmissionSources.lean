import OAI.Computability.BorderVNP.PackedDirectoryKeys
import OAI.Computability.BorderVNP.TransmissionPinsComplete
import OAI.Computability.BorderVNP.TransmissionPinsInput
import OAI.Computability.BorderVNP.TransmissionReadback

/-!
# Literal and substituted-index sources in the seven-word delivery table

A literal row addresses the original processor input, including the program prefix and
private description suffix. A row for the extra field addresses the independently
prepared substitution array. Its source does not read the live matrix-column pin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open BorderVNP.RoutingISA VPVNP.BurstRAM

/-- Absolute source base of a data transmission obtained from a public delivery row. -/
def Row.sourceBase (r : Row) (L : Pins.Layout) : ℕ :=
  if r.field = 0 then r.processor*L.stride + r.offset
  else L.ibase + r.processor*L.literal + r.offset

private theorem literal_address_lt (L : Pins.Layout) {p off : ℕ} (hp : p < L.processors)
    (ho : off < L.literal) : p * L.stride + off < L.processors * L.stride := by
  have h : L.literal ≤ L.stride := by unfold Pins.Layout.stride Pins.Layout.offset; omega
  exact (Nat.add_lt_add_left (ho.trans_le h) _).trans_le
    ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right L.stride hp)

/-- After pin preparation, reading a literal-row source at offset `e` still returns
the actual programmed input bit. This applies equally to code, scalar advice and private
site strings placed in the literal suffix. -/
theorem Row.literal_source {w : ℕ} (r : Row) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (guess : ℕ → Bool) (m : Memory w) (hm : P.ContainsInput m) (e : ℕ)
    (hf : r.field = 0) (hp : r.processor < L.processors) (ho : r.offset+e < L.literal)
    (hi : L.processors * L.stride ≤ L.ibase) (hh : L.processors * L.stride ≤ L.hbase) :
    Pins.preparedMemory L guess m L.count (r.sourceBase L + e) =
      TeamTapeInputEmit.headerWord w (P.literal ⟨r.processor,hp⟩) (r.offset+e) := by
  have ha := literal_address_lt L hp ho
  simp only [Row.sourceBase,hf,ite_true,Nat.add_assoc]
  rw [Pins.preparedMemory_other]
  · exact hm.literal ⟨r.processor,hp⟩ ⟨r.offset+e,ho⟩
  · intro j _; omega
  · intro j _ _; omega

/-- An extra-field delivery returns the independently guessed substitution bit on the
index team, and returns zero for each padding position and each other team. -/
theorem Row.pin_source {w : ℕ} (r : Row) (L : Pins.Layout) (guess : ℕ → Bool) (m : Memory w)
    (sep : Pins.Separated L) (e : ℕ) (hf : r.field = 1) (hp : r.processor < L.processors)
    (ho : r.offset+e < L.literal) :
    let i := r.processor * L.literal + (r.offset+e)
    Pins.preparedMemory L guess m L.count (r.sourceBase L + e) =
      if L.active i then Fin.ofNat _ (guess i).toNat else 0 := by
  have hpos : r.processor * L.literal + (r.offset+e) < L.count :=
    (Nat.add_lt_add_left ho _).trans_le ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right L.literal hp)
  simp only [Row.sourceBase,hf,Nat.one_ne_zero,ite_false,Nat.add_assoc]
  exact Pins.preparedMemory_substitute L guess m sep le_rfl hpos

/-- A bit in the ordinary literal appears in an enumerated directory row and that row's
actual addressed source word equals the original bit. -/
theorem Layout.deliver_literal_source {w : ℕ} (d : Layout) (pp lp : ℕ → ℕ × ℕ) (t : Fin d.teams)
    (p : Fin d.processors) (b : Fin d.literal) (hb : 0 < d.block) (hf : 0 < d.fields)
    (L : Pins.Layout) (P : Pins.ProcessorFields L) (hl : d.literal = L.literal)
    (hproc : d.processors = L.processors) (guess : ℕ → Bool) (m : Memory w)
    (hm : P.ContainsInput m) (hi : L.processors*L.stride ≤ L.ibase) (hh : L.processors*L.stride ≤ L.hbase) :
    let pos := p.val * d.stride + b.val
    let dst := lp (t.val * d.sites + pos/d.block)
    ∃ r ∈ d.directory pp lp, ∃ e < r.width, r.team = t.val ∧ r.cell = dst.1 ∧
      r.slot+e = dst.2+pos%d.block ∧
      Pins.preparedMemory L guess m L.count (r.sourceBase L + e) =
        TeamTapeInputEmit.headerWord w (P.literal (p.cast hproc)) b.val := by
  obtain ⟨r,hr,e,he,ht,hp,field,hoff,hcell,hslot⟩ := d.live_delivered pp lp t p ⟨0,hf⟩ hb b
  have hproc' : r.processor < L.processors := hp ▸ (hproc ▸ p.isLt)
  have ho : r.offset+e < L.literal := hoff ▸ (hl ▸ b.isLt)
  refine ⟨r,hr,e,he,ht,by simpa using hcell,by simpa using hslot,?_⟩
  rw [r.literal_source L P guess m hm e field hproc' ho hi hh,hoff]
  congr 2
  exact Fin.ext hp

end Packing.Directory

end BorderVNP
end Computability
end OAI
