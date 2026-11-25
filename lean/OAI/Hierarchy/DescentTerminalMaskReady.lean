import OAI.Hierarchy.DescentTerminalMaskAllocation
import OAI.Hierarchy.DescentTerminalHomeFrame

namespace OAI
/-! # Shared issued terminal fields for the private counter and masked scalar suffix -/
namespace Hierarchy.DescentTerminalVertexFields.MaskAllocation
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks sites V B bw : ℕ}
local notation "F" => Fin (channels blocks)
local notation "size" => channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "cap" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "width" => span q t H N A p
local notation "L" => shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
local notation "C" => counter (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
local notation "known" => marks size+cap
variable (R : Channels blocks) (base header : ℕ)
local notation "end₀" => (C R base).base+cap+sites+sites+3
local notation "system" => PrivateCounter.registers (C R base) header sites cap
local notation "emit" => PrivateCounter.rawFinal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
  (homes:=sites) (C R base) system

theorem directory_room {out : ℕ} (earlier : ∀f,(R.bank f).base+(R.bank f).size≤base)
    (enough : end₀<2^bw) (later : (C R base).base≤out) :
    (guardedMask (L R base) sites).Fits bw out := by
  have old:=room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) R base earlier enough
  have cardinal : 2^(∑f:F,size f)=cap := by symm;unfold cohortSize;rw [Finset.prod_pow_eq_pow_sum]
  have tab : ((L R base).table).Fits bw out := by
    refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change 2^(∑f:F,size f)<_
      rw [cardinal]
      have h:=old.space;omega
    · change base+marks size+2^(∑f:F,size f)≤out
      rw [cardinal];change base+(marks size+cap)≤out at later;omega
  refine ⟨trivial,trivial,⟨tab,?_⟩,trivial⟩
  have row (f : F) : (maskTerm (L R base) f).Fits bw out :=
    ProtocolRAMGeneratedWrite.fits_mono _ later ⟨(old.old f).2,(old.old f).1,trivial⟩
  generalize List.finRange (channels blocks)=l
  induction l with
  | nil=>trivial
  | cons f tail ih=>exact ⟨row f,ih⟩

/-- The two literal writers and the private count never change any of the earlier
nine physical channels. Their clipped dictionary remains mounted through the count. -/
theorem prepared (m : Memory bw) (fit : V*width≤B) (prior : ∀f,(R.bank f).base+(R.bank f).size≤base)
    (headerBefore : header<base) (enough : end₀<2^bw) :
    let printed:=image (groups:=groups) (blocks:=blocks) fit base m
    let final:=emit printed
    let shelf:=L R base
    PrivateCounter.Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (C R base) bw ∧
      (system).Room bw ∧ MountedMask (groups:=groups) shelf final fit ∧
      (∀f z,(R.bank f).read final z=(R.bank f).read m z) ∧
      final header=m header := by
  intro printed final layout
  have hx:(C R base).base=base+known:=rfl
  have src:=room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) R base prior enough
  have good :=PrivateCounter.registers_room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (homes:=sites) (C R base) header (by omega) enough
  have before : ∀j,j<(C R base).base→final j=printed j :=
    fun j bound=>PrivateCounter.rawFinal_low (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
      (homes:=sites) (C R base) header printed j bound
  obtain ⟨_,preset,kept,_⟩:=install_at R base fit m (by change base+known<_;omega)
  have same (b : Bank) (h : b.base+b.size≤(C R base).base) (z : Word bw) : b.read final z=b.read printed z := by
    exact before _ ((Nat.add_lt_add_left (Nat.mod_lt z.val (Nat.two_pow_pos b.bits)) _).trans_le h)
  have cardinal : 2^(∑f:F,size f)=cap := by symm;unfold cohortSize;rw [Finset.prod_pow_eq_pow_sum]
  have tableLow : layout.table.base+layout.table.size≤(C R base).base := by
    change base+marks size+2^(∑f:F,size f)≤base+(marks size+cap);rw [cardinal];omega
  refine ⟨src,good,⟨fun f z=>(same (layout.weight f) (src.old f).2.2.2 z).trans (preset.shift f z),
    fun j=>(same layout.table tableLow (j.val:Word bw)).trans (preset.menu j)⟩,?_,?_⟩
  · intro f z
    have low : (R.bank f).base+z.val%(R.bank f).size<base:=
      (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (prior f)
    exact (same (R.bank f) (by have:=prior f;omega) z).trans (kept _ (.inl low))
  · exact (before _ (by omega)).trans (kept _ (.inl headerBefore))


end
end Hierarchy.DescentTerminalVertexFields.MaskAllocation

end OAI
