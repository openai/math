import OAI.Hierarchy.ProtocolRAMTurnWindow
import OAI.Hierarchy.ProtocolRAMTurnChart
import OAI.Hierarchy.ProtocolRAMHalfRole

namespace OAI
/-! # The public chronological header, floor-halving table and sparse shelf directory -/
namespace Hierarchy.ProtocolRAMTurnWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProtocolRAM ProtocolRAMPackedRanked ProtocolRAMSupergroupDirectory
open scoped Fin.CommRing

namespace Layout
variable (L : Layout) {W : ℕ}

def directoryBase (start : ℕ) := start+6*2^groupBits L.rows
def halfBase (start : ℕ) := L.directoryBase start+4*2^L.romBits
def readOnlyEnd (start roles : ℕ) := L.halfBase start+span (2*roles)

def install (start roles : ℕ) (u : Fin L.rows→ProtocolRAMTurnChart.Geometry) (m : Memory W) : Memory W :=
  ProtocolRAMHalfRole.mount (L.halfBase start) roles
    (ProtocolRAMTurnDirectory.store (L.directoryBase start) L.romBits
      (ProtocolRAMTurnDirectory.words L.rows L.sites L.seats L.base)
      (ProtocolRAMTurnChart.mount start (groupBits L.rows) u m))

theorem readOnly_le (start roles : ℕ) :
    L.readOnlyEnd start roles ≤ start+52*L.rows+8*L.sites+4*roles+22 := by
  have pages := L.rom_words
  have dec := ProtocolRAMHalfRole.space_le roles
  unfold readOnlyEnd halfBase directoryBase
  omega

private theorem half_frame (start roles : ℕ) (m : Memory W) (x : ℕ)
    (off : x<start ∨ start+span (2*roles)≤x) : ProtocolRAMHalfRole.mount start roles m x=m x := by
  simp [ProtocolRAMHalfRole.mount,store,fillSegment,show ¬(start≤x ∧ x<start+span (2*roles)) by omega]

theorem outside (start roles : ℕ) (u : Fin L.rows→ProtocolRAMTurnChart.Geometry) (m : Memory W)
    (a : ℕ) (off : a<start ∨ L.readOnlyEnd start roles≤a) : L.install start roles u m a=m a := by
  have here : L.directoryBase start=start+6*2^groupBits L.rows := rfl
  have next : L.halfBase start=L.directoryBase start+4*2^L.romBits := rfl
  have stop : L.readOnlyEnd start roles=L.halfBase start+span (2*roles) := rfl
  unfold install
  rw [half_frame _ _ _ _ (by omega),ProtocolRAMTurnDirectory.frame _ _ _ _ _ (by omega)]
  unfold ProtocolRAMTurnChart.mount
  simp [fillSegment,show ¬(start≤a ∧ a<start+6*2^groupBits L.rows) by omega]

theorem loaded (start roles : ℕ) (u : Fin L.rows→ProtocolRAMTurnChart.Geometry) (m : Memory W)
    (small : L.readOnlyEnd start roles≤2^W) :
    ProtocolRAMTurnChart.Loaded start (groupBits L.rows) u (L.install start roles u m) ∧
      (∀(j : Fin 4) (t : ℕ),t<2^L.romBits →
        (ProtocolRAMTurnDirectory.bank (L.directoryBase start) L.romBits j).read
          (L.install start roles u m) (t:Word W)=ProtocolRAMTurnDirectory.words L.rows L.sites L.seats L.base j t) ∧
      ∀t,t<2*roles → (groupBank (L.halfBase start) (2*roles)).read (L.install start roles u m)
        (t:Word W)=((t/2:ℕ):Word W) := by
  let header := ProtocolRAMTurnChart.mount start (groupBits L.rows) u m
  let dir := ProtocolRAMTurnDirectory.store (L.directoryBase start) L.romBits
    (ProtocolRAMTurnDirectory.words L.rows L.sites L.seats L.base) header
  have a : L.directoryBase start=start+6*2^groupBits L.rows := rfl
  have b : L.halfBase start=L.directoryBase start+4*2^L.romBits := rfl
  have c : L.readOnlyEnd start roles=L.halfBase start+span (2*roles) := rfl
  have r := group_capacity L.rows
  have fits := slotFits (2*roles)
  have half (x : ℕ) (h : x<L.halfBase start) : L.install start roles u m x=dir x :=
    half_frame _ _ _ _ (.inl h)
  have early (x : ℕ) (h : x<L.directoryBase start) : L.install start roles u m x=header x :=
    (half x (by omega)).trans (ProtocolRAMTurnDirectory.frame _ _ _ _ _ (.inl h))
  refine ⟨?_,?_,fun t ht=>ProtocolRAMHalfRole.read _ _ _ _ ht (by omega)⟩
  · intro f i
    have mem := ProtocolRAMTurnChart.mounted start (groupBits L.rows) u m r (by omega : L.rows≤2^W) f i
    let x := start+f.val*2^groupBits L.rows+(i.val:Word W).val%2^groupBits L.rows
    have up := Nat.mul_le_mul_right (2^groupBits L.rows) (show f.val≤5 by omega)
    have rem := Nat.mod_lt (i.val:Word W).val (Nat.two_pow_pos (groupBits L.rows))
    have read := early x (by dsimp [x]; omega)
    exact read.trans mem
  · intro j t ht
    let x := L.directoryBase start+j.val*2^L.romBits+(t:Word W).val%2^L.romBits
    have up := Nat.mul_le_mul_right (2^L.romBits) (show j.val≤3 by omega)
    have rem := Nat.mod_lt (t:Word W).val (Nat.two_pow_pos L.romBits)
    exact (half x (by dsimp [x];omega)).trans (ProtocolRAMTurnDirectory.read_store _ _ _ _ _ _ ht (by omega))

/-- Read the true immutable header and addressing tables from any later memory that
has preserved this public allocation. The frame is required only on the allocated pages. -/
theorem retained (start roles : ℕ) (u : Fin L.rows→ProtocolRAMTurnChart.Geometry) (raw out : Memory W)
    (small : L.readOnlyEnd start roles≤2^W)
    (keep : ∀ a, start ≤ a → a < L.readOnlyEnd start roles → out a = L.install start roles u raw a) :
    ProtocolRAMTurnChart.Loaded start (groupBits L.rows) u out ∧
      (∀(j : Fin 4) (t : ℕ),t<2^L.romBits →
        (ProtocolRAMTurnDirectory.bank (L.directoryBase start) L.romBits j).read out (t:Word W)=
          ProtocolRAMTurnDirectory.words L.rows L.sites L.seats L.base j t) ∧
      ∀t,t<2*roles → (groupBank (L.halfBase start) (2*roles)).read out (t:Word W)=((t/2:ℕ):Word W) := by
  have initial := L.loaded start roles u raw small
  have a : L.directoryBase start=start+6*2^groupBits L.rows := rfl
  have b : L.halfBase start=L.directoryBase start+4*2^L.romBits := rfl
  have c : L.readOnlyEnd start roles=L.halfBase start+span (2*roles) := rfl
  have same (p : Bank) (z : Word W) (above : start≤p.base) (below : p.base+p.size≤L.readOnlyEnd start roles) :
      p.read out z=p.read (L.install start roles u raw) z :=
    keep _ (above.trans (Nat.le_add_right ..)) ((Nat.add_lt_add_left (Nat.mod_lt z.val (Nat.two_pow_pos p.bits)) _).trans_le below)
  refine ⟨?_,?_,?_⟩
  · intro f i
    have q := Nat.mul_le_mul_right (2^groupBits L.rows) (show f.val≤5 by omega)
    apply Eq.trans (same (ProtocolRAMTurnChart.bank start (groupBits L.rows) f) i.val (Nat.le_add_right ..) ?_) (initial.1 f i)
    change start+f.val*2^groupBits L.rows+2^groupBits L.rows≤L.readOnlyEnd start roles
    omega
  · intro j t ht
    have q := Nat.mul_le_mul_right (2^L.romBits) (show j.val≤3 by omega)
    apply Eq.trans (same (ProtocolRAMTurnDirectory.bank (L.directoryBase start) L.romBits j) t ?_ ?_) (initial.2.1 j t ht)
    · change start≤L.directoryBase start+j.val*2^L.romBits
      omega
    · change L.directoryBase start+j.val*2^L.romBits+2^L.romBits≤L.readOnlyEnd start roles
      omega
  · intro t ht
    exact (same (groupBank (L.halfBase start) (2*roles)) t (by change start≤L.halfBase start;omega) le_rfl).trans
      (initial.2.2 t ht)

end Layout
end Hierarchy.ProtocolRAMTurnWindow

end OAI
