import OAI.Computability.VPVNP.CompressorShrinkResidentDirectory
import OAI.Computability.VPVNP.CompressorScanProgress

/-! # Accesses and guard progress of the two native resident-owner scans -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentDirectory

open BurstRAM Compression SourceTransport ResidentOwners PairSimulation.LocalHistory
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (maps : Bool) (p : Fin 4 → Word w)

open private role_lt_end motif_lt from OAI.Computability.VPVNP.CompressorShrinkResidentDirectory

/-- The two regions the owner scan may read, containing dense absolute CD identifiers and four
role words per absolute old arc. -/
def readable (x : ℕ) :=
  ((p 0).val ≤ x ∧ x < (p 0).val + (shrinkMotifOrder X).length) ∨
    ((p 1).val ≤ x ∧ x < (p 1).val + 4*DemandRAM.absoluteCount X)

/-- The owner column written by the scan, one word per motif occurrence in the chosen field or
map order. -/
def writable (x : ℕ) := (p 3).val ≤ x ∧ x < (p 3).val+(oldOrder X maps).length

set_option maxHeartbeats 1800000 in
/-- At each reset the absolute-CD word is still live, so the second
indirect read lies in the selected role rows. Each write advances through
the dense owner column. -/
theorem Written.scanned {side : Bool} {m : Memory w} {rs : List (Report w)}
    (written : Written X maps p side m rs) (hs : p 2 = (side.toNat : Word w))
    (areas : Areas X maps p) (dir : Absolute X (p 0) m) :
    StageFrame.Scanned 0 (oldOrder X maps).length rs ∧
    Reads (readable X p) (eventLog rs) ∧ Writes (writable X maps p) (eventLog rs) := by
  let n := (oldOrder X maps).length
  let W := (worker maps).table.instantiate w p
  let es := fun (mem : Memory w) (i : Word w) => (report maps p i mem).events
  have step (j : ℕ) (_ : 0 ≤ j) (hj : j < n) (mem : Memory w) (hd : Absolute X (p 0) mem) :
      Absolute X (p 0) (after mem (es mem (j : Word w))) ∧
        Reads (readable X p) (es mem (j : Word w)) ∧ Writes (writable X maps p) (es mem (j : Word w)) := by
    let i : Fin n := ⟨j,hj⟩
    let u := (oldOrder X maps).entries i
    let word := (j : Word w)
    have room := areas.ownerRoom
    change (p 3).val+n ≤ 2^w at room
    have val : word.val=j := Nat.mod_eq_of_lt (by omega)
    have ow : (p 3+word).val=(p 3).val+j := by rw [Fin.val_add,val,Nat.mod_eq_of_lt (by omega)]
    have absRead : readable X p (absoluteAddr maps p word).val := by
      change readable X p (absoluteAddr maps p (i.val : Word w)).val
      rw [absolute_address X maps p areas i]
      exact .inl ⟨Nat.le_add_right ..,Nat.add_lt_add_left (motif_lt X u.1) _⟩
    have roleRead : readable X p (roleAddr maps p mem word).val := by
      change readable X p (roleAddr maps p mem (i.val : Word w)).val
      rw [role_address X maps p hs areas hd i]
      exact .inr ⟨(Nat.le_add_right ..).trans (Nat.le_add_right ..),role_lt_end X p u.1 _⟩
    have write : writable X maps p (p 3+word).val := by rw [ow]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩
    refine ⟨?_,?_,?_⟩
    · intro b
      have eqLen := Fintype.card_congr (ShrinkMotifOrder.stateNumber X)
      rw [Fintype.card_fin] at eqLen
      have hb : b.val < (shrinkMotifOrder X).length := b.isLt.trans_eq eqLen.symm
      have neq : (p 0).val+b.val ≠ (p 3+word).val := by
        rw [ow]
        rcases areas.absoluteApart with h | h <;> dsimp only [n] at hj <;> omega
      change (after mem (report maps p word mem).events ((p 0).val+b.val)).val = _
      rw [(ResidentOwners.native maps p word mem).2.1,writeMemory,ite_eq_right neq]
      exact hd b
    · intro a v hv
      change Event.read a v ∈ (report maps p word mem).events at hv
      simp [report] at hv
      rcases hv with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact absRead
      · exact roleRead
    · intro a v hv
      change Event.write a v ∈ (report maps p word mem).events at hv
      simp [report] at hv
      exact hv.1 ▸ write
  obtain ⟨shape,_,rd,wr⟩ := StageFrame.scan W.program (1+(code maps).length) 0 n
    (fun _ mem => Absolute X (p 0) mem) es (readable X p) (writable X maps p)
    (fun _ _ _ mem => (ResidentOwners.native maps p _ mem).1) step (Nat.zero_le _) m rs dir (by simpa only [Nat.sub_zero,Nat.cast_zero] using written.native)
  exact ⟨shape,rd,wr⟩

end CompressorRecords.ShrinkResidentDirectory

end VPVNP
end Computability
end OAI
