import OAI.Computability.VPVNP.PairShrinkABBuffers
import OAI.Computability.VPVNP.PairSimulationReverseSlices

/-!
# Native AB copies from the independent old half-wire buffers

The indexed-starts scan records intersections of thick wires with AB fields in
source-major order. A resident map visits one column of the resulting bank.
The slice loop reads its length and, for a positive intersection, both offsets.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkAB

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData CompressorRecords
open ShrinkSliceArrays SliceSchedule
open scoped Fin.CommRing

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (width : Arc V H Tag L d c → ℕ) {b : Site V Tag L × Fin d} (m : P.MotifFiber b)
variable {w p r k : ℕ}

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag]
  [DecidableEq L] in
private theorem frame_fit (B : Word w) (a : P.ThickFiber b)
    (space : B.val + IndexedStarts.capacity (2 ^ c * d / 4) (pieceCount d c) < 2 ^ w) :
    frame P number order m B a + 2 < 2 ^ w := by
  have h : (order b a).val * pieceCount d c + (number b m).val <
      (2 ^ c * d / 4) * pieceCount d c := calc
    _ < (order b a).val * pieceCount d c + pieceCount d c := Nat.add_lt_add_left (number b m).isLt _
    _ = ((order b a).val + 1) * pieceCount d c := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (order b a).isLt
  unfold frame
  unfold IndexedStarts.capacity at space
  omega

/-- Execute a complete source-major interval at an actual old endpoint. The old
field remains intact. The destination can subsequently be filled by the other
thick arcs of the bundle. -/
theorem execute_piece {M : Machine w p r k} {pc : Fin 11 → Fin p}
    {reg : Fin 6 ↪ Fin r} {arcPC : Fin 7 → Fin p} {done : Fin p}
    (linked : PrivateSlices.Linked M pc reg (arcPC 0) done)
    (copy : PrivateFields.Linked M .copy arcPC (PrivateSlices.copyRegs reg) done)
    (cfg : Config w p r) (entry : cfg.pc = pc 0) (one : cfg.reg (reg 3) = 1)
    {mem : Memory w} {B : Word w}
    (stored : IndexedStarts.Stored B (thickWidths P order width b) (abWidths P number width b) mem)
    (space : B.val + IndexedStarts.capacity (2 ^ c * d / 4) (pieceCount d c) < 2 ^ w)
    (a : P.ThickFiber b) (src dst : ℕ)
    (hf : cfg.reg (reg 5) = (frame P number order m B a : Word w))
    (source : cfg.reg (reg 0) = (src : Word w)) (dest : cfg.reg (reg 2) = (dst : Word w))
    (apart : src + width a.1.1 ≤ dst) (room : dst + P.abWidth number width m.val < 2 ^ w)
    (data : (a : P.ThickFiber b) → Fin (width a.1.1) → Bool)
    (old : ∀ i, cfg.privateMem ((src + i.val : ℕ) : Word w) = PrivateFields.bitValue w (data a i)) :
    ReverseSlices.FrameResult M reg done cfg mem (frame P number order m B a : Word w)
      (dst + (P.demandSlice number order width b a m).targetOffset)
      (copyBits P number order width m data a) := by
  let s := P.demandSlice number order width b a m
  let bs := copyBits P number order width m data a
  have len : bs.length = s.length := List.length_ofFn
  obtain ⟨h₁, h₂⟩ := frame_words P number order width m stored a
  obtain ⟨h₃, h₄⟩ := ReverseSlices.oriented_frame_words false mem
    (frame P number order m B a) (frame P number order m B a)
    s.sourceOffset s.targetOffset bs.length rfl (frame_fit P number order m B a space)
    (h₁.trans len.symm) (fun hp ↦ h₂ (len ▸ hp))
  have sourceEnd (hp : 0 < bs.length) : s.sourceOffset + bs.length ≤ width a.1.1 := by
    let last : Fin s.length := ⟨bs.length - 1, by omega⟩
    have h := source_bound P number order width m a last
    change s.sourceOffset + (bs.length - 1) < width a.1.1 at h
    omega
  apply ReverseSlices.execute_stored_frame false linked copy cfg entry one mem _ hf src dst
    s.sourceOffset s.targetOffset source dest bs h₃ h₄
  · intro hp
    have hs := sourceEnd hp
    have ht := target_bound P number order width m a (len ▸ hp)
    change s.targetOffset + s.length ≤ _ at ht
    omega
  · intro hp
    exact Or.inr (by have hs := sourceEnd hp; omega)
  · intro i
    let ix : Fin s.length := ⟨i.val, len ▸ i.isLt⟩
    have h := old ⟨s.sourceOffset + i.val, source_bound P number order width m a ix⟩
    simpa only [bs, copyBits, List.getElem_ofFn, Nat.add_assoc] using h

end PairSimulation.ShrinkAB

end VPVNP
end Computability
end OAI
