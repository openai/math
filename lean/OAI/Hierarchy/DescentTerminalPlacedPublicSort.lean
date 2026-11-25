import OAI.Hierarchy.DescentTerminalPublicSortBook
import OAI.Hierarchy.DescentTerminalPlacedChipInit

namespace OAI
/-! # Sorted cohort, immutable rank and installed matrix in one printed input state -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalRowArena
open DescentTerminalPrimitiveArena DescentExteriorShelf DescentExterior
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {blocks ν bound w : ℕ} (V : Home.Format) (S : Shape) (I : Input)
variable (R : MaskAllocation.Channels blocks) (origin privateAt : ℕ)
variable (short : ν*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ bound)
variable (literal : DescentTerminalEmitter.Compact.Literals I.sources)
set_option quotPrecheck false
local notation "base_" => afterMeter V S R origin
local notation "C" => meter V R origin
local notation "O" => registers V S R origin privateAt
local notation "A" => rowArena S I base_
local notation "L" => layout S I base_ O
local notation "m₁" => input V S I R origin privateAt short literal
local notation "μ" => fun m:Memory w => Suffix.events S L (C).layout ((A).mount (m₁ m))
local notation "P" => S.terminal.plane
local notation "off_" => takeOff S I base_

theorem public_sort (m : Memory w) (old : Earlier S I base_ (C).layout w) (space : last V S I R origin < 2^w)
    (home : Fin S.packets → Fin S.sites) (src : ∀i,I.homes.read m (i.val:Word w)=((home i).val:Word w))
    (early : I.homes.base+I.homes.size ≤ origin) (i : Fin S.packets) :
    μ m ((A).order.sorted+i.val)=(((Computability.BorderVNP.FragmentBucket.dest home).symm i).val:Word w) := by
  have lo : origin ≤ base_ := by change origin ≤ origin+_+_+_+_+3;omega
  have stored (q:Fin S.packets) : I.homes.base+(q.val:Word w).val%I.homes.size < origin :=
    (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le early
  have addr : (A).order.sorted+S.packets ≤ (A).finish := by
    have h := (A).stride_min
    change 2*S.sites+_+S.packets+1 < (A).stride at h
    change base_+17*(A).stride+S.packets ≤ base_+22*(A).stride
    omega
  apply Suffix.sorted_rows S L (C).layout ((A).mount (m₁ m)) (suffix_room S I base_ (C).layout O old space) home
  · intro q
    change (A).mount (m₁ m) (I.homes.base + (q.val : Word w).val % I.homes.size) = _
    rw [(A).mount_before _ ((stored q).trans_le lo),
      input_frame V S I R origin privateAt short literal m (.inl (stored q))]
    exact src q
  · intro q
    exact (before S I base_ O _ (by
      change I.homes.base + (q.val : Word w).val % I.homes.size < base_+2
      have h := (stored q).trans_le lo
      omega)).original
  · exact addr
  · change (A).order.sorted+S.packets ≤ (inputs S I base_ 40).base
    rw [show inputs S I base_ 40=events A S.terminal.pool from by simp [inputs]]
    exact addr.trans (Nat.le_add_right ..)

theorem public_matrix (m : Memory w) (old : Earlier S I base_ (C).layout w) (space : last V S I R origin < 2^w)
    (M : Fin (P).exteriors → DescentGL.Layout ((P).headBits+((P).headBits+(P).restBits)))
    (x : Fin (P).exteriors → Plane (P).headBits (P).restBits → Fin (P).bitLanes→Bool)
    (z : Hidden (P).exteriors (P).headBits (P).restBits (P).bitLanes→Bool)
    (initial : Loaded off_ M x z m) : Loaded off_ M x z (μ m) := by
  intro col i hi
  let a := (bank (P).headBits (P).restBits (P).bitLanes (P).exteriors off_ col.val).base+i
  have high : off_ ≤ a := by change off_ ≤ off_+_+_;omega
  obtain ⟨_,between,_,_,_⟩:=stages S I base_
  exact (events_after S I base_ (C).layout O (m₁ m) old space (between.trans high)).trans
    ((input_frame V S I R origin privateAt short literal m (.inr high)).trans (initial col i hi))

theorem public_identity (m : Memory w) (old : Earlier S I base_ (C).layout w) (space : last V S I R origin < 2^w)
    (addr : ℕ) (low : addr+pad S.packets ≤ origin) (start_ : ∀j<pad S.packets,m (addr+j)=(j:Word w))
    (j : ℕ) (hj : j < pad S.packets) : μ m (addr+j)=(j:Word w) :=
  (events_original V S I R origin privateAt short literal m old space
    ((Nat.add_lt_add_left hj _).trans_le low)).trans (start_ j hj)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
