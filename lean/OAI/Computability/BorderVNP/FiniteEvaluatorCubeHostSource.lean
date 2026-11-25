import OAI.Computability.BorderVNP.CubeHostScatterPhysicalEnds
import OAI.Computability.BorderVNP.CubeISALocalRowSpace
import OAI.Computability.BorderVNP.RoutingISACubeArena

/-! # Packed ordinal and source addresses of an owned host-scatter row

A positive-width cable with distinct endpoints has a unique location among the
physical crossings, even when the cable table has holes. Its last occupied slot
bounds the entire copied interval. Every individual source lies in the packet
or singleton allocation below the first vertex triple.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube BorderVNP.Crossing Physical Physical.Owned NativeIntervals Tally
open HostAddress RoutingISA VPVNP.MotifBase
open private key_lt from OAI.Computability.BorderVNP.CubeScatterPaddingTail

variable (a : CubeArena.Layout)
variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
variable {N : Network D P bits} {cell : N.Site → Cell} {l : HostScatter.Layout}
variable {il : NativeIntervals.Layout} {before dir mem : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin m ↪o Fin il.count} {cells : Cell ↪ ℕ} {label : Cell → Label (a.n+1) a.header.d}
variable {hz : a.header.d^(a.n+1) = il.alphabet}
variable (data : HostScatter.ResidentRows l il before dir mem a.n a.header.d a.header.blocks a.b a.h a.K a.s)
variable (rows : PhysicalRows N cell il before ord row cells label (productCode a.n a.header.d il.alphabet hz))
variable (img : il.Image before il.count dir)
variable (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
    (crossWidth N cell ∘ ord.symm) u ≤ a.header.blocks*(a.h*a.b))

include data rows in
private theorem owned_crossing {i : ℕ} (hi : i < l.count) {side : Bool} (own : l.Owned mem i side) :
    ∃ e : N.CrossingEdge cell, (row (ord e)).val = i ∧ l.width mem i = N.width e.val := by
  let r : Fin il.count := ⟨i,data.count ▸ hi⟩
  obtain ⟨src,dst,width⟩ := data.endpoints r
  have active : ¬ (il.src before r = il.dst before r ∨ il.width before r = 0) :=
    fun h => h.elim (fun same => own.2.1 (src.trans (same.trans dst.symm)))
      (fun zero => own.1 (width.trans zero))
  have present : r ∈ Set.range row := by
    by_contra missing
    exact active (rows.holes r missing)
  obtain ⟨k,hk⟩ := present
  have columns := rows.cable k
  rw [hk] at columns
  refine ⟨ord.symm k,?_,width.trans ((columns.resolve_right (fun empty => active empty.1)).2.2)⟩
  rw [ord.apply_symm_apply, hk]

include data rows img cap in
/-- The last bit of each positive-width owned crossing is in its padded label-pair interval. -/
theorem host_ordinal (i : ℕ) (hi : i < l.count) (side : Bool) (own : l.Owned mem i side) :
    mem (l.ordinals+i)+l.width mem i ≤ l.blocks*l.bc := by
  obtain ⟨e,atRow,width⟩ := owned_crossing a data rows hi own
  have live : N.width e.val ≠ 0 := width ▸ own.1
  let last : Fin (N.width e.val) := ⟨N.width e.val-1,by omega⟩
  let slot := packedSlotEmbedding N cell ord label a.header.blocks (a.h*a.b) cap ⟨e,last⟩
  have off : slot.2.val = dir (il.ordinals+(row (ord e)).val)+last.val :=
    (rows.packedSlot img _ _ cap e last).2
  have word := data.ordinals (row (ord e))
  rw [atRow] at off word
  have lim := slot.2.isLt
  change slot.2.val < a.header.blocks*(a.h*a.b) at lim
  rw [data.bankShape.1,data.bankShape.2.1,width,word]
  dsimp only [last] at off
  omega

/-- Each packed endpoint address is strictly below the vertex-triple directory. -/
theorem host_address_lt (u v : Label (a.n+1) a.header.d)
    (j : Fin (a.header.blocks*(a.h*a.b))) (side : Bool) :
    address a.header.d (a.n+1) a.header.blocks (a.h*a.b) a.header.packetBase
      (bankWidth a.n a.b a.h a.K a.s) (selectorWidth a.n a.K a.h)
      a.singleBank (code u) (code v) j.val side < a.vertexBase := by
  rw [address_eq_split]
  cases splitSlot a.n a.header.d a.header.blocks (a.h*a.b) ((u,v),j) with
  | inr single =>
    have lim := Nat.mul_le_mul_right (a.header.blocks*(a.h*a.b))
      (key_lt single.1.val.1 single.1.val.2)
    rw [Nat.succ_mul] at lim
    have within := single.2.isLt
    simp only [CubeArena.Layout.vertexBase,CubeArena.Layout.alphabet,pow_two]
    omega
  | inl z =>
    obtain ⟨p,x,k⟩ := z
    have lim := Nat.mul_le_mul_right (bankWidth a.n a.b a.h a.K a.s) (LocalRow.index_lt p)
    rw [Nat.succ_mul] at lim
    have slot := (demandOffset_range (K := a.K) (x,side) k).2
    have within : demandOffset a.n a.b a.h a.K (x,side) k < bankWidth a.n a.b a.h a.K a.s := by
      unfold bankWidth
      omega
    have past : a.packetEnd ≤ a.vertexBase := by
      have gap := a.separated
      omega
    unfold CubeArena.Layout.packetEnd CubeHeaderInstall.bankStop at past
    simp only
    omega

include data rows img cap in
/-- Every source bit of the native host copy lies strictly below the first vertex triple. -/
theorem host_source (packet : l.packets = a.header.packetBase) (single : l.singles = a.singleBank)
    (i : ℕ) (hi : i < l.count) (side : Bool) (own : l.Owned mem i side)
    (j : ℕ) (hj : j < l.width mem i) : l.source mem i side j < a.vertexBase := by
  obtain ⟨e,atRow,width⟩ := owned_crossing a data rows hi own
  let bit : Fin (N.width e.val) := ⟨j,width ▸ hj⟩
  have src := data.source_eq rows img cap e bit side
  dsimp only at src
  rw [atRow,packet,single] at src
  exact src.trans_lt (host_address_lt a _ _ _ side)

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
