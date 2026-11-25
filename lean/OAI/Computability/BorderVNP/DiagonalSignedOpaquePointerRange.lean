import OAI.Computability.BorderVNP.CellPacketGeometrySignedFields
import OAI.Computability.BorderVNP.FragmentRowsSparsePatch
import OAI.Computability.BorderVNP.PackedGridSeedWordsFit

/-! # The stored original-description pointer and its two protected native source regions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.PrivatePlacement

open scoped Classical

/-- The occupied prefix ending at this real original lies in the complete
description allocation of its own receiving cell. -/
theorem prefixCounts_entry {C J : ℕ} (actual : Fin J → Fin C) (old : ℕ → ℕ)
    (owners : ∀ i, old i.val=(actual i).val) (desc : ℕ) (i : Fin J) :
    prefixCounts old desc i.val (actual i).val + desc ≤
      ∑ j : Fin J, if actual j=actual i then desc else 0 := by
  let x := fun j => if old j=(actual i).val then desc else 0
  have finish : prefixCounts old desc i.val (actual i).val + desc = ∑ j ∈ Finset.range (i.val+1), x j := by
    rw [Finset.sum_range_succ]
    simp only [prefixCounts,x,owners i,ite_true]
  have whole : (∑ j ∈ Finset.range J, x j) = ∑ j : Fin J, if actual j=actual i then desc else 0 := by
    rw [←Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp only [x,owners j,Fin.val_inj]
  rw [finish,←whole]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono i.isLt) (fun _ _ _ => Nat.zero_le _)

end RoutingISA.PrivatePlacement

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Packing Packing.Inherited CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork RoutingISA

variable {σ Orig Port : Type} [Fintype σ] [Fintype Port]
    {s m n d k w entries D : ℕ} {bits : Port → ℕ} (a : SignedTaskArena.Layout)
    (F : Fields s m n a.cube.cells d k w σ) (boxes : Fin s → List (Source.Box Orig)) (entry : Fin entries → Fin s)
    (N : Network D Port bits) (cell : N.Site → Fin a.cube.cells) (state : N.Site → Site)
    (sites : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : Port ↪ Fin n)
    (x : σ → Bool) (physical : Represents N cell (fun v => (state v).size) sites edge port F x)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^w)
    (host : Fin entries → N.Site) (hosts : ∀ i, entry i=sites (host i))
    (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell (host i)).val)

include physical sizeFit hosts owners in
/-- The genuine original-description address lies beyond the actual supplied
region and every bit of a returning report's reserved tail, while the whole
allocated description stays inside this same physical cell stride. -/
theorem pointer_report_gap (gap desc gadgets digits : ℕ)
    (wordFit : a.cube.stop < 2^w)
    (capacity : ∀ c, suppliedSize N cell c + gap +
      (∑ j : Fin entries, if cell (host j)=c then desc else 0) ≤ a.cube.cellStride)
    (i : Fin entries) :
    let slot := value (fun j => (frame F boxes entry a.cube.cellBank a.cube.cellStride gap desc gadgets digits).eval x (.inr i,j))
    let c := cell (host i)
    let bank := a.cube.cellBank+a.cube.cellStride*c.val
    (∀ tail ≤ gap, bank+suppliedSize N cell c+tail ≤ slot) ∧ slot+desc ≤ bank+a.cube.cellStride ∧
      slot=bank+suppliedSize N cell c+gap+PrivatePlacement.prefixCounts old desc i.val c.val := by
  intro slot c bank
  let who := fun j : Fin entries => cell (host j)
  let head := a.cube.cellBank+a.cube.cellStride*c.val+suppliedSize N cell c+gap
  let prior := PrivatePlacement.prefixCounts old desc i.val c.val
  have bnd : prior+desc ≤ ∑ j, if who j=c then desc else 0 := PrivatePlacement.prefixCounts_entry who old owners desc i
  have cap := capacity c
  change suppliedSize N cell c+gap+(∑ j, if who j=c then desc else 0) ≤ a.cube.cellStride at cap
  have last := Nat.mul_le_mul_right a.cube.cellStride c.isLt
  rw [Nat.succ_mul,Nat.mul_comm c.val a.cube.cellStride] at last
  have ending : head+prior+desc ≤ a.cube.stop := by
    change _ ≤ a.cube.cellBank+a.cube.cells*a.cube.cellStride
    dsimp only [head]
    omega
  have byCell (b : Fin a.cube.cells) : (∑ j, if cell (host j)=b then desc else 0) < 2^w := by
    have h := capacity b
    have stride := (Nat.le_mul_of_pos_left a.cube.cellStride (Nat.zero_lt_of_lt c.isLt)).trans
      (Nat.le_add_left (a.cube.cells*a.cube.cellStride) a.cube.cellBank)
    change a.cube.cellBank+a.cube.cells*a.cube.cellStride < _ at wordFit
    omega
  have limit : head+prior < 2^w := ((Nat.le_add_right _ desc).trans ending).trans_lt wordFit
  have eqn : slot = head+prior := pointer_read F boxes entry a.cube.cellBank a.cube.cellStride gap desc gadgets digits
    N cell state sites edge port x physical sizeFit host hosts old owners (by omega) byCell i limit
  rw [eqn]
  refine ⟨fun tail le => ?_,?_,rfl⟩
  · change bank+suppliedSize N cell c+tail ≤ bank+suppliedSize N cell c+gap+prior
    omega
  · change bank+suppliedSize N cell c+gap+prior+desc ≤ bank+a.cube.cellStride
    omega

include physical sizeFit hosts owners in
/-- The actual frozen scalar-field producer places every opaque pointer and
its whole allocated description before the sparse external writer. Its source
range is disjoint from the marker and new merged-count control words. Only
the descriptions owned by each cell enter its stride inequality. -/
theorem pointer_bank (frameBase ctl gap desc gadgets digits : ℕ) (safe : a.SparsePlacement frameBase ctl)
    (wordFit : a.cube.stop < 2^w)
    (capacity : ∀ c, suppliedSize N cell c + gap +
      (∑ j : Fin entries, if cell (host j)=c then desc else 0) ≤ a.cube.cellStride)
    (i : Fin entries) :
    let slot := value (fun j => (frame F boxes entry a.cube.cellBank a.cube.cellStride gap desc gadgets digits).eval x (.inr i,j))
    a.cube.cellBank ≤ slot ∧ slot+desc ≤ a.fragments.external ∧
      ∀ addr ≥ slot, addr ≠ frameBase+90 ∧ addr ≠ ctl+29 := by
  intro slot
  let c := cell (host i)
  let bank := a.cube.cellBank+a.cube.cellStride*c.val
  have inside := pointer_report_gap a F boxes entry N cell state sites edge port x physical sizeFit host hosts old owners
    gap desc gadgets digits wordFit capacity i
  have last := Nat.mul_le_mul_right a.cube.cellStride c.isLt
  rw [Nat.succ_mul,Nat.mul_comm c.val a.cube.cellStride] at last
  have bankEnd : bank+a.cube.cellStride ≤ a.cube.stop := by
    change a.cube.cellBank+a.cube.cellStride*c.val+a.cube.cellStride ≤ a.cube.cellBank+a.cube.cells*a.cube.cellStride
    omega
  have ending : slot+desc ≤ a.cube.stop := inside.2.1.trans bankEnd
  have st := (a.sparse_order safe.cells).2.1
  have external : a.fragments.start ≤ a.fragments.external := by
    unfold FragmentArena.Layout.external FragmentArena.Layout.cursors FragmentArena.Layout.triples FragmentArena.Layout.pairs FragmentArena.Layout.quads
    omega
  have low : a.cube.cellBank ≤ slot := by
    have keep := inside.1 0 (Nat.zero_le gap)
    change bank+suppliedSize N cell c+0 ≤ slot at keep
    dsimp only [bank] at keep
    omega
  exact ⟨low,ending.trans (st.trans external),fun addr below => by
    have before := safe.beforeControl
    have after := safe.beforeBank
    omega⟩

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
