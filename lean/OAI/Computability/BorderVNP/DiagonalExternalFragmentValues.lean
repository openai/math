import OAI.Computability.BorderVNP.DiagonalExternalFragmentEndData

/-! # Full restored evaluator bank and report tail -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

/-- The decoder copies the original report suffix after restoring all logical slots. -/
theorem expand_append_tail (width : ℕ) (tail : List Bool) (pos : ℕ) (ss : List Span) :
    expand width tail pos ss = expand width [] pos ss ++ tail := by
  induction ss generalizing pos with
  | nil => simp [expand]
  | cons s ss ih => simp [expand,ih,List.append_assoc]

end RoutingISA.SparseExterior

namespace Diagonal.ExternalSew.Fragments

open Crossing Packing Packing.Directory Packing.CellAddresses Packing.Inherited BorderVNP.Cube
open Cube.Physical RoutingISA.SparseExterior
open scoped Classical

variable {D R r w link V g C m n entries desc : ℕ} (N : Network D (FreeBlock R V) (fun _ => g))
    (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    {l : HostScatter.Layout} {mem : ℕ → ℕ} (rows : CableRows N cell edgeID portID l mem)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g) (pp lp : ℕ → ℕ × ℕ) (supplied : ℕ → ℕ)
    (place : LivePlacement N cell edgeID portID lp) (counts : ∀ c : Fin C, supplied c.val = suppliedSize N cell c)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (input : FreePort R r w → Bool) (ends : Bool → LiveBit N cell → Bool)

local notation "bank" => fillFree hg room input (fun _ => false)
local notation "data" => endData N cell edgeID portID bank ends
local notation "dir" => freeDirectory R r w link V g entries desc
local notation "quads" => stream l mem supplied (Layout.directory dir pp lp)

include rows place counts privateAfter in
/-- At every typed ordinal, restored bits give the true evaluator's external
argument with distinct routed crossing ends and zero in unused grouped lanes. -/
theorem expand_endSupply_bit (c : Fin C) (tail : List Bool) (k : Fin (suppliedSize N cell c))
    (order : Ordered (supplied c.val) 0 (spans quads data c.val)) :
    (expand (supplied c.val) tail 0 (spans quads data c.val))[k.val]? =
      some (Placement.endSupply N cell c edgeID portID bank ends k) := by
  obtain ⟨u,j,rfl⟩ := suppliedOrdinal_surj N edgeID portID cell c k
  rw [← endData_at]
  rcases u with u | p
  · exact expand_boundary_lane_read rows supplied _ data c u j tail order
  · let a : Σ _ : FreeBlock R V, Fin g := ⟨p.val,j⟩
    let pos := laneAddress lp a
    let k := suppliedOrdinal N cell c edgeID portID (.inr p) j
    have addr := placedOrdinal N cell edgeID portID place c p j
    change laneAddress lp a = (c.val,k.val) at addr
    by_cases h : a ∈ Set.range (freeLane hg room)
    · obtain ⟨z,hz⟩ := h
      have read := expand_free_lane_read (entries := entries) (desc := desc) hg room pp lp supplied
        (live_base_fits N cell edgeID portID place supplied counts) l mem data z tail
      dsimp only at read
      rw [hz,addr] at read
      exact read order
    · have read := expand_unused_lane (desc := desc) N cell edgeID portID rows hg room pp lp place supplied
        counts privateAfter data tail a h
      dsimp only at read
      rw [addr] at read
      have b := endData_group N cell edgeID portID place bank ends a
      change (data) (laneAddress lp a).1 (laneAddress lp a).2 = (bank) a.1 a.2 at b
      rw [addr] at b
      have zero : (bank) a.1 a.2 = false := Function.extend_apply' _ _ _ h
      exact (read order).trans (congrArg some (b.trans zero).symm)

include rows place counts privateAfter in
/-- Exact payload seen by the private field evaluator after sparse decoding,
including its original full report tail. -/
theorem expand_endSupply (c : Fin C) (tail : List Bool)
    (order : Ordered (supplied c.val) 0 (spans quads data c.val)) :
    expand (supplied c.val) tail 0 (spans quads data c.val) =
      List.ofFn (Placement.endSupply N cell c edgeID portID bank ends) ++ tail := by
  rw [expand_append_tail]
  apply congrArg (· ++ tail)
  have hn := expand_length [] (spans quads data c.val) order
  simp only [Nat.zero_add,List.length_nil,Nat.add_zero] at hn
  replace hn := hn.trans (counts c)
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hn)
  intro i hi hbound
  let j : Fin (suppliedSize N cell c) := ⟨i,hi.trans_eq hn⟩
  have h := expand_endSupply_bit (desc := desc) N cell edgeID portID rows hg room pp lp supplied place
    counts privateAfter input ends c [] j order
  exact (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans h)).trans (List.getElem_ofFn ..).symm

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
