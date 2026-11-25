import OAI.Computability.BorderVNP.TeamSiteRowUnique
import OAI.Computability.BorderVNP.TeamSiteConsistencyEndpoints
import OAI.Computability.BorderVNP.TeamSiteEndpointTimes

/-! # Local sorter checks and the unique decoded history of a team

A real processor's post-pass inspects its own row and possibly one empty padded
row. Its local input therefore gives exactly the verdict computed with the entire
array once the decoded predecessor timestamp is known. On a fixed link assignment
the complete physical branch spelling determines all the semantic rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteTraversal

open VPVNP RAMTape TeamTapeHandoff TeamContraction.Wires TeamSiteConsistency TeamTapeSorting
open TeamSite TeamTapeInputRoute.Verify TeamEventRecords
open BurstRAM (Word)
open RAMSerialization (WordRecord)
open TeamRAM (Event)

variable {w r k e d W p pub a m g : ℕ} {Q Γ : Type}

private theorem valid_same (hw : 2 ≤ W) (hc : 2^d*2^e < 2^W) (f : Fields d e W)
    (v : Word d) (xs ys : Word d → List (WordRecord W)) (eq : xs v = ys v) :
    valid hw hc f (rowInput e xs) v ↔ valid hw hc f (rowInput e ys) v := by
  have blocks : RAMSort.block (2+e) v.val (wire (rowInput e xs)) =
      RAMSort.block (2+e) v.val (wire (rowInput e ys)) := by
    funext i
    simp [RAMSort.block, wire, rowInput, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt i.isLt,
      Nat.mul_comm v.val, Nat.mod_eq_of_lt i.isLt, v.isLt,eq]
  simp only [valid,blocks]

/-- The actual sort predicate evaluated on the real row data and the empty secondary
row, before any data at other sites is known. -/
def sorted (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 r)*2^e < 2^(w+1))
    (input : Fin r → List Bool) (links : Edge r k w e (w+1) → Bool) (j : Fin r) (f : Frame w k) (es : List (Event w)) : Prop :=
  let slots := TeamTapeInputEmit.records (w+1) (TeamTapeInputEmit.rowStart input j) (input j) ++
    TeamEventRecords.historySlots (f.elapsed.val+1) es
  let rows := fun v => if v = primary j then slots else []
  ownerValid hw hc (edgeEquiv links).2 (rowInput e rows) (primary j) (secondary j)

/-- The local memory post-pass and the complete physical sorting array agree exactly
on this owner's data. The time equality follows by counting charges along the shared
predecessor frames. -/
theorem sorted_iff_global (hw : 2 ≤ w+1) (hc : 2^(Nat.clog 2 r)*2^e < 2^(w+1))
    (input : Fin r → List Bool) (links : Edge r k w e (w+1) → Bool) (blocks : Fin r → List (Event w))
    (j : Fin r) (f : Frame w k) (elapsed : f.elapsed.val+1 = 1+blockOffset blocks j) :
    sorted hw hc input links j f (blocks j) ↔
      ownerValid hw hc (edgeEquiv links).2 (array e input blocks) (primary j) (secondary j) := by
  let slots := TeamTapeInputEmit.records (w+1) (TeamTapeInputEmit.rowStart input j) (input j) ++
    TeamEventRecords.historySlots (f.elapsed.val+1) (blocks j)
  let xs (v : Word (Nat.clog 2 r)) := if v = primary j then slots else []
  let ys := padRows (realRows input blocks)
  have main : xs (primary j) = ys (primary j) := by
    simp [xs,slots,ys,padRows,realRows,primary,elapsed]
  have other (u : Word (Nat.clog 2 r)) (hu : secondary j = some u) : xs u = ys u := by
    unfold secondary at hu
    split at hu <;> try contradiction
    cases hu
    have notReal : ¬ j.val+r < r := by omega
    have neq : (⟨j.val+r,by assumption⟩ : Word (Nat.clog 2 r)) ≠ primary j := by
      intro h
      have hh := congrArg Fin.val h
      change j.val+r = j.val at hh
      have := j.isLt
      omega
    simp [xs,ys,padRows,notReal,neq]
  change (valid hw hc _ (rowInput e xs) _ ∧ ∀ u, secondary j = some u → valid hw hc _ (rowInput e xs) u) ↔
    valid hw hc _ (rowInput e ys) _ ∧ ∀ u, secondary j = some u → valid hw hc _ (rowInput e ys) u
  apply and_congr (valid_same hw hc _ _ _ _ main)
  exact forall_congr' fun u => imp_congr_right fun hu => valid_same hw hc _ _ _ _ (other u hu)

/-- Two fully checked histories with the same raw interior assignment and the same
physical choice spelling coincide. The argument uses the unique incoming frame at
each receiver and the actual native decoder for every local block. -/
theorem histories_unique_fuel (cfg : Setup r w p k pub a e) (lib : Fin a → Macro Q Γ m g)
    (fuel : ℕ) (hlib : cfg.lib = TeamSiteEvents.macros lib fuel) (bound : max 1 (fuel-1) ≤ cfg.privateClock)
    (x y : cfg.Histories) (links : x.val.links = y.val.links)
    (bits : ∀ j, chunkBits (x.val.blocks j) = chunkBits (y.val.blocks j)) : x = y := by
  have hx := (cfg.endpointChecks_iff_fuel x.val lib fuel hlib bound).mpr x.property
  have hy := (cfg.endpointChecks_iff_fuel y.val lib fuel hlib bound).mpr y.property
  have incoming := same_inputs hx.2.2.1 (raw := (edgeEquiv x.val.links).1) (links ▸ hy.2.2.1)
  have eq (j : Fin r) : x.val.blocks j = y.val.blocks j ∧ x.val.frames j = y.val.frames j := by
    have left := hx.1 j
    have right := hy.1 j
    rw [← incoming] at right
    apply EndpointRow.determined cfg.program cfg.pub lib fuel cfg.block cfg.limit cfg.cap cfg.pcs _
      (bits := bits j)
    · simpa only [← hlib] using left
    · simpa only [← hlib] using right
  apply Subtype.ext
  obtain ⟨⟨xb,xf,xl⟩,xvalid⟩ := x
  obtain ⟨⟨yb,yf,yl⟩,yvalid⟩ := y
  exact (congrArg₂ (fun u v => RawHistory.mk u v xl) (funext fun j => (eq j).1) (funext fun j => (eq j).2)).trans
    (congrArg (RawHistory.mk yb yf) links)

/-- The same uniqueness at a native evaluator clock equal to the declared choice bound. -/
theorem histories_unique (cfg : Setup r w p k pub a e) (lib : Fin a → Macro Q Γ m g)
    (hlib : cfg.lib = TeamSiteEvents.macros lib cfg.privateClock) (fuel : 0 < cfg.privateClock)
    (x y : cfg.Histories) (links : x.val.links = y.val.links)
    (bits : ∀ j, chunkBits (x.val.blocks j) = chunkBits (y.val.blocks j)) : x = y :=
  histories_unique_fuel cfg lib cfg.privateClock hlib (by omega) x y links bits

end TeamSiteTraversal

end BorderVNP
end Computability
end OAI
