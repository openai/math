import OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# External reads of numbered half-wire addresses

A field address is a sum of widths. For incoming slots the incidence directory
maps the destination slot to its original outgoing slot before the width is read.
Both passes stay inside their respective finite columns, for static and runtime slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.ArgumentAddress

open BurstRAM Compression PairSimulation.NodeArguments PhaseRecipe
open scoped Fin.CommRing
open private eval_port from OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress

variable {a g w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
  {I : Input} {X : State a g} {u : X.network.Site} {T : IncidenceDirectory w} {A : Arena}
  {node limit : ℕ}
local notation "ok" => Expr.ReadsFrom (· < limit) pub state m
local notation "ev" => Expr.eval pub state m
local notation "N" => Fintype.card X.Base * 2 ^ g * 2 ^ a

/-- Requires every load used to evaluate the arena base, stride, node, site, incoming column
and width column to lie below the given limit. -/
structure Readable (I : Input) (limit : ℕ) (pub : Fin 5 → Word w) (state : Word w)
    (m : Memory w) : Prop where
  arena : Expr.ReadsFrom (· < limit) pub state m I.arenaBase
  stride : Expr.ReadsFrom (· < limit) pub state m I.stride
  node : Expr.ReadsFrom (· < limit) pub state m I.node
  site : Expr.ReadsFrom (· < limit) pub state m I.siteOrd
  actualIn : Expr.ReadsFrom (· < limit) pub state m I.actualIn
  width : Expr.ReadsFrom (· < limit) pub state m I.width

private theorem port_below (col : Word w) (e : (X.Base × BitWord g) × Fin (2 ^ a))
    (room : col.val + N ≤ limit) :
    (col + IncidenceDirectory.actualPort X e).val < limit := by
  rw [IncidenceDirectory.actualPort_number]
  exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt
    (IncidenceDirectory.actualOrder X e).isLt) _).trans_le room)

private theorem sum_reads {J : Type*} (xs : List J) (f : J → Expr)
    (read : ∀ j, ok (f j)) : ok (sum (xs.map f)) := by
  induction xs with
  | nil => trivial
  | cons i is ih => exact ⟨read i, ih⟩

variable (base : Readable I limit pub state m) (h : Represents pub state m I X u T A node)
  (cols : T.ActualColumns X m)
  (inRoom : T.actualIn.val + Fintype.card X.Base * 2 ^ g * 2 ^ a ≤ limit)
  (widthRoom : T.width.val + Fintype.card X.Base * 2 ^ g * 2 ^ a ≤ limit)

include base h cols inRoom widthRoom in
private theorem half_reads (incoming : Bool) (i : Fin (2 ^ a)) : ok (I.half incoming i) := by
  have slot : ok (I.port i) := ⟨⟨base.site, trivial⟩, trivial⟩
  have idx := eval_port h i
  cases incoming with
  | false =>
    refine ⟨⟨base.width, slot⟩, ?_⟩
    change (ev I.width + ev (I.port i)).val < limit
    rw [h.width, idx]; exact port_below _ _ widthRoom
  | true =>
    refine ⟨⟨base.width, ⟨⟨base.actualIn, slot⟩, ?_⟩⟩, ?_⟩
    · change (ev I.actualIn + ev (I.port i)).val < limit
      rw [h.actualIn, idx]; exact port_below _ _ inRoom
    · change (ev I.width + m (ev I.actualIn + ev (I.port i)).val).val < limit
      rw [h.width, h.actualIn, idx, cols.actualIn]; exact port_below _ _ widthRoom

include base h cols inRoom widthRoom in
private theorem outgoing_reads (incoming : Bool) : ok (outgoing (2 ^ a) I incoming) := by
  cases incoming with
  | false => trivial
  | true => exact sum_reads _ _ (half_reads base h cols inRoom widthRoom false)

include base h cols inRoom widthRoom in
theorem field_reads_below (incoming : Bool) (j : Expr)
    (index : ok j) : ok (field (2 ^ a) I incoming j) := by
  have earlier (i : Fin (2 ^ a)) : ok (before j i) := ⟨trivial, trivial, ⟨index, trivial⟩, trivial⟩
  exact ⟨⟨base.arena, base.node, base.stride⟩, outgoing_reads base h cols inRoom widthRoom incoming,
    sum_reads _ _ (fun i => ⟨earlier i, half_reads base h cols inRoom widthRoom incoming i⟩)⟩

include base h cols inRoom widthRoom in
theorem fieldStatic_reads_below (incoming : Bool)
    (j : Fin (2 ^ a)) : ok (fieldStatic I incoming j) :=
  ⟨⟨base.arena, base.node, base.stride⟩, outgoing_reads base h cols inRoom widthRoom incoming,
    sum_reads _ _ (half_reads base h cols inRoom widthRoom incoming)⟩

end CompressorRecords.PortRefresh.ArgumentAddress

end VPVNP
end Computability
end OAI
