import OAI.Computability.VPVNP.PairShrinkSurvivingAddress
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# Read bounds for the private argument address calculation

A width prefix uses the actual slot directory of the chosen endpoint.
An incoming slot first indexes the inverse incidence column and then the
width column by the outgoing arc returned there. Both numerical indices
belong to the same finite actual port range.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ArgumentReadBounds

open BurstRAM BurstRAM.PrivateRAM Compression NodeArguments CompressorRecords
open CompressorRecords.PortRefresh.ArgumentAddress CompressorRecords.PhaseRecipe
open ShrinkOldHalves.Physical
open private unpack word_of_val from OAI.Computability.VPVNP.PairShrinkOldHalfAddresses
open private eval_port from OAI.Computability.VPVNP.CompressorRecordRefreshArgumentAddress
open scoped Fin.CommRing

variable {a g w : ℕ} {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
variable (X : State a g) (u : X.network.Site) (k : Fin (2 ^ a))
variable (Hdr : Header) (T : IncidenceDirectory w) (A : Arena) {layer pitch : ℕ}
local notation "N" => Fintype.card X.Base * 2 ^ g * 2 ^ a
local notation "ev" => Expr.eval pub state mem

/-- The four scalar input expressions common to old and new private argument field lookups. -/
structure FieldsReadable (Hdr : Header) (H : ℕ) (pub : Fin 5 → Word w) (state : Word w)
    (mem : Memory w) : Prop where
  arena : Hdr.arenaBase.ReadsFrom (· < H) pub state mem
  stride : Hdr.arenaStride.ReadsFrom (· < H) pub state mem
  actualIn : Hdr.actualIn.ReadsFrom (· < H) pub state mem
  width : Hdr.width.ReadsFrom (· < H) pub state mem

private theorem column_lt (col : Word w) (e : (X.Base × BitWord g) × Fin (2 ^ a)) (H : ℕ)
    (room : col.val + N ≤ H) : (col + IncidenceDirectory.actualPort X e).val < H := by
  have bound := (IncidenceDirectory.actualOrder X e).isLt
  rw [IncidenceDirectory.actualPort_number]
  change (col.val + (IncidenceDirectory.actualOrder X e).val % 2 ^ w) % 2 ^ w < H
  exact (Nat.mod_le ..).trans_lt <| lt_of_lt_of_le
    (Nat.add_lt_add_left ((Nat.mod_le ..).trans_lt bound) _) room

private theorem sum_safe {α : Type*} (xs : List α) (f : α → Expr) (H : ℕ)
    (h : ∀ x, (f x).ReadsFrom (· < H) pub state mem) :
    (sum (xs.map f)).ReadsFrom (· < H) pub state mem := by
  induction xs with
  | nil => trivial
  | cons i is ih => exact ⟨h i, ih⟩

/-- Every nested load of the complete private address lies in the allowed prefix.
The endpoint port already includes the incoming or outgoing orientation. -/
theorem field (stored : Hdr.Stored T A layer pitch pub state mem)
    (cols : T.ActualColumns X mem) (capacity : N ≤ 2 ^ w) (degreeFits : 2 ^ a < 2 ^ w)
    (node port : Expr) (dir : Bool)
    (portEq : ev port = IncidenceDirectory.actualPort X (u, k)) (H : ℕ)
    (ins : FieldsReadable Hdr H pub state mem)
    (nodeSafe : node.ReadsFrom (· < H) pub state mem)
    (portSafe : port.ReadsFrom (· < H) pub state mem)
    (inRoom : T.actualIn.val + N ≤ H) (widthRoom : T.width.val + N ≤ H) :
    (ShrinkSurvivingAddress.field (2 ^ a) Hdr node dir port).ReadsFrom (· < H) pub state mem := by
  let E := { Hdr.input (2 ^ a) port with node := node }
  let site := siteOrdinal X u
  have portVal : (ev port).val = site * 2 ^ a + k.val := by
    rw [portEq, IncidenceDirectory.actualPort_number]
    exact (Nat.mod_eq_of_lt ((IncidenceDirectory.actualOrder X (u, k)).isLt.trans_le capacity)).trans
      (IncidenceDirectory.actualOrder_val X (u, k))
  have dval : (CursorRAM.encode w (2 ^ a)).val = 2 ^ a := Nat.mod_eq_of_lt degreeFits
  have parts := unpack (ev port) (CursorRAM.encode w (2 ^ a)) site k.val
    (by rw [dval]; exact portVal) (by rw [dval]; exact k.isLt)
  have rep : Represents pub state mem E X u T A (ev node).val :=
    ⟨stored.arenaBase, stored.arenaStride, word_of_val rfl, word_of_val parts.1,
      stored.actualIn,
      stored.width⟩
  let safe := Expr.ReadsFrom (· < H) pub state mem
  have halfSafe (incoming : Bool) (i : Fin (2 ^ a)) : safe (E.half incoming i) := by
    have pi : safe (E.port i) := ⟨⟨⟨portSafe, trivial⟩, trivial⟩, trivial⟩
    have value := eval_port rep i
    have inAt : (ev E.actualIn + ev (E.port i)).val < H := by
      rw [rep.actualIn, value]
      exact column_lt X _ _ H inRoom
    cases incoming with
    | false =>
      refine ⟨⟨ins.width, pi⟩, ?_⟩
      change (ev E.width + ev (E.port i)).val < H
      rw [rep.width, value]
      exact column_lt X _ _ H widthRoom
    | true =>
      refine ⟨⟨ins.width, ⟨⟨ins.actualIn, pi⟩, inAt⟩⟩, ?_⟩
      change (ev E.width + mem (ev E.actualIn + ev (E.port i)).val).val < H
      rw [rep.width, rep.actualIn, value, cols.actualIn]
      exact column_lt X _ _ H widthRoom
  have side : safe (outgoing (2 ^ a) E dir) := by
    cases dir with
    | false => trivial
    | true => exact sum_safe _ _ H (halfSafe false)
  let j := port.mod (.lit (2 ^ a))
  have selector (i : Fin (2 ^ a)) : safe (before j i) :=
    ⟨trivial, ⟨trivial, ⟨⟨⟨portSafe, trivial⟩, trivial⟩, trivial⟩⟩⟩
  exact ⟨⟨ins.arena, nodeSafe, ins.stride⟩, side,
    sum_safe _ _ H (fun i ↦ ⟨selector i, halfSafe dir i⟩)⟩

/-- The old half lookup also reads the forward incidence column at the source arc
when the desired endpoint is incoming. Its node comes from the old layer's site ordinal. -/
theorem old_field (stored : Hdr.Stored T A layer pitch pub state mem)
    (cols : T.ActualColumns X mem) (capacity : N ≤ 2 ^ w) (degreeFits : 2 ^ a < 2 ^ w)
    (arc : Expr) (e : (X.Base × BitWord g) × Fin (2 ^ a)) (dir : Bool)
    (arcEq : ev arc = IncidenceDirectory.actualPort X e)
    (portEq : ev (Hdr.port arc dir) = IncidenceDirectory.actualPort X (u, k)) (H : ℕ)
    (ins : FieldsReadable Hdr H pub state mem)
    (arcSafe : arc.ReadsFrom (· < H) pub state mem)
    (outSafe : Hdr.actualOut.ReadsFrom (· < H) pub state mem)
    (layerSafe : Hdr.layerBase.ReadsFrom (· < H) pub state mem)
    (pitchSafe : Hdr.layerStride.ReadsFrom (· < H) pub state mem)
    (outRoom : T.actualOut.val + N ≤ H) (inRoom : T.actualIn.val + N ≤ H)
    (widthRoom : T.width.val + N ≤ H) :
    (Hdr.field (2 ^ a) arc dir).ReadsFrom (· < H) pub state mem := by
  let p := Hdr.port arc dir
  have portSafe : p.ReadsFrom (· < H) pub state mem := by
    cases dir with
    | false => exact arcSafe
    | true =>
      refine ⟨⟨outSafe, arcSafe⟩, ?_⟩
      change (ev Hdr.actualOut + ev arc).val < H
      rw [stored.actualOut, arcEq]
      exact column_lt X _ _ H outRoom
  let node := (Hdr.input (2 ^ a) p).node
  have nodeSafe : node.ReadsFrom (· < H) pub state mem :=
    ⟨layerSafe, pitchSafe, portSafe, trivial⟩
  exact field X u k Hdr T A stored cols capacity degreeFits node p dir portEq H ins nodeSafe
    portSafe inRoom widthRoom

end PairSimulation.ArgumentReadBounds

end VPVNP
end Computability
end OAI
