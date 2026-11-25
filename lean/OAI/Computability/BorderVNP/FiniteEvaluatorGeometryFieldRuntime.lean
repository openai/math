import OAI.Computability.BorderVNP.CellPacketGeometryTerminalFeeds
import OAI.Computability.BorderVNP.FiniteEvaluatorGeometryFields
import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueRuntime
import OAI.Computability.BorderVNP.PackedTerminalRetainedEmitter

/-! # Field pointer pins on the shared saved-history input and the real placement RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.FiniteFields

open Crossing Packing Packing.Inherited FrozenTape CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork FinalReports RoutingISA

variable {a m n C k w d entries A : ℕ} {σ H O : Type} [Fintype σ] [Fintype H]
    (F : Fields a m n C d k w σ) (boxes : Fin a → List (Source.Box O)) (entry : Fin entries → Fin a)
    (arena stride gap desc g digits : ℕ)

/-- The public terminal bus supplies all field pins, alongside the independently
saved historical row tape of the native geometry emitter. -/
noncomputable def liveFrame : Frame (σ ⊕ H) (Spare.Field C g digits (Fin entries) × Fin w) :=
  PackedHistoryCircuit.Retained.lift (frame F boxes entry arena stride gap desc g digits)

/-- Adding the saved-history pin bus preserves every selected field bit. -/
theorem liveFrame_eval (x : σ → Bool) (tape : H → Bool) (p : Spare.Field C g digits (Fin entries) × Fin w) :
    (liveFrame F boxes entry arena stride gap desc g digits).eval (Sum.elim x tape) p =
      (frame F boxes entry arena stride gap desc g digits).eval x p :=
  PackedHistoryCircuit.Retained.lift_eval _ x tape p

/-- The saved-history input bus requires no further gates for the finite field words. -/
theorem liveFrame_size :
    (liveFrame (H:=H) F boxes entry arena stride gap desc g digits).size =
      (frame F boxes entry arena stride gap desc g digits).size :=
  PackedHistoryCircuit.Retained.lift_size _

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (aux : N.Site → ℕ) (sid : N.Site ↪ Fin a) (edge : N.Edge ↪ Fin m) (port : P ↪ Fin n)
    {x : σ → Bool} (physical : Represents N cell aux sid edge port F x) (code : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (host : Fin entries → N.Site) (sites : ∀ i, entry i=sid (host i)) (live : Fin A → P)
    (head origin : ℕ) (before placed mem : ℕ → ℕ)
local notation "pl" => RoutingOutputs.privateLayout head origin m C entries desc gap

include physical code fit sites in
/-- The finite emitter's original-site word agrees with the physical RAM reader,
including the global placement row and the absolute receiving-bank address. -/
theorem pointer_runtime (tape : H → Bool)
    (geo : RoutingOutputs.Image F (sid ∘ host) (port ∘ live) x origin before)
    (image : (pl).Image before entries placed) (bounds : (pl).Fits w before)
    (i : Fin entries) (ptr : mem (head+64)=(pl).raw)
    (row : Directory.ISA.placement mem (pl).raw i=Directory.ISA.placement placed (pl).raw i)
    (receive : mem (mem (head+72)+2*(cell (host i)).val+1)=arena+stride*(cell (host i)).val)
    (room : opaqueFrameSlot mem head i < 2^w) :
    value (fun b => (liveFrame F boxes entry arena stride gap desc g digits).eval (Sum.elim x tape)
      (pointerField g digits i,b))=opaqueFrameSlot mem head i := by
  simpa only [liveFrame_eval,frame,Frame.select_eval,transpose,pointerField,SignedFields.pointer_bits,
    SignedFields.pointers,Frame.subst_eval] using
    OpaqueSlots.fromBank_runtime F N cell aux sid edge port physical code fit entry host sites live head origin
      arena stride gap desc before placed mem boxes geo image bounds i ptr row receive room

end CellPacketGeometry.History.Native.FiniteFields

namespace CellPacketGeometry.History.Native.FiniteFields

open Crossing Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse CellSparse.Packet
open CellSparse.Packet.Source FinalReports SiteWords VPVNP.BurstRAM RoutingISA CellPacket
open Packing.CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork

variable {s : Shape} {n C d k w t J : ℕ} {Z H R B : Type} [Fintype Z] [Fintype H] [Fintype R] [Fintype B]
    (F : Fields s.sites s.edges n C d k w Z) (occupied : Fin s.edges → Z) (portUsed : Fin n → Bool)
    (boxes : Fin s.sites → List (Source.Box (Fin J)))
    (old : Frame (Z ⊕ H) (FrozenTape.Pins R B t))
    (entry : Fin J → Fin s.sites) (arena stride gap desc g digits : ℕ) (valid : Z)
    (z : Z → Bool) (saved : H → Bool)

local notation3 (prettyPrint := false) "src" => liveFrame (H:=H) F boxes entry arena stride gap desc g digits
local notation3 (prettyPrint := false) "feed" => Terminal.feeds (s:=s) F occupied portUsed boxes old src valid
local notation3 (prettyPrint := false) "args" => (feed).arguments (Sum.elim z saved)
local notation3 (prettyPrint := false) "slot" => fun j : Fin J => value (fun b => (frame F boxes entry arena stride gap desc g digits).eval z (pointerField g digits j,b))

variable {a : ℕ} {I : Type} (T : LiveWords.Template (Spare.Field C g digits (Fin J)) I (Fin J) a (C+1))
    (read : Fin a → I → ℕ)
local notation3 (prettyPrint := false) "ref" => (fun j : Fin J => Sum.inl (Sum.inr j) : Fin J → T.Fields)

/-- The dynamic input read by each opaque reference is the actual finite-field
pointer selected by the address circuit. This identity includes zero and
does not require the factor body at this key to pass its later checks. -/
theorem sourcePointer (i : Fin J) : T.arguments args read (ref i) = slot i := by
  apply congrArg value
  funext b
  exact liveFrame_eval F boxes entry arena stride gap desc g digits z saved (pointerField g digits i,b)


open CellAddressPhysical CellAddresses RoutingOutputs

variable {D ports : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (aux : N.Site → ℕ) (sid : N.Site ↪ Fin s.sites)
    (edge : N.Edge ↪ Fin s.edges) (port : P ↪ Fin n) (physical : Represents N cell aux sid edge port F z)
    (code : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (host : Fin J → N.Site) (sites : ∀ i, entry i=sid (host i)) (live : Fin ports → P)
    (head origin : ℕ) (before placed mem : ℕ → ℕ)
local notation3 (prettyPrint := false) "layout" => privateLayout head origin s.edges C J desc gap

include physical code fit sites in
/-- The opaque reference in the emitted directory points to the address actually read
by the native receiver, including its physical cell bank and original row offset. -/
theorem sourcePointer_runtime (i : Fin J)
    (geo : Image F (sid ∘ host) (port ∘ live) z origin before)
    (image : (layout).Image before J placed) (bounds : (layout).Fits w before)
    (ptr : mem (head+64)=(layout).raw)
    (row : Directory.ISA.placement mem (layout).raw i=Directory.ISA.placement placed (layout).raw i)
    (receive : mem (mem (head+72)+2*(cell (host i)).val+1)=arena+stride*(cell (host i)).val)
    (room : opaqueFrameSlot mem head i < 2^w) :
    T.arguments args read (ref i) = opaqueFrameSlot mem head i := by
  have actual := pointer_runtime F boxes entry arena stride gap desc g digits N cell aux sid edge port
    physical code fit host sites live head origin before placed mem saved geo image bounds i ptr row receive room
  have reported := sourcePointer F occupied portUsed boxes old entry arena stride gap desc g digits valid z saved T read i
  exact reported.trans ((congrArg (ParseBatchSort.value (w:=w))
    (funext (fun bit => (liveFrame_eval F boxes entry arena stride gap desc g digits z saved (pointerField g digits i,bit)).symm))).trans actual)

end CellPacketGeometry.History.Native.FiniteFields

end BorderVNP
end Computability
end OAI
