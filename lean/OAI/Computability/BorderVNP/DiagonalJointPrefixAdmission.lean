import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalPreparedBroadcastAdmission
import OAI.Computability.BorderVNP.DiagonalSignedPublishedWriter

/-! # Admission of the directory reached by a joint signed prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open RoutingISA.LocalRow PackedHistoryCircuit Packing Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun u => (B u).start)) (u : Fin (R+1))
local notation3 (prettyPrint := false) "lib" => install SparseExterior.driver n (B u).start.routines
local notation3 (prettyPrint := false) "frame₀" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "fields₀" => G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "Full" => Returns (withStartup pinGeometry) (pub u) lib (reg u)
  (processorMemory fields₀ w)
variable {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {mid : Memory w} {base : ℕ}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {width : I → ℕ}
    (writer : SlottedWriter ar dir pp lp pins (pub u) mid base host key width)
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ)
    (word : List Bool) (claims : List (List Bool)) (pad : ℕ) (raw : Broadcast ar.n ar.header.d ar.header.cap) (X : ℕ)
    (input : PinnedRawInput (ar:=ar) (D:=dir) (pp:=pp) (lp:=lp) (pub:=pub u) (slotted:=mid) (base:=base)
      (G.transferFrame u (args u).header (args u).dst) old fresh gates outputs bitWidth off ell controls word claims pad raw R X)

local notation3 (prettyPrint := false) "dd" => dir.directory pp lp
local notation3 (prettyPrint := false) "pubMem" => Directory.ISA.publish mid (pub u 0).val base dd
local notation3 (prettyPrint := false) "sizes" => fun i : Fin (dd).length => (dd)[i.val].width

include writer input in
set_option maxRecDepth 5500 in
/-- A team's own substitution and pre-call trace authenticate its reached
directory, including the decoded coordinate, minimum test and per-team capacity.
The directory's full profile return is precisely the dictionary entry at this pin. -/
theorem joint_published_admission
    (profile : (Fin (B u).start.guessWidth → Bool) ≃ Full)
    (spelling : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v)
    (ret : Full) (digits : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn (a u).1)
    (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) (pub u) lib ret.val.2.1 ret.val.2.2)
    (stored : scan.val.2.2=pubMem)
    {dim : ℕ} {Names : Type*} {bits : Names → ℕ} (N : Network dim Names bits)
    (tile : N.Site → Fin ar.cells) (recv : Fin (dd).length → Fin ar.cells)
    (placed : PublishedRowPlacement N tile recv sizes (pub u 0).val scan.val.2.2) (hd : 0<ar.header.d) :
    let label := meanPackedLabel N tile recv sizes (List.finRange ar.cells) ar.n ar.header.d hd
    let decl : LengthDeclaration ar.n ar.header.d := (Fin.ofNat (ar.n+1) (readCode (ar.n+1) raw.1),
      fun pair j => readCode (ar.header.cap+1) (raw.2 pair j))
    let mass := declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv sizes
    let group := fun j : Fin ar.header.d => TeamNative.owner R mass j.val
    let owner := fun c : ℕ => if h:c<ar.cells then group (label ⟨c,h⟩ decl.1) else 0
    profile (a u).1=ret ∧ declarationInRange raw ∧
      broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv sizes raw ∧
      Nonempty (HeaderWriterReceipt ar dir pp lp owner decl group pins frame₀ (pub u) lib scan.val.2.1 scan.val.2.2) := by
  intro label decl mass group owner
  have same : profile (a u).1=ret := by
    obtain ⟨v,hv⟩ := profile.surjective ret
    have tape := spelling v
    rw [hv] at tape
    exact (List.ofFn_injective (tape.symm.trans digits)) ▸ hv
  have directory : Runs (pub u) lib (.seq PrivatePlacement.program Directory.ISA.program)
      (profile (a u).1).val.2.1 (profile (a u).1).val.2.2 scan.val.1 scan.val.2.1 pubMem := by
    rw [same,←stored]
    exact scan.property
  have boot := (B u).boot
  rw [siteLibrary_installed SparseExterior.driver n] at boot
  rw [stored] at placed
  obtain ⟨_,_,_,_,placement⟩ := placed
  have permitted := prepared_allowed frame₀ boot (B u).stable (B u).positive (B u).pins (fun v => ((B u).outputs v).1)
    profile spelling writer old fresh gates outputs bitWidth off ell controls word claims pad raw R X input
    id (a u).1 (a u).2 directory N tile recv sizes placement hd
  refine ⟨same,permitted.1,permitted.2,?_⟩
  exact ⟨SignedPrep.geometricHeaderReceipt (mac:=lib) (reg:=scan.val.2.1) writer frame₀ old fresh gates outputs
    bitWidth off ell controls word claims pad raw input N tile recv sizes placement permitted.1 permitted.2
    writer.placement (fun _ => rfl) scan.val.2.2 stored⟩

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
