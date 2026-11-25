import OAI.Hierarchy.DescentResetPrimitiveCheckpoint
import OAI.Hierarchy.DescentResetAtlasMenu
import OAI.Hierarchy.DescentPrimitiveBirthCases

namespace OAI
/-! # The global reached primitive at each genuinely occupied compact node -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open DescentSIMDLookup DescentPackedResetRotorRoles DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail p : ℕ}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (menu : Runnable F op) (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit)
    (fixed : Chronology.resetSpec b=op) (a : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) a.bit)
local notation "next" => (Chronology.resetArchive b p hp whole a).bit
local notation "enc" => Encoding.reset op menu b hp whole fixed a old
local notation "gate" => reachedInput G s Z op menu b hp whole a old

theorem code_fit (bits : ℕ) (width : roleBits b.reset.n≤bits) (x : Option (NodeOrder.All next)) :
    DescentResetPrimitivePage.localRole (x.elim .padding gate)<2^bits:=by
  cases x with
  | none=>exact Nat.two_pow_pos _
  | some x=>
    change DescentResetPrimitivePage.localRole (Sum.elim _ (Sum.elim _ _) (resetOrigin b hp whole a x))<_
    rcases resetOrigin b hp whole a x with u|e|⟨v,j⟩
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact (DescentDatedAddressBook.PhysicalReset.Atlas.roleCode b.reset.n _).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)

/-- A rectangular cursor may be empty in either axis, including at the final
unused compact host. The dictionary key of every occupied archived node is
read from the actual mounting of the predecessor, relay and device operands. -/
theorem issued_reached {w : ℕ} (v : DescentResetPrimitiveCheckpoint.Shape) (base : ℕ) (src : v.Inputs)
    (m : Memory w) (safe : v.Fits base src w) (room : v.endAddress base<2^w)
    (bitsEq : v.chart.bits=printedBits G s Z op) (width : roleBits b.reset.n≤v.rawBits)
    (row : Fin v.chart.blocks→Fin v.chart.nodes→Fin v.chart.hosts→Fin v.chart.groups→Option (NodeOrder.All next))
    (oldSource : ∀x n,Source (src.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord ((row x n h g).elim .padding gate)) v.chart.lanes m)
    (newSource : ∀x n,Source (src.fresh x n) (fun h g=>(DescentResetPrimitivePage.localRole ((row x n h g).elim .padding gate):Cell v.rawBits)) v.chart.lanes m)
    (relaySource : ∀x n,Source (src.relay x n) (fun h g=>DescentResetPrimitivePage.relayFlag ((row x n h g).elim .padding gate)) v.chart.lanes m)
    (x : Fin v.chart.blocks) :
    Reads (v.bank base x) (fun h g=>encode v.chart.bits v.chart.nodes fun j=>
      ((row x j h g).elim 0 (fun picked=>((codec (G:=G) op).store ((enc).atNode picked)).val+1):Cell v.chart.bits))
      v.chart.lanes (v.finalMem G s Z op base src m):=by
  let records (x : Fin v.chart.blocks) (j : Fin v.chart.nodes) (h : Fin v.chart.hosts) (g : Fin v.chart.groups) :=
    (row x j h g).elim (.padding : PrintedInput (printedBits G s Z op)) gate
  have out:=v.issued G s Z op base src m safe room bitsEq records
    (fun block node host group=>code_fit G s Z op menu b hp whole a old _ width (row block node host group))
    oldSource newSource relaySource x
  have castWord (picked : Option (NodeOrder.All next)) :
      ((picked.elim 0 (fun n=>((codec (G:=G) op).store ((enc).atNode n)).val+1) : ℕ) : Cell v.chart.bits) =
        picked.elim 0 (fun n=>(((codec (G:=G) op).store ((enc).atNode n)).val : Cell v.chart.bits) + 1) := by
    cases picked <;> simp
  simpa only [records,published_word G s Z op menu b hp whole fixed a old,castWord] using out

end
end Hierarchy.DescentPrimitivePalette

end OAI
