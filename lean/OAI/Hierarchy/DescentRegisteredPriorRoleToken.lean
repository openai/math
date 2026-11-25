import OAI.Hierarchy.DescentDatePortArchiveRead
import OAI.Hierarchy.DescentArchiveRoleExtension
import OAI.Hierarchy.DescentOrdinaryMountedBirth

namespace OAI
/-! The prior tokens mounted by the ordinary registered W input keep their original
group and node ordinals at an actual donor. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}


open DescentOrdinaryHostPad
local notation "slot" => slotAt ports r B number room
local notation "tok" => token G s Z op
local notation "bits_" => printedBits G s Z op

/-- The original group number survives the split into successor group and block. -/
theorem ordinary_source_number (ageOk : age<S.length) (radix : S.radix=2^k) (j : Fin (S.groupCount age)) :
    (finProdFinEquiv (S.groupDigits ageOk radix j)).val=j.val:=by
  change (finProdFinEquiv (finProdFinEquiv.symm _)).val=j.val
  rw [Equiv.apply_symm_apply]
  rfl

/-- This is the actual old-input expression in `captured_role_stock`. The three
casts account for the fixed receiving host count, group reshape, and published width. -/
theorem registered_prior_token {H HH C : ℕ} (count : HH=H)
    (ageOk : age<S.length) (radix : S.radix=2^k)
    (groups : S.groupCount (age+1)*2^k=ports.venue.groups)
    (field : C=bits_*ports.nodes)
    (name : r.V↪Fin HH) (faith : ∀v,(name v).val=(r.vertex v).val)
    (v : W.graph.Site) (n : (B.recipe v).Node) (node : Fin ports.nodes) (ordinal : node.val=(number v n).val) :
    let x:=(r.placement.block v).cast (congrArg (2^·) room.radix)
    let src:=fun h g=>encode bits_ ports.nodes (fun t=>(slot x t h g).elim 0 (fun a=>tok (label a)))
    let mounted:=PhysicalOrdinary.ArgumentEntry.rowsAt count groups field.symm (extend H src)
    (encode bits_ ports.nodes).symm
      (Fin.cast (congrArg (fun a : ℕ=>2^a) field) (mounted (name (r.placement.pos v).2)
        (finProdFinEquiv (S.groupDigits ageOk radix (r.placement.pos v).1)))) node = tok (label ⟨v,n⟩):=by
  subst C
  subst HH
  intro x src mounted
  have same : (finProdFinEquiv (S.groupDigits ageOk radix (r.placement.pos v).1)).cast groups=
      ((r.placement.pos v).1.cast room.groups):=Fin.ext (ordinary_source_number ageOk radix _)
  simpa only [mounted,PhysicalOrdinary.ArgumentEntry.rowsAt,Fin.cast_refl,id_eq,src,same,x] using
    (extended_role_node (label:=label) (room:=room) name faith v n node ordinal)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
