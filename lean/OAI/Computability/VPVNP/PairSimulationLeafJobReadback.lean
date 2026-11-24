import OAI.Computability.VPVNP.PairSimulationLeafPhysicalInput
import OAI.Computability.VPVNP.PairSimulationLeafReadback
import OAI.Computability.VPVNP.PairSimulationNominationAssembly

/-!
# Exact acceptance at the cursor leaves of the selected compression tree

The numerical row address and private four-port buffer identify the leaf
reader used in the compressor state. A successful DFS visit consumes its
selected occurrence's word and returns the entire suffix. Conversely every
successful visit comes from that site's occurrence type.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafHandler

open BurstRAM PrivateRAM CursorRouting CursorNetwork RAMLayout Compression DFS
open LocalHistory TraversalRows NodeArguments NetworkKernel CompressorRecords
open scoped Fin.CommRing

universe u

private theorem castReader_suffix {α β : Type u} (h : α = β) (reader : ChoiceReader α)
    (bits : List Bool) : (((h ▸ reader) : ChoiceReader β).read bits).map Prod.snd =
      (reader.read bits).map Prod.snd := by
  subst β
  rfl

/-- Transporting an occurrence to its compressor site only changes the
dependent result type. The unread suffix is identical. -/
theorem pushLeafReaders_suffix {N Y : Network} (I : N.Iso Y) (P : Factors Type N)
    (read : ∀ u h, ChoiceReader (P u h)) (v : N.Site) (z : Y.Half (I.site v))
    (bits : List Bool) :
    ((pushLeafReaders I P read (I.site v) z).read bits).map Prod.snd =
      ((read v (I.pullHalf v z)).read bits).map Prod.snd := by
  rw [pushLeafReaders, Equiv.piCongrLeft_apply_apply]
  exact castReader_suffix _ _ _

variable {b l a p e w W endAddr : ℕ} [NeZero (b+l)] (hD : 1 < b+l) (hd : 2+p = 2^a)
    {L : PrimedInputRAM.Lengths} {n ai H s : ℕ} {Q : PrimedInputRAM.Layout L n ai H w}
    (D : PrimedCounter.Data Q s) (hw : 2 ≤ w) (hc : 2^(b+l)*2^e < 2^w)
    {R : Type*} [CommRing R] {Label : Type} [Fintype Label] (f : Label → R)
    (clock : ℕ) (bound : NominationClock D hw hc clock)
    (storage : StackMachine.Layout (LeafStartup.Port 52 34) W)
    (pub : LeafAddress.Field → Word W) (arena : Arena)
    (trace : Word W → Scratch W endAddr → List (Event W))
    (prepared : Word W → Scratch W endAddr → Scratch W endAddr)
    (node : Word W) (saved : Scratch W endAddr) (cap : ℕ) (v : Position (b+l))
    (z : (LeafArguments.state hD hd (2^e) w).network.Half (lanePositions (cursorCoordinateLabels b l) v))

/-- The numerical row header and pending packet supplied to an actual leaf. -/
structure StoredCursorRow : Prop where
  width : b+l ≤ W
  stride : (pub .stride).val = cap+2
  radixB : (pub .radixB).val = 2^b
  radixL : (pub .radixL).val = 2^l
  address : node.val = (sitePointers cap (pub .base).val (siteOrder (LeafArguments.state hD hd (2^e) w))
    (lanePositions (cursorCoordinateLabels b l) v)).1
  fit : (cursorPacket hD hd node.val v z).Fits arena W endAddr
  stored : (cursorPacket hD hd node.val v z).Stored arena saved

variable (row : StoredCursorRow hD hd pub arena node saved cap v z)

/-- The native leaf parser specialized to a node and four half-wire buffers decoded from the
physical row and private argument arena. -/
noncomputable abbrev cursorHook :=
  parser D hw hc storage (physicalInput (b+l) e w pub arena trace prepared) clock

/-- The selected nomination reader at the cursor site, specialized to its supplied half-wire
assignment. -/
noncomputable abbrev cursorSiteReader :=
  (nominationSites D hw hc (cursorCoordinateLabels b l) hD hd f clock bound).read
    (lanePositions (cursorCoordinateLabels b l) v) z

include row in
/-- This is the compressed occurrence reader on the genuine, ordered
cursor state, evaluated on precisely the word stream seen by the physical hook. -/
theorem cursorHook_suffix (bits : List Bool) :
    ((cursorHook D hw hc clock storage pub arena trace prepared).read node saved bits).map Prod.snd =
      ((cursorSiteReader hD hd D hw hc f clock bound v z).read bits).map Prod.snd := by
  let I := LeafArguments.iso hD hd (2^e) w
  let old := unpadHalf p v (I.pullHalf v z)
  let input := physicalInput (b+l) e w pub arena trace prepared
  have correct := physicalInput_correct hD hd pub arena trace prepared node saved cap v z
    row.width row.stride row.radixB row.radixL row.address row.fit row.stored
  have suffix := parser_nomination D hw hc storage input clock node saved bits v old
    (congrArg Input.pos correct) (congrArg Input.buffers correct) (bound v old)
  let P : Factors Type (paddedNetwork (b+l) p (ramFieldBits (2^e) w : RAMSystem (b+l) → ℕ)) :=
    fun u y => initialChoices D.machine D.fuel 0 D.initial hw hc u (unpadHalf p u y)
  exact suffix.trans (pushLeafReaders_suffix I P (fun u y =>
    LeafStartup.nominationReader D hw hc u (unpadHalf p u y) clock (bound _ _)) v z bits).symm

private theorem read_exists {α β : Type*} {native : Option (β × List Bool)} (reader : ChoiceReader α)
    (bits tail : List Bool) (h : native.map Prod.snd = (reader.read bits).map Prod.snd) :
    (∃ job, native = some (job,tail)) ↔ ∃ x, bits = reader.encode x ++ tail := by
  constructor
  · rintro ⟨job, hj⟩
    rw [hj,Option.map_some] at h
    obtain ⟨⟨x, suffix⟩, read, rfl⟩ := Option.map_eq_some_iff.mp h.symm
    exact ⟨x, (reader.read_iff bits x suffix).mp read⟩
  · rintro ⟨x, hx⟩
    rw [(reader.read_iff bits x tail).mpr hx,Option.map_some] at h
    obtain ⟨⟨job,suffix⟩, read, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨job,read⟩

include row in
/-- On arbitrary private bits, a hook path with this exact unread suffix
exists precisely when the selected site's reader has the corresponding prefix. -/
theorem cursorHook_read_iff (bits tail : List Bool) :
    (∃ job, (cursorHook D hw hc clock storage pub arena trace prepared).read node saved bits =
      some (job,tail)) ↔ ∃ x, bits = (cursorSiteReader hD hd D hw hc f clock bound v z).encode x ++ tail :=
  read_exists _ bits tail (cursorHook_suffix hD hd D hw hc f clock bound storage pub arena trace
    prepared node saved cap v z row bits)

include row in
/-- In the one-node leaf preorder the successful native hook and the
semantic leaf occurrence consume exactly the same private prefix. -/
theorem cursorHook_preorder_iff (bits tail : List Bool) :
    (∃ out, (cursorHook D hw hc clock storage pub arena trace prepared).decode [node] saved bits =
      some (out,tail)) ↔ ∃ x, bits = (cursorSiteReader hD hd D hw hc f clock bound v z).encode x ++ tail := by
  rw [← cursorHook_read_iff hD hd D hw hc f clock bound storage pub arena trace prepared node saved
    cap v z row]
  let hook := cursorHook D hw hc clock storage pub arena trace prepared
  change (∃ out, hook.decode [node] saved bits = some (out,tail)) ↔ ∃ job, hook.read node saved bits = some (job,tail)
  cases hr : hook.read node saved bits with
  | none => simp [HookParser.decode, hr]
  | some pair =>
    obtain ⟨job,suffix⟩ := pair
    simp [HookParser.decode, hr]

end PairSimulation.LeafHandler

end VPVNP
end Computability
end OAI
