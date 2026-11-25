import OAI.Computability.BorderVNP.RoutingISATypedTaskPackets
import OAI.Computability.BorderVNP.CellPacketSupplementalTyped
import OAI.Computability.BorderVNP.CellPacketSourceSize

/-! # Owned task rows for the actual sidecar-augmented private directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM CellSparse CellPacket CompactMachine

variable {Site : Type} (l : Layout) (mem : ℕ → ℕ) (p : ℕ → Placed Site)
variable (supp : ℕ → Supplement.Layout) (geom : ℕ → ℕ) (extra : ℕ → List Record)

/-- The actual typed task, after the four reserved descriptors have been patched. -/
noncomputable def augmented (j : ℕ) : TypedBatch.Task :=
  let c := globalCell l mem j
  ⟨Supplement.task (supp c) (l.atCell mem p c) (geom c) (extra c),l.call c⟩

/-- The private macro input includes exactly the genuine supplemental row list. -/
def augmentedInput (c : ℕ) : CellInput :=
  let q := l.atCell mem p c
  ⟨{q.directory with records := q.rows++extra c},q.privateWires,q.external⟩

private theorem supplemented_length (q : Placed Site) (a : Supplement.Layout) (g : ℕ) (xs : List Record) :
    (Supplement.task a q g xs).chunks.length=q.parts.length+3 := by
  simp only [Supplement.task,List.length_append,Supplement.prefixChunks,Packet.Source.chunks_length,
    Supplement.prefixParts,Supplement.tailChunks,List.length_cons,List.length_map,List.length_nil,Placed.parts,
    Packet.Source.plan,List.length_append]

/-- The actual native seven-word task already has the right descriptor range for
the patched packet. The reserve is three descriptors beyond the ordinary plan. -/
theorem augmented_stored {w : ℕ} (room : l.Room mem w) (after : Memory w) (hout : readings after=l.published mem)
    {j : ℕ} (hj : j < l.before mem l.cells) :
    let c := globalCell l mem j
    mem (l.sorted+l.padded+c) < mem (l.sorted+l.padded+(l.stops+c)) →
    mem (l.sorted+l.padded+(l.stops+c))-mem (l.sorted+l.padded+c)-1 = 3*((p c).parts.length+3) →
    mem (l.offsets+2*l.cables+c)+mem (l.tails+c)=(p c).external.length →
    (augmented l mem p supp geom extra j).Stored after l.tasks j := by
  intro c ord len ext
  apply stored_parameters l mem room after hout hj
  have end' : l.sorted+mem (l.sorted+l.padded+(l.stops+c)) =
      l.sorted+mem (l.sorted+l.padded+c)+1+3*((p c).parts.length+3) := by omega
  change l.row mem c=parameters ⟨Supplement.task (supp c) (l.atCell mem p c) (geom c) (extra c),l.call c⟩
  simp only [Layout.row,parameters,end',ext]
  rw [supplemented_length]
  rfl

/-- After the genuine prepass each owned global call points to the packet for its
augmented directory. Argument shape and its equality with the typed generator input
come from the physical supplemental chunk construction. -/
theorem augmented_placedRows {w n : ℕ} (pub : Arg → Word w) (after : Memory w)
    (hf : CellDispatch.Frame.ofMemory pub after=⟨l.team,l.calls,l.cells⟩)
    (owners : ∀ c < l.cells, readings after (l.call c)=l.owner mem c)
    (cap : ∀ j < l.before mem l.cells, ((augmented l mem p supp geom extra j).cell.burst w).length ≤ TeamScales.width n (1/2)) :
    TypedBatch.PlacedRows pub after (augmented l mem p supp geom extra) (l.before mem l.cells) n
      (augmentedInput l mem p extra) := by
  refine ⟨?_,cap⟩
  rw [hf]
  intro c hc own
  have ha : (CellDispatch.Frame.mk l.team l.calls l.cells).address c=l.call c := by
    simp [CellDispatch.Frame.address,Layout.call,Nat.add_comm,Nat.mul_comm]
  change readings after ((CellDispatch.Frame.mk l.team l.calls l.cells).address c)=l.team at own
  rw [ha,owners c hc] at own
  refine ⟨l.before mem c,l.before_strict mem hc own,?_⟩
  simp only [augmented,global_at l mem hc own,ha,true_and,augmentedInput]
  exact Supplement.payload_eq (supp c) _ (geom c) (extra c)

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
