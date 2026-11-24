import OAI.Computability.VPVNP.CompressorSelectedDirectoryHistory
import OAI.Computability.VPVNP.CompressorBlockMetadataPackets

/-!
# Native metadata publications for selected directory histories

The preimage worker supplies the arrays in the incoming memory. The
metadata worker leaves these arrays intact and installs the five directory
operands and the next state's DFS header. Later term-head publishers can
extend the emission by preserving precisely those cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedDirectoryHistory

open BurstRAM Compression DescriptorSpace PairSimulation.TraversalRows
open BlockPlanner PhaseRecipe Schedule
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f} {v : SelectedLevel B f hf}
variable {L : Layout} {i : ℕ} {m m₀ out out' : Memory w}

/-- The five packet fields read by the traversal controller, in the
metadata writer's twelve-word order. -/
def PlacementWords (values : Fin 12 → Word w) (pub : Fin 6 → Word w) : Prop :=
  values 6 = pub 0 ∧ values 7 = pub 2 ∧ values 9 = pub 3 ∧ values 10 = pub 5 ∧ values 11 = pub 4

/-- Recover the pre-pass input after preliminary work on placement and incidence
arrays which leaves the DFS base and role of the active state intact. -/
noncomputable def Emission.prepend (e : Emission L i v m out)
    (base : m (levelStart L i+14) = m₀ (levelStart L i+14))
    (role : m (levelStart L i+27) = m₀ (levelStart L i+27)) : Emission L i v m₀ out :=
  { e with
    keepBase := e.keepBase.trans base
    keepRole := e.keepRole.trans role
    nextBase := by rw [e.nextBase,base] }

/-- Term pointers and scheduler writes can follow the packet in the same
pass. They only need to frame its placement arrays and these header offsets. -/
noncomputable def Emission.transfer (e : Emission L i v m out)
    (arrays : SourceTransport.Agree (Directory.cells e.dir.pub) out out')
    (active : ∀ o ∈ [14,21,22,24,25,26,27], out' (levelStart L i+o) = out (levelStart L i+o))
    (successor : ∀ o ∈ [14,27], out' (levelStart L (i+1)+o) = out (levelStart L (i+1)+o)) :
    Emission L i v m out' := by
  exact ⟨e.dir.transport arrays,e.lower,(active 14 (by decide)).trans e.keepBase,
    (active 27 (by decide)).trans e.keepRole,(successor 14 (by decide)).trans e.nextBase,
    (successor 27 (by decide)).trans e.nextRole,(active 21 (by decide)).trans e.old,
    (active 22 (by decide)).trans e.directory.1,(active 24 (by decide)).trans e.directory.2.1,
    (active 25 (by decide)).trans e.directory.2.2.1,(active 26 (by decide)).trans e.directory.2.2.2⟩

@[simp] theorem Emission.prepend_pub (e : Emission L i v m out) (base role) :
    (e.prepend (m₀ := m₀) base role).dir.pub = e.dir.pub := rfl

@[simp] theorem Emission.transfer_pub (e : Emission L i v m out) (arrays active successor) :
    (e.transfer (out' := out') arrays active successor).dir.pub = e.dir.pub := rfl

variable {workspace : Word w} {positions blocks t step : ℕ} {fields : BlockMetadata.Fields}
variable {rs : List (Report w)}
local notation "plan" => BlockProgram.script B
local notation "layout" => BlockProgram.layout B workspace.val positions blocks
local notation "first" => Script.levelsPerBlock plan*t
local notation "cur" => first+step
local notation "head" => levelStart layout cur
local notation "next" => levelStart layout (cur+1)
local notation "pub" => Ports.data (Workspace.ports (arity (Script.catalog plan)) workspace)
local notation "state" => (levelStart layout first : Word w)

/-- The native writer evaluates the field bank in the metadata input memory
and publishes all five traversal operands with their exact word values. -/
theorem placement_words {bank : Fin 6 → Word w} {oldSites : ℕ} {role : BlockMetadata.Role}
    (p : BlockMetadata.Published B workspace positions blocks t step role fields m oldSites rs)
    (values : PlacementWords (fun j =>
      (BlockMetadata.fieldExprs (layout).shape step B.recordLimit (slotDegree S) fields j).eval pub state m) bank) :
    PlacementWords (fun j => after m (eventLog rs) (head+15+j.val)) bank := by
  obtain ⟨a,b,c,d,e⟩ := values
  exact ⟨(p.payload 6).trans a,(p.payload 7).trans b,(p.payload 9).trans c,
    (p.payload 10).trans d,(p.payload 11).trans e⟩

/-- Construct the pass emission from the actual three metadata visits and
the completed native preimage rows. The owner column starts past the scalar
packet, and the entire directory ends before the successor header. -/
noncomputable def Emission.ofPublished
    (p : BlockMetadata.Published B workspace positions blocks t step (BlockMetadata.producingRole v.origin)
      fields m v.input.positions rs)
    (d : LevelDirectory v m next) (lower : head+28 ≤ (d.pub 1).val)
    (values : PlacementWords (fun j => after m (eventLog rs) (head+15+j.val)) d.pub) :
    Emission layout cur v m (after m (eventLog rs)) := by
  have stepEq : first+(step+1) = cur+1 := Nat.add_assoc .. |>.symm
  have wide : 28 ≤ levelWords layout := by
    change 28 ≤ 54+6+6+6*slotCapacity layout+6*tableWords layout
    omega
  have span : head+28 ≤ next := by
    have advance (j : ℕ) : levelStart layout (j+1) = levelStart layout j+levelWords layout := by
      simp only [levelStart,Nat.succ_mul,Nat.add_assoc]
    rw [advance]
    exact Nat.add_le_add_left wide head
  have arrays : SourceTransport.Agree (Directory.cells d.pub) m (after m (eventLog rs)) := by
    intro x hx
    obtain ⟨lo,hi⟩ := Directory.cells_interval d hx
    exact (p.outside x (by omega) (by rw [stepEq]; omega) (by rw [stepEq]; omega)).symm
  have keep (o : ℕ) (ho : o = 14 ∨ o = 27) : after m (eventLog rs) (head+o) = m (head+o) := by
    apply p.outside <;> first | omega | rw [stepEq]; omega
  have low : levelsBase layout ≤ head := Nat.le_add_right ..
  exact ⟨d.transport arrays,show levelsBase layout ≤ (d.pub 1).val by omega,keep 14 (Or.inl rfl),keep 27 (Or.inr rfl),
    stepEq ▸ p.successor,stepEq ▸ p.tag,values.1,values.2.1,values.2.2.1,values.2.2.2.1,values.2.2.2.2⟩

@[simp] theorem Emission.ofPublished_pub
    (p : BlockMetadata.Published B workspace positions blocks t step (BlockMetadata.producingRole v.origin)
      fields m v.input.positions rs)
    (d : LevelDirectory v m next) (lower values) :
    (Emission.ofPublished p d lower values).dir.pub = d.pub := rfl

end CompressorRecords.SelectedDirectoryHistory

end VPVNP
end Computability
end OAI
