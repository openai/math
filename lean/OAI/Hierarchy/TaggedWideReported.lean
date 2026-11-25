import OAI.Hierarchy.TaggedWideStack
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Closing the physical shorter board on the native controller's link records -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ThreeFlat Routing Spill CallPool
open TaggedShorterCompaction TaggedShorterNetwork ProtocolStackContraction
open ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {F : Type*} [CommSemiring F] {n groups D half address modules : ℕ}
    {w scale γ : ℕ} {fraction parentRows : ℝ}

/-- Allocate actual reported rows by their dyadic width and their emitted group.
Both roles use prefix addresses of their own physical endpoint order. They
share the ordinal of the link ID and of the piece within its original word. -/
def ofReported (rows : Fin n → ProtocolRAMEmit.Row)
    (distinct : Function.Injective fun i => (rows i).link)
    (capacityFit : ∀ g : Fin groups,count rows w scale γ g.val≤D)
    (volume : ((∑ g : Fin groups,count rows w scale γ g.val : ℕ):ℝ) ≤ fraction*parentRows)
    (pad : (groups:ℝ)*(2*half:ℕ)≤fraction*parentRows) (halfPos : 0<half)
    (twice : 2^address=2*half) (purchase : modules=⌈6*fraction*parentRows/(2*half:ℕ)⌉₊)
    (near : Compactor F D (2^address) (address+⌈TaggedShorterBudget.dyadic γ*w⌉₊))
    (far : Compactor F (TaggedShorterGroups.capacity (Fin groups) D half modules) modules
      (Width (2^address) (address+⌈TaggedShorterBudget.dyadic γ*w⌉₊)))
    (metadata : 1+address+address≤⌈TaggedShorterBudget.dyadic γ*w⌉₊) : Board F where
  Group := Fin groups
  D := D
  halfBatch := half
  address := address
  width := ⌈TaggedShorterBudget.dyadic γ*w⌉₊
  modules := modules
  fraction := fraction
  parentRows := parentRows
  counts := fun g => count rows w scale γ g.val
  positive := halfPos
  batch := twice
  bound := capacityFit
  active := volume
  padding := by simpa using pad
  purchased := purchase
  near := near
  far := far
  fits := metadata
  place := fun g => ProtocolRAMReportedPorts.place rows w scale γ g.val distinct (capacityFit g)

/-- The common ID may be computed in the current active-link order, while
the two data locations always refer to their hardwired incident ports.
Only the short mask and ID need to be scattered. -/
def ofStaticReported {ports lanes : ℕ} (rows : Fin n → ProtocolRAMEmit.Row)
    (distinct : Function.Injective fun i => (rows i).link)
    (volume : ((∑ g : Fin groups,count rows w scale γ g.val : ℕ):ℝ) ≤ fraction*parentRows)
    (pad : (groups:ℝ)*(2*half:ℕ)≤fraction*parentRows) (halfPos : 0<half)
    (twice : 2^address=2*half) (purchase : modules=⌈6*fraction*parentRows/(2*half:ℕ)⌉₊)
    (near : Compactor F D (2^address) (address+⌈TaggedShorterBudget.dyadic γ*w⌉₊))
    (far : Compactor F (TaggedShorterGroups.capacity (Fin groups) D half modules) modules
      (Width (2^address) (address+⌈TaggedShorterBudget.dyadic γ*w⌉₊)))
    (metadata : 1+address+address≤⌈TaggedShorterBudget.dyadic γ*w⌉₊)
    (port : Bool → Fin n → Fin ports)
    (portsInj : ∀ (g : Fin groups) b,PortDistinct rows w scale γ g.val (port b))
    (room : ∀ i,pieces rows w i≤lanes) (fit : ports*lanes≤D) : Board F :=
  { ofReported rows distinct (fun g=>static_capacity rows distinct g port (portsInj g) room fit) volume pad halfPos twice purchase near far metadata with
      place := fun g b => (common rows w scale γ g.val distinct).symm.toEmbedding.trans
        (staticUnit rows g port (portsInj g) room fit b) }

/-- When the payload comes from the actual site's two words for each row,
the linked port predicate equals full word equality on every reported record
of this dyadic type. Zero-width rows are allowed. -/
theorem reported_linked_iff (rows : Fin n → ProtocolRAMEmit.Row) (hw : 0<w)
    (distinct : Function.Injective fun i => (rows i).link)
    (capacityFit : ∀ g : Fin groups,count rows w scale γ g.val≤D)
    (words : ∀ i : Fin n,Bool → Fin (rows i).width → Bool)
    (x : Slot (Fin groups) D → Bits ⌈TaggedShorterBudget.dyadic γ*w⌉₊)
    (load : ∀ (g : Fin groups) (side : Bool) (i : InGroup rows w scale γ g.val)
      (j : Fin (pieces rows w i.val)),
      x (some g,side,ProtocolRAMReportedPorts.place rows w scale γ g.val distinct (capacityFit g) side
        (common rows w scale γ g.val distinct ⟨i,j⟩)) =
      TaggedShorterFields.slice ⌈TaggedShorterBudget.dyadic γ*w⌉₊ (words i.val side) j.val) :
    Linked (fun g : Fin groups => ProtocolRAMReportedPorts.place rows w scale γ g.val distinct
      (capacityFit g)) x ↔
      ∀ (g : Fin groups) (i : InGroup rows w scale γ g.val), words i.val true=words i.val false := by
  constructor
  · intro eqn g i
    apply (equality_of_units rows scale γ g.val hw i (words i.val true) (words i.val false)).mp
    intro j
    simpa only [load] using eqn g (common rows w scale γ g.val distinct ⟨i,j⟩)
  · intro eqn g t
    obtain ⟨⟨i,j⟩,rfl⟩ := (common rows w scale γ g.val distinct).surjective t
    exact (load g true i j).trans ((congrArg (fun z=>TaggedShorterFields.slice _ z j.val) (eqn g i)).trans
      (load g false i j).symm)

/-- With fixed site ports, loading a data lane reads just its site's own
word. Complete link equality follows without moving payload on the
native endpoint sort or depending on the number of earlier active ports. -/
theorem static_linked_iff {ports lanes : ℕ} (rows : Fin n → ProtocolRAMEmit.Row) (hw : 0<w)
    (distinct : Function.Injective fun i => (rows i).link) (port : Bool → Fin n → Fin ports)
    (portsInj : ∀ (g : Fin groups) b,PortDistinct rows w scale γ g.val (port b))
    (room : ∀ i,pieces rows w i≤lanes) (fit : ports*lanes≤D)
    (words : ∀ i : Fin n,Bool → Fin (rows i).width → Bool)
    (x : Slot (Fin groups) D → Bits ⌈TaggedShorterBudget.dyadic γ*w⌉₊)
    (load : ∀ (g : Fin groups) (side : Bool) (i : InGroup rows w scale γ g.val)
      (j : Fin (pieces rows w i.val)),
      x (some g,side,fixedSlot fit (port side i.val,Fin.castLE (room i.val) j)) =
      TaggedShorterFields.slice ⌈TaggedShorterBudget.dyadic γ*w⌉₊ (words i.val side) j.val) :
    Linked (fun (g : Fin groups) b => (common rows w scale γ g.val distinct).symm.toEmbedding.trans
      (staticUnit rows g port (portsInj g) room fit b)) x ↔
      ∀ (g : Fin groups) (i : InGroup rows w scale γ g.val), words i.val true=words i.val false := by
  constructor
  · intro eqn g i
    apply (equality_of_units rows scale γ g.val hw i (words i.val true) (words i.val false)).mp
    intro j
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply,
      read_staticUnit,load] using eqn g (common rows w scale γ g.val distinct ⟨i,j⟩)
  · intro eqn g t
    obtain ⟨⟨i,j⟩,rfl⟩ := (common rows w scale γ g.val distinct).surjective t
    simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
    exact (load g true i j).trans ((congrArg (fun z=>TaggedShorterFields.slice _ z j.val) (eqn g i)).trans
      (load g false i j).symm)

end Hierarchy.Tagged.WideStack

end
end OAI
