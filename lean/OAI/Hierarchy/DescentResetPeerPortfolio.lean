import OAI.Hierarchy.DescentResetPeerAxes

namespace OAI
/-! # Combining the four measured reset cable families into the issued peer directory -/
namespace Hierarchy.DescentResetPeerUnionRAM.Axes
noncomputable section
open scoped Classical
variable {s c p : ℕ} {α : Type*}

/-- Existence of a tagged measurement is invariant under the public mixed-radix enumeration.
The two contact coordinates are its reserved socket and its previous signed donor. -/
theorem family_search (f : Fields s c p α) (hit : α→Prop) (tag : Fin 4) :
    (∃i,kind s c p i=tag ∧ hit (f.all i)) ↔
      (0=tag ∧ ∃j,hit (f.stem j)) ∨ (1=tag ∧ hit f.trunk) ∨
      (2=tag ∧ ∃j l,hit (f.contact j l)) ∨ (3=tag ∧ ∃j,hit (f.privateEdge j)) := by
  let tags : Fields s c p (Fin 4) := ⟨fun _=>0,1,fun _ _=>2,fun _=>3⟩
  constructor
  · rintro ⟨i,tagged,found⟩
    obtain ⟨j,rfl⟩:=(order s c p).surjective i
    change tags.all (order s c p j)=tag at tagged
    rw [Fields.all_at] at tagged found
    rcases j with j | (j | (⟨u,l⟩ | j))
    · exact .inl ⟨tagged,j,found⟩
    · exact .inr (.inl ⟨tagged,found⟩)
    · exact .inr (.inr (.inl ⟨tagged,u,l,found⟩))
    · exact .inr (.inr (.inr ⟨tagged,j,found⟩))
  · have inject (j : Index s c p) (label : tags.atIndex j=tag) (found : hit (f.atIndex j)) :
        ∃i,kind s c p i=tag ∧ hit (f.all i) := by
      refine ⟨order s c p j,?_,?_⟩
      · exact (tags.all_at j).trans label
      · rwa [Fields.all_at]
    rintro (⟨ht,j,v⟩|⟨ht,v⟩|⟨ht,j,l,v⟩|⟨ht,j,v⟩)
    · exact inject (.inl j) ht v
    · exact inject (.inr (.inl 0)) ht v
    · exact inject (.inr (.inr (.inl (j,l)))) ht v
    · exact inject (.inr (.inr (.inr j))) ht v

/-- Four separately measured native operands have the same row semantics after enumeration. -/
theorem tabulate {β : Type*} (f : Fields s c p α) (g : Fields s c p β) (P : α→β→Prop)
    (stem : ∀j,P (f.stem j) (g.stem j)) (trunk : P f.trunk g.trunk)
    (contact : ∀j l,P (f.contact j l) (g.contact j l))
    (privateEdge : ∀j,P (f.privateEdge j) (g.privateEdge j)) :
    ∀i,P (f.all i) (g.all i) := by
  intro i
  obtain ⟨j,rfl⟩:=(order s c p).surjective i
  rw [Fields.all_at,Fields.all_at]
  rcases j with j | (j | (⟨u,l⟩ | j))
  · exact stem j
  · exact trunk
  · exact contact u l
  · exact privateEdge j

end
end Hierarchy.DescentResetPeerUnionRAM.Axes

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentStageEdgeReceipt DescentSortedRoster
open DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
variable {H D₀ J b M w : ℕ}
local notation "pitch" => H*shelf
local notation "Family" => Axes.Fields (stemsCount B) (contactCount B) (privateCount B)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

/-- A single source bank may fire in any genuine high-group lane. A matching candidate slot
names a raw successor host through the same original old-neighbor array used by the CPU. -/
def rowHit (peers : Fin H→Fin D₀→Option (Fin H)) (v x : Fin pitch)
    (one : Fin pitch→Fin J→Cell b) : Prop :=
  ∃(g₀ : Fin J) (j : Fin (Candidates.count shelf D₀)),Candidates.candidate peers v j=some x ∧ (one v g₀).val=j.val+1

theorem family_receipt (previous : Fintype.card input.V ≤ H) (peers : Fin H→Fin D₀→Option (Fin H))
    (words : Family (Fin pitch→Fin J→Cell b))
    (stem : ∀(v : B.next.V) (x : Fin pitch),
      let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
      (∃l,rowHit B peers a x (words.stem l)) ↔ ∃t,rawPeer B (stemParent B t) a.val x.val)
    (trunk : ∀(v : B.next.V) (x : Fin pitch),
      let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
      rowHit B peers a x words.trunk ↔ ∃t,rawPeer B (trunkParent B t) a.val x.val)
    (contact : ∀(v : B.next.V) (x : Fin pitch),
      let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
      (∃l d₀,rowHit B peers a x (words.contact l d₀)) ↔ ∃t,rawPeer B (contactParent B t) a.val x.val)
    (privateEdge : ∀(v : B.next.V) (x : Fin pitch),
      let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
      (∃l,rowHit B peers a x (words.privateEdge l)) ↔ ∃t,rawPeer B (privateWire B t) a.val x.val) :
    IssuedTickets B previous peers kind_ words.all := by
  have reorder (tag : Fin 4) (a x : Fin pitch) :
      ticketAt B peers kind_ words.all tag a x ↔ ∃l,kind_ l=tag ∧ rowHit B peers a x (words.all l) := by
    constructor
    · rintro ⟨j,l,g₀,addr,kind,bit⟩
      exact ⟨l,kind,g₀,j,addr,bit⟩
    · rintro ⟨l,kind,g₀,j,addr,bit⟩
      exact ⟨j,l,g₀,addr,kind,bit⟩
  constructor
  all_goals
    intro v x a
    refine (reorder _ a x).trans ((Axes.family_search words (rowHit B peers a x) _).trans ?_)
    simp (config := {decide := true}) only [true_and, false_and, false_or, or_false]
    first | exact stem v x | exact trunk v x | exact contact v x | exact privateEdge v x

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
