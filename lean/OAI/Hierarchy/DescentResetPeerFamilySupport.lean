import OAI.Hierarchy.DescentResetPeerUnionRAM
import OAI.Hierarchy.DescentResetNativeClass
import OAI.Hierarchy.DescentClosedLocalRoster

namespace OAI
/-! # Complete raw incidence of reset stems, trunks, contacts and installed device edges -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentStageEdgeReceipt DescentParallelBase
open DescentPacking DescentResetPeerUnionRAM DescentSortedRoster DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "raw" => B.reset.rawHostRank B.terminals vertex
local notation "Vnew" => B.next.V

/-- Columns zero, one and two of the literal raw header. Both polarities
of a loop work, and column five (the width) plays no role here. -/
def incidentWords (v u : ℕ) (row : Fin 7→ℕ) : Prop :=
  row 0=1 ∧ ((row 1=v ∧ row 2=u) ∨ (row 2=v ∧ row 1=u))

def rawPeer (e : (coarse).graph.Edge) (v u : ℕ) : Prop :=
  incidentWords v u ((Z).actualRecord T vertex e)

/-- This is an exhaustive disjunction even for actual contacts or device
cables whose width is zero. The four parent constructors cover the prior graph. -/
theorem raw_families (v u : ℕ) :
    (∃e,rawPeer B e v u) ↔
      (∃x,rawPeer B (stemParent B x) v u) ∨
      (∃t,rawPeer B (trunkParent B t) v u) ∨
      (∃c,rawPeer B (contactParent B c) v u) ∨
      ∃j,rawPeer B (privateWire B j) v u := by
  constructor
  · rintro ⟨e,near⟩
    obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
    rcases tag with x|t|c|j
    · exact .inl ⟨x,near⟩
    · exact .inr (.inl ⟨t,near⟩)
    · exact .inr (.inr (.inl ⟨c,near⟩))
    · exact .inr (.inr (.inr ⟨j,(private_parent B j) ▸ near⟩))
  · rintro (⟨x,hx⟩|⟨x,hx⟩|⟨x,hx⟩|⟨x,hx⟩) <;> exact ⟨_,hx⟩

theorem raw_incidence (v u : Vnew) :
    (∃e,rawPeer B e (raw v).val (raw u).val) ↔ u∈(Z).emittedNear T v := by
  have range (x y : Vnew) : (raw x).val=(raw y).val ↔ x=y :=
    ⟨fun h=>(raw).injective (Fin.ext h),fun h=>h ▸ rfl⟩
  have edge (e : (coarse).graph.Edge) :
      rawPeer B e (raw v).val (raw u).val ↔
        (((Z).placed T ((coarse).graph.src e)=v ∧ (Z).placed T ((coarse).graph.dst e)=u) ∨
         ((Z).placed T ((coarse).graph.dst e)=v ∧ (Z).placed T ((coarse).graph.src e)=u)) := by
    change (1=1 ∧ (((raw ((Z).placed T ((coarse).graph.src e))).val=(raw v).val ∧
        (raw ((Z).placed T ((coarse).graph.dst e))).val=(raw u).val) ∨
        ((raw ((Z).placed T ((coarse).graph.dst e))).val=(raw v).val ∧
        (raw ((Z).placed T ((coarse).graph.src e))).val=(raw u).val))) ↔ _
    exact (and_iff_right (rfl : 1=1)).trans
      (or_congr (and_congr (range _ _) (range _ _)) (and_congr (range _ _) (range _ _)))
  have member {α : Type} {p : α → Prop} {dec : DecidablePred p} {a : α} {fs : Finset α} :
      a ∈ @Finset.filter α p dec fs ↔ a ∈ fs ∧ p a := @Finset.mem_filter α p dec fs a
  constructor
  · rintro ⟨e,he⟩
    exact member.mpr ⟨Finset.mem_univ _, e, (edge e).mp he⟩
  · intro he
    obtain ⟨e,he⟩ := (member.mp he).2
    exact ⟨e,(edge e).mpr he⟩

/-- Numeric candidates may repeat or be absent. All membership evidence is
read from the original raw parent records of these four families. -/
structure FamilyReads {pitch slots sheets word : ℕ} (ports : Inputs slots sheets)
    (keys : Fin pitch→Fin slots→Option (Fin pitch)) (m : Memory word)
    (name : Vnew↪Fin pitch) : Prop where
  hostCode : ∀v,(name v).val=(raw v).val
  other : ∀h : Fin pitch,∀j,(ports.other j).eval m (h.val:Word word)=(target (keys h j):Word word)
  capacity : ∀v u : Vnew,u∈(Z).emittedNear T v → ∃j,keys (name v) j=some (name u)
  signals : ∀v j (x : Fin pitch),keys (name v) j=some x →
    ((∃l,(ports.evidence j l).eval m ((name v).val:Word word) ≠ 0) ↔
      (∃a,rawPeer B (stemParent B a) (name v).val x.val) ∨
      (∃a,rawPeer B (trunkParent B a) (name v).val x.val) ∨
      (∃a,rawPeer B (contactParent B a) (name v).val x.val) ∨
      ∃a,rawPeer B (privateWire B a) (name v).val x.val)

theorem raw_has_target (v u : ℕ) (e : (coarse).graph.Edge) (near : rawPeer B e v u) :
    ∃y : Vnew,(raw y).val=u := by
  rcases near.2 with pair|pair
  · exact ⟨_,pair.2⟩
  · exact ⟨_,pair.2⟩

theorem FamilyReads.targets {pitch slots sheets word : ℕ} {ports : Inputs slots sheets}
    {keys : Fin pitch→Fin slots→Option (Fin pitch)} {m : Memory word} {name : Vnew↪Fin pitch}
    (reads : FamilyReads B ports keys m name) (v : Vnew) :
    present (observed ports m keys) (name v)=((Z).emittedNear T v).map name := by
  classical
  ext x
  constructor
  · intro seen
    obtain ⟨j,hit⟩:=(Finset.mem_filter.mp seen).2
    unfold observed at hit
    split at hit
    · rename_i yes
      obtain ⟨e,near⟩:=(raw_families B _ _).mpr ((reads.signals v j x hit).mp yes)
      obtain ⟨u,r⟩:=raw_has_target B _ _ e near
      have same : name u=x:=Fin.ext ((reads.hostCode u).trans r)
      refine Finset.mem_map.mpr ⟨u,?_,same⟩
      apply (raw_incidence B v u).mp
      exact ⟨e,by simpa only [←reads.hostCode v,r] using near⟩
    · contradiction
  · rintro member
    obtain ⟨u,near,rfl⟩:=Finset.mem_map.mp member
    obtain ⟨j,key⟩:=reads.capacity v u near
    have evidence := (raw_incidence B v u).mpr near
    rw [←reads.hostCode v,←reads.hostCode u] at evidence
    have ok:=(reads.signals v j _ key).mpr ((raw_families B _ _).mp evidence)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,by simp only [observed,ite_eq_left ok,key]⟩

/-- The same reached memory contains all three genuine neighbor labels and
the complete self-plus-neighbor set used by the physical four-way ranker. -/
theorem emitted_directory {pitch slots sheets word base : ℕ} (ports : Inputs slots sheets)
    (safe : DescentResetPeerUnionRAM.Room ports base pitch word) (keys : Fin pitch→Fin slots→Option (Fin pitch))
    (m : Memory word) (name : Vnew↪Fin pitch) (reads : FamilyReads B ports keys m name) :
    let peers:=adj (observed ports m keys) safe.candidates
    let reached:=after ports base pitch m
    (machine ports word base pitch).Exec m reached (ticks ports base pitch) ∧
    (∀h : Fin pitch,∀j : Fin 3,reached (outBase base pitch slots+j.val*pitch+h.val)=(target (peers h j):Word word)) ∧
    (∀v : Vnew,present (selfPeers peers) (name v)=(insert v ((Z).emittedNear T v)).map name) ∧
    (∀v : Vnew,(∀j,peers (name v) j ≠ some (name v)) ↔ v∉(Z).emittedNear T v) ∧
    (∀a,a < base ∨ stop base pitch slots ≤ a → reached a=m a) ∧ CheapCode (machine ports word base pitch) := by
  intro peers reached
  obtain ⟨run,cheap,frame⟩:=any ports safe m
  have sets (v : Vnew) : present peers (name v)=((Z).emittedNear T v).map name := by
    have total:=reads.targets B v
    have bound := (Z).emitted_degree T v
    have size : (present (observed ports m keys) (name v)).card ≤ 3 := by
      rw [total]
      exact (Finset.card_map (s:=(Z).emittedNear T v) name).trans_le bound
    exact (present_three _ _ _ size).trans total
  refine ⟨run,read ports safe m keys reads.other,?_,?_,frame,cheap⟩
  · intro v
    rw [self_present,sets]
    exact (Finset.map_insert name v ((Z).emittedNear T v)).symm
  · intro v
    have own : name v∈present peers (name v) ↔ v∈(Z).emittedNear T v := by
      rw [sets]
      exact Finset.mem_map' name
    refine Iff.trans ?_ (not_congr own)
    simp [present]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
