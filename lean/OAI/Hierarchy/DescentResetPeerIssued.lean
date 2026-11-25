import OAI.Hierarchy.DescentResetPeerReach
import OAI.Hierarchy.DescentResetPeerTariff

namespace OAI
/-! # Three native peer words from the four unfiltered reset record families -/
namespace Hierarchy.DescentResetPeerUnionRAM

/-- A packed lane contains zero for an absent record, or one plus its local
candidate slot. More than one slot may name the same genuine neighbor. -/
def marked {D E b : ℕ} (j : Fin D) (_ : Fin E) (code : DescentSIMDLookup.Cell b) : Bool :=
  decide (code.val=j.val+1)

theorem marked_zero {D E b : ℕ} (j : Fin D) (e : Fin E) : marked j e (0:DescentSIMDLookup.Cell b)=false := by
  simp [marked]

end Hierarchy.DescentResetPeerUnionRAM

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
local notation "Vnew" => ↥(ResetInput.commonNames B.reset B.terminals)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
variable {H D₀ E b M J w : ℕ}
local notation "pitch" => H*shelf
local notation "slots" => Candidates.count shelf D₀

/-- One word-wide equality represents an entire SIMD chunk. Individual
LANE tickets contain only a short relative old socket and a local shape. -/
def ticketAt (peers : Fin H→Fin D₀→Option (Fin H)) (family : Fin E→Fin 4)
    (values : Fin E→Fin pitch→Fin J→Cell b) (tag : Fin 4) (v x : Fin pitch) : Prop :=
  ∃(j : Fin slots) (e : Fin E) (g₀ : Fin J),
    Candidates.candidate peers v j=some x ∧ family e=tag ∧ (values e v g₀).val=j.val+1

structure IssuedTickets (previous : Fintype.card input.V ≤ H) (peers : Fin H→Fin D₀→Option (Fin H))
    (family : Fin E→Fin 4) (values : Fin E→Fin pitch→Fin J→Cell b) : Prop where
  stem : ∀(v : Vnew) (x : Fin pitch),
    let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
    ticketAt B peers family values 0 a x ↔ ∃t,rawPeer B (stemParent B t) a.val x.val
  trunk : ∀(v : Vnew) (x : Fin pitch),
    let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
    ticketAt B peers family values 1 a x ↔ ∃t,rawPeer B (trunkParent B t) a.val x.val
  contact : ∀(v : Vnew) (x : Fin pitch),
    let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
    ticketAt B peers family values 2 a x ↔ ∃t,rawPeer B (contactParent B t) a.val x.val
  privateEdge : ∀(v : Vnew) (x : Fin pitch),
    let a:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous)) v
    ticketAt B peers family values 3 a x ↔ ∃t,rawPeer B (privateWire B t) a.val x.val

/-- The code runs on all inputs. On the physical grouped raw-family chips its
output is the complete emitted neighbor set, with a separate membership test for loops. -/
theorem genuine_program {start : ℕ} (previous : Fintype.card input.V ≤ H) (old : Bank)
    (src : Fin E→Fin (chunks J M)→Expr) (safe : Program.Space start H shelf D₀ E b M J w old src)
    (peers : Fin H→Fin D₀→Option (Fin H)) (family : Fin E→Fin 4)
    (values : Fin E→Fin pitch→Fin J→Cell b) (m : Memory w)
    (reads : ∀(h : Fin H) (d : Fin D₀),m (old.base+(h.val*D₀+d.val))=(target (peers h d):Word w))
    (rows : ∀(e : Fin E) (h : Fin pitch) (c : Fin (chunks J M)),(src e c).eval m (h.val:Word w)=((data (M:=M) (values e) (h,c)).val:Word w))
    (pos : 0 < M) (bitsRead : IssuedTickets B previous peers family values) :
    let name:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous))
    let code:=Program.program w start H shelf D₀ b M J old marked src
    let out:=Program.output start H shelf D₀ b M J old marked src m
    let address:=Program.scratchAt start H shelf D₀ E b M
    code.Exec m out (Program.clock start H shelf D₀ b M J old src) ∧ CheapCode code ∧
      (∃found : Fin pitch→Fin 3→Option (Fin pitch),
        (∀(h : Fin pitch) (j : Fin 3),out (outBase address pitch slots+j.val*pitch+h.val)=(target (found h j):Word w)) ∧
        (∀v : Vnew,present (selfPeers found) (name v)=(insert v ((Z).emittedNear T v)).map name) ∧
        (∀v : Vnew,(∀j,found (name v) j ≠ some (name v)) ↔ v∉(Z).emittedNear T v)) ∧
      ∀a,a < start ∨ Program.endAddress start H shelf D₀ E b M ≤ a → out a=m a := by
  intro name code out address
  let ports:=Program.operands start H shelf D₀ b M J old src
  let mid:=Program.mounted start H shelf D₀ M (marked (E:=E) (b:=b)) m
  let keys:=Candidates.candidate (S:=shelf) peers
  let evidence:=observed ports mid keys
  let room:=Program.room safe
  have go:=Program.any old marked src safe m
  obtain ⟨names,raw⟩:=Program.loaded old marked src safe m peers reads values rows pos marked_zero
  have sampled (v : Fin pitch) (x : Fin pitch) :
      x∈present evidence v ↔ ∃tag,ticketAt B peers family values tag v x := by
    constructor
    · intro hx
      obtain ⟨j,hit⟩:=(Finset.mem_filter.mp hx).2
      unfold evidence observed at hit
      split at hit
      · rename_i yes
        obtain ⟨e,g₀,word⟩:=(raw v j).mp yes
        exact ⟨family e,j,e,g₀,hit,rfl,of_decide_eq_true word⟩
      · contradiction
    · rintro ⟨tag,j,e,g₀,key,_,bit⟩
      have live:=(raw v j).mpr ⟨e,g₀,decide_eq_true bit⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,?_⟩
      change (if ∃t,(ports.evidence j t).eval mid (v.val:Word w) ≠ 0 then keys v j else none)=some x
      exact (ite_eq_left live).trans key
  have found (v : Vnew) (x : Fin pitch) :
      x∈present evidence (name v) ↔ ∃e,rawPeer B e (name v).val x.val := by
    rw [sampled,raw_families]
    constructor
    · rintro ⟨tag,hit⟩
      fin_cases tag
      · exact .inl ((bitsRead.stem v x).mp hit)
      · exact .inr (.inl ((bitsRead.trunk v x).mp hit))
      · exact .inr (.inr (.inl ((bitsRead.contact v x).mp hit)))
      · exact .inr (.inr (.inr ((bitsRead.privateEdge v x).mp hit)))
    · rintro (hs|ht|hc|hp)
      · exact ⟨0,(bitsRead.stem v x).mpr hs⟩
      · exact ⟨1,(bitsRead.trunk v x).mpr ht⟩
      · exact ⟨2,(bitsRead.contact v x).mpr hc⟩
      · exact ⟨3,(bitsRead.privateEdge v x).mpr hp⟩
  have sets (v : Vnew) : present evidence (name v)=((Z).emittedNear T v).map name := by
    ext x
    rw [found]
    constructor
    · rintro ⟨e,physical⟩
      obtain ⟨u,hu⟩:=raw_has_target B _ _ e physical
      have same : name u=x := Fin.ext hu
      refine Finset.mem_map.mpr ⟨u,(raw_incidence B v u).mp ⟨e,?_⟩,same⟩
      exact hu.symm ▸ physical
    · intro hx
      obtain ⟨u,near,rfl⟩:=Finset.mem_map.mp hx
      exact (raw_incidence B v u).mpr near
  let reported:=adj evidence room.candidates
  have all (v : Vnew) : present reported (name v)=((Z).emittedNear T v).map name := by
    have bound : (present evidence (name v)).card ≤ 3 := by
      rw [sets,Finset.card_map]
      exact (Z).emitted_degree T v
    exact (present_three evidence room.candidates (name v) bound).trans (sets v)
  refine ⟨go.1,go.2.1,⟨reported,read ports room mid keys names,?_,?_⟩,go.2.2⟩
  · intro v
    rw [self_present,all,Finset.map_insert]
  · intro v
    have iff_ : name v∈present reported (name v) ↔ v∈(Z).emittedNear T v := by rw [all];simp
    have neg:=not_congr iff_
    simpa only [present,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using neg

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
