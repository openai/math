import OAI.Hierarchy.DescentTerminalPeerTokenRead

namespace OAI
/-! # The measured finite set of sender keys across both wings and all resident cells -/
namespace Hierarchy.DescentTerminalPeerChronology
open DescentSixParty DescentCompiler DescentSharedCableNames DescentChosenRouter DescentColonies
open DescentTerminalCableOrder DescentTerminalGrainProfiles Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section

def localKeys {D cap : ℕ} (here other group block blocks : ℕ)
    (panel : Fin (2*cap)→Option (Stage.Live D cap)) (lane:Fin D) : Finset ℕ :=
  let entries:=Finset.univ.filter fun j=>∃u,panel j=some u ∧ u.neighbor=lane
  entries.image fun j=>(panel j).elim 0 (wingKey here other group block blocks)

theorem mem_keys {D cap : ℕ} (here other group block blocks : ℕ)
    (panel : Fin (2*cap)→Option (Stage.Live D cap)) (lane:Fin D) (z : ℕ) :
    z∈localKeys here other group block blocks panel lane ↔
      ∃j u,panel j=some u ∧ u.neighbor=lane ∧ wingKey here other group block blocks u=z := by
  simp only [localKeys,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,⟨u,hit,matchLane⟩,value⟩
    exact ⟨j,u,hit,matchLane,by simpa [hit] using value⟩
  · rintro ⟨j,u,hit,matchLane,value⟩
    exact ⟨j,⟨u,hit,matchLane⟩,by simpa [hit] using value⟩

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {groups d k i Hn : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε:ℝ}
    (A : GroupStage W G price ε (Fin groups) V k)
    (hosts : V↪Fin Hn) (S : AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (names : Stage.Host (Fin groups) V k↪ℕ)
local notation "ord" => native.trans Fin.valEmbedding
local notation "B" => Stage.source A ord
local notation "wing" => Stage.signedPanel A ord S ready names
local notation "socket" => Ends.neighborOrder (Stage.near A) names (Stage.near_room A)

theorem local_keys (h : Stage.Host (Fin groups) V k) (v:↥(Stage.near A h)) :
    let first:=min (hosts h.1.2).val (hosts v.val.1.2).val
    localKeys (hosts h.1.2).val (hosts v.val.1.2).val h.1.1.val h.2.val (2^k) (wing h) (socket h v)=
      ((Finset.univ.filter fun z : Stage.Grain A=>Stage.stream A ord z∈(B).parallel h v.val).image
        (grainKey A hosts S ready native first)) := by
  intro first
  ext n
  rw [mem_keys]
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,u,hit,lane,val⟩
    have occupied:∃a,Stage.signed A ord S ready h.1 h.2 a=j:=by
      by_contra no
      rw [Stage.signed_empty A ord S ready names h j (not_exists.mp no)] at hit
      contradiction
    obtain ⟨a,rfl⟩:=occupied
    rw [Stage.signed_read] at hit
    obtain rfl:=Option.some.inj hit
    let e:=Stage.ofPort A ord h a
    have friend:(B).peer h e.val=v.val:=(peer_slot A ord S ready names h v a).1 lane
    refine ⟨Stage.recover A h a,?_,?_⟩
    · rw [←recover_stream A native]
      exact ((B).mem_parallel ..).2 ⟨e.property,friend⟩
    · have read:=wing_key A hosts S ready native names h a
      rw [show (B).peer h (Stage.ofPort A ord h a).val=v.val from friend] at read
      exact read.symm.trans val
  · rintro ⟨z,hz,rfl⟩
    let e:=Stage.stream A ord z
    have both:=((B).mem_parallel ..).1 hz
    let a:=Stage.asPort A ord h ⟨e,both.1⟩
    have recovered:Stage.recover A h a=z:=(Stage.recover_port ..).trans ((Stage.stream A ord).symm_apply_apply z)
    have orig:(Stage.ofPort A ord h a).val=e:=by rw [recover_stream,recovered]
    have friend:(B).peer h (Stage.ofPort A ord h a).val=v.val:=orig ▸ both.2
    refine ⟨_,_,Stage.signed_read A ord S ready names h a,(peer_slot A ord S ready names h v a).2 friend,?_⟩
    have read:=wing_key A hosts S ready native names h a
    simpa only [friend,recovered] using read

/-- No separate symbol is introduced for the receiving copy of an internal wire. -/
def peerKeys {groups blocks D cap:ℕ} (here other:ℕ) (lane:Fin D)
    (panel:Fin groups→Fin blocks→Fin (2*cap)→Option (Stage.Live D cap)) : Finset ℕ :=
  Finset.univ.biUnion fun g=>Finset.univ.biUnion fun b=>localKeys here other g.val b.val blocks (panel g b) lane

theorem union_keys (here other : V) (adj:other∈A.near here) :
    let panel:=fun (g:Fin groups) (b:Block k)=>wing ((g,here),b)
    let first:=min (hosts here).val (hosts other).val
    let neighbor:=fun (g:Fin groups) (b:Block k)=>
      (⟨((g,other),b),Finset.mem_map.mpr ⟨(g,other),Finset.mem_map.mpr ⟨other,adj,rfl⟩,rfl⟩⟩ :
        ↥(Stage.near A ((g,here),b)))
    (Finset.univ.biUnion fun g=>Finset.univ.biUnion fun b=>
        localKeys (hosts here).val (hosts other).val g.val b.val (2^k) (panel g b) (socket _ (neighbor g b)))=
      ((Finset.univ.filter fun z : Stage.Grain A=>
        pairIndex W.graph (fun u=>hosts (A.pos u).2) z.1=pair (hosts here) (hosts other)).image
          (grainKey A hosts S ready native first)) := by
  intro panel first neighbor
  have one (g:Fin groups) (b:Block k):=local_keys A hosts S ready native names ((g,here),b) (neighbor g b)
  simp only at one
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨g,b,hz⟩
    rw [one] at hz
    obtain ⟨y,h,eqn⟩:=Finset.mem_image.mp hz
    exact ⟨y,((parallel_at A ord hosts here other g b y).1 (Finset.mem_filter.mp h).2).2.2,eqn⟩
  · rintro ⟨y,h,eqn⟩
    let g:=(A.pos (W.graph.src y.1)).1
    let b:=A.block (W.graph.src y.1)
    refine ⟨g,b,?_⟩
    rw [one]
    exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(parallel_at A ord hosts here other g b y).2 ⟨rfl,rfl,h⟩⟩,eqn⟩

end
end Hierarchy.DescentTerminalPeerChronology

end OAI
