import OAI.Hierarchy.DescentPackedFlowIdentity
import OAI.Hierarchy.DescentPackedFlowRAM

namespace OAI
/-! # The true grouped signed tags and common physical neighbor rows -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentSIMDLookup DescentSharedCableNames DescentStageEdgeReceipt DescentHostDirectory
open DescentPacking.PackedMatch.Local
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i m : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J↪ℕ) (hosts : V↪ℕ)
local notation "rank" => groupRank groups hosts
local notation "Nm" => DescentPacking.PackedMatch.Local.Stage.cableNames k rank
local notation "rot" => DescentPacking.PackedMatch.Local.Stage.rotor A rank
local notation "ord" => DescentPacking.PackedMatch.Local.Stage.ordinal A rank

def socket (v : V) := Ends.neighborOrder A.near hosts A.degreeBound v

theorem socket_grouped (g : J) (v : V) (u : ↥(A.near v)) :
    ord (g,v) ⟨(g,u.val),Finset.mem_map.mpr ⟨u.val,u.property,rfl⟩⟩=socket A hosts v u := by
  apply Fin.ext
  rw [DescentPacking.PackedMatch.Local.Stage.ordinal,socket,DescentPacking.PackedMatch.Local.Stage.nb_val,
    DescentPacking.PackedMatch.Local.Stage.nb_val]
  have equal : ((DescentPacking.PackedMatch.Local.Stage.neighbors A (g,v)).filter (fun z=>rank z<rank (g,u.val)))=
      ((A.near v).filter (fun z=>hosts z<hosts u.val)).map (liftSite g) := by
    ext z
    simp only [DescentPacking.PackedMatch.Local.Stage.neighbors,groupedNear,Finset.mem_map,Finset.mem_filter]
    constructor
    · rintro ⟨⟨y,inRoster,rfl⟩,less⟩
      exact ⟨y,⟨inRoster,Nat.lt_of_add_lt_add_left less⟩,rfl⟩
    · rintro ⟨y,⟨inRoster,less⟩,rfl⟩
      exact ⟨⟨y,inRoster,rfl⟩,Nat.add_lt_add_left less _⟩
  rw [equal,Finset.card_map]

theorem grouped_peer (g : J) (v : V) (u : ↥(A.near v)) :
    rot (g,v) (socket A hosts v u)=some (g,u.val) := by
  rw [←socket_grouped A groups hosts g v u]
  exact DescentPacking.PackedMatch.Local.Stage.rotor_at ..

def chips (short : ℕ) (g : J) (v : V) (q : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) : Cell short :=
  DescentPacking.PackedMatch.Local.Stage.marked short
    (DescentSharedCableNames.Stage.signedPanel A native S ready Nm ((g,v),q.1) q.2)

theorem chip_count (short : ℕ) (ok : A.degree<2^short) (g : J) (v : V) (u : ↥(A.near v)) (x : Block k) :
    DescentPackedFlowRAM.counts (chips A native S ready groups hosts short g v) (socket A hosts v u).val x =
      outgoing A (g,v) (g,u.val) x := by
  let t:=socket A hosts v u
  let p:=DescentPacking.PackedMatch.Local.Stage.terrain (short:=short) A native S ready Nm
    (fun _ _=>(0:Cell 1)) rot (g,v)
  let tag:=chips A native S ready groups hosts short g v
  have cond (s : Fin (2*A.cap)) : (tag (x,s)).val=t.val+1 ↔ peer p x s=some t := by
    let n:=(tag (x,s)).val
    change n=t.val+1 ↔ (if h:0<n ∧ n≤A.degree then some ⟨n-1,by omega⟩ else none)=some t
    split
    · simp only [Option.some.injEq,Fin.ext_iff];omega
    · constructor
      · intro same
        have bound := t.isLt
        omega
      · intro same
        cases same
  have a : Fintype.card {s : Fin (2*A.cap) // (tag (x,s)).val=t.val+1}=
      Fintype.card {s : Fin (2*A.cap) // peer p x s=some t} :=
    Fintype.card_congr (Equiv.subtypeEquivRight cond)
  exact a.trans (directed_card A native S ready rank short ok (g,v) (g,u.val) x t
    (grouped_peer A groups hosts g v u))

theorem unused (short : ℕ) (ok : A.degree<2^short) (g : J) (v : V) (t : Fin A.degree)
    (empty : ∀u : ↥(A.near v),socket A hosts v u≠t) (x : Block k) :
    DescentPackedFlowRAM.counts (chips A native S ready groups hosts short g v) t.val x=0 := by
  let p:=DescentPacking.PackedMatch.Local.Stage.terrain (short:=short) A native S ready Nm
    (fun _ _=>(0:Cell 1)) rot (g,v)
  apply Fintype.card_eq_zero_iff.2
  constructor
  rintro ⟨s,hit⟩
  have key : (p.neighbor x s).val=t.val+1:=hit
  have live : peer p x s=some t := by
    have := t.isLt
    simp [peer,key,show t.val+1≤A.degree by omega]
  obtain ⟨e,_,eqn⟩ := (DescentPacking.PackedMatch.Local.Stage.all_ports A native S ready Nm
    (fun _ _=>(0:Cell 1)) rot ((g,v),x) s t ok).1 live
  have dst:=DescentPacking.PackedMatch.Local.Stage.rotor_routes A native S ready rank (g,v) x e
  rw [eqn] at dst
  have mem := (A.peers e.val).1
  rw [e.property.1.1] at mem
  obtain ⟨u,inside,ueq⟩:=Finset.mem_map.mp mem
  have canon:=grouped_peer A groups hosts g v ⟨u,inside⟩
  change (g,u)=A.pos (W.graph.dst e.val) at ueq
  rw [←ueq] at dst
  exact empty ⟨u,inside⟩ (rotor_unique A rank _ _ _ _ canon dst)

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
