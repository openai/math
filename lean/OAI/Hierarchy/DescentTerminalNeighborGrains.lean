import OAI.Hierarchy.DescentTerminalSignedGrainWord

namespace OAI
/-! # Counting a physical neighbor's live grains in the two signed port panels -/
namespace Hierarchy.DescentTerminalGrainProfiles
open DescentSixParty DescentSharedCableNames DescentCompiler DescentColonies
open scoped Classical
noncomputable section

/-- A loop contributes its wire serial once even when both signed records are present. -/
def peerWires {D c : ℕ} (panel:Fin (2*c)→Option (Stage.Live D c)) (lane:Fin D) : Finset (Fin c) :=
  Finset.univ.filter fun s=>∃i u,panel i=some u ∧ u.neighbor=lane ∧ u.wire=s

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready:A.StateBounds S i)
    (names:Stage.Host J V k↪ℕ)
local notation "B" => Stage.source A native
local notation "order" => Ends.neighborOrder (Stage.near A) names (Stage.near_room A)

def serialMap (h v:Stage.Host J V k) : ↥((B).parallel h v) ↪ Fin A.cap where
  toFun q:=⟨(B).serial h v q.val,(B).serial_lt (Stage.measured A native S ready) h v q.val q.property⟩
  inj' a b eqn:=Subtype.ext ((B).distinguish a.property b.property (congrArg Fin.val eqn))

theorem peer_slot (h:Stage.Host J V k) (v:↥(Stage.near A h)) (u:A.CellPorts h.1.1 h.1.2 h.2) :
    (Stage.live A native S ready names h u).neighbor=order h v ↔
      (B).peer h (Stage.ofPort A native h u).val=v.val := by
  change order h _=order h v ↔ _
  rw [Function.Embedding.apply_eq_iff_eq,Subtype.ext_iff]

theorem pair_columns (h:Stage.Host J V k) (v:↥(Stage.near A h)) :
    peerWires (Stage.signedPanel A native S ready names h) (order h v)=
      Finset.univ.map (serialMap A native S ready h v.val) := by
  ext s
  simp only [peerWires,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  constructor
  · rintro ⟨j,out,hit,lane,wire⟩
    have found:∃u,Stage.signed A native S ready h.1 h.2 u=j := by
      by_contra no
      rw [Stage.signed_empty A native S ready names h j (not_exists.mp no)] at hit
      contradiction
    obtain ⟨u,rfl⟩:=found
    rw [Stage.signed_read] at hit
    obtain rfl:=Option.some.inj hit
    let e:=Stage.ofPort A native h u
    have friend:(B).peer h e.val=v.val:=(peer_slot A native S ready names h v u).1 lane
    refine ⟨⟨e.val,((B).mem_parallel ..).2 ⟨e.property,friend⟩⟩,?_⟩
    apply Fin.ext
    rw [←wire]
    change (B).serial h v.val e.val=(B).serial h ((B).peer h e.val) e.val
    rw [friend]
  · rintro ⟨e,rfl⟩
    have both:=((B).mem_parallel ..).1 e.property
    let u:=Stage.asPort A native h ⟨e.val,both.1⟩
    have back:(Stage.ofPort A native h u).val=e.val := by
      have repr (p:A.CellPorts h.1.1 h.1.2 h.2) :
          (Stage.ofPort A native h p).val=Stage.stream A native (Stage.recover A h p) := by cases p <;> rfl
      rw [repr,show Stage.recover A h u=(Stage.stream A native).symm e.val from Stage.recover_port ..,
        Equiv.apply_symm_apply]
    refine ⟨_,_,Stage.signed_read A native S ready names h u,
      (peer_slot A native S ready names h v u).2 (by rw [back];exact both.2),?_⟩
    apply Fin.ext
    change (B).serial h ((B).peer h (Stage.ofPort A native h u).val) (Stage.ofPort A native h u).val=(B).serial h v.val e.val
    rw [back,both.2]

theorem pair_count (h:Stage.Host J V k) (v:↥(Stage.near A h)) :
    (peerWires (Stage.signedPanel A native S ready names h) (order h v)).card=((B).parallel h v.val).card := by
  simp [pair_columns A native S ready names h v]

end
end Hierarchy.DescentTerminalGrainProfiles

end OAI
