import OAI.Hierarchy.DescentOrdinaryParticleReceipt
import OAI.Hierarchy.DescentRecipeTokenCorrespondence

namespace OAI
/-! # Local semantic meaning of the actual native placement and name-permutation receipt -/

namespace Hierarchy.DescentSixParty
open DescentKernelHistory DescentHostDirectory DescentColonies GadgetNetwork MarkedWorld
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

structure LocalParticles (B : BitDescription W) (count : W.graph.Site→ℕ) (hub : W.graph.Site→Bool) : Prop where
  nodes : ∀v,Fintype.card (B.recipe v).Node=count v+W.exteriorTokens v
  balance : W.HubExterior hub
  attached : ∀i,hub (W.graph.attach i)=true

namespace LocalParticles
variable {B : BitDescription W} {count : W.graph.Site→ℕ} {hub : W.graph.Site→Bool} (h : LocalParticles B count hub)
include h

theorem renamed (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) :
    LocalParticles (B.renamed s e) (count∘s.symm) (hub∘s.symm) := by
  let records (u : W.graph.Site) := List.replicate (count u) ()
  have old : B.Tokenized records := by intro v;simpa [records] using h.nodes v
  refine ⟨?_,PhysicalRename.hub_balance W s e hub h.balance,?_⟩
  · intro v
    have node := BitDescription.Tokenized.renamed B records old s e v
    change _ = (List.replicate (count (s.symm v)) ()).length +
      (PhysicalRename.world W s e).exteriorTokens v at node
    rw [List.length_replicate] at node
    exact node
  · intro i
    change hub (s.symm (s (W.graph.attach i)))=true
    simpa using h.attached i

theorem castRow {X : MarkedWorld F d P bits} {b : BitDescription X} (same : X=W) (bb : HEq b B) :
    LocalParticles b (transferRow same count) (transferRow same hub) := by
  subst X
  cases eq_of_heq bb
  exact h
end LocalParticles

omit [Fintype P] in
private theorem append_description {N : MarkedWorld F d P bits} (norm : Normalize N) (b : BitDescription N)
    (s : Equiv.Perm norm.result.graph.Site) (e : Equiv.Perm norm.result.graph.Edge) :
    HEq (BitDescription.follow (norm.appendNames s e) b) ((BitDescription.follow norm b).renamed s e) := by
  induction norm with
  | done=>rfl
  | named W v a n ih=> exact ih (b.renamed v a) s e
  | split W q m fit n ih=> exact ih (b.pieces m q fit) s e
  | merge W V key flag k g n ih=>exact ih (b.coalesced key flag k g) s e

variable {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε)
  (c : (T.result he).Choice) (B : BitDescription W)
private abbrev selectedParticleDescription :=
  let rows := BitDescription.scannedRows he T
  B.selected G rows.pick (fun _ => T.z) (fun _ => T.unitPos) rows.fit
    (fun _ => le_refl T.z) rows.pack (rows.profile c)

theorem ParticleRows.readFrom {N : MarkedWorld F d P bits} {n : Normalize N} {count : n.result.graph.Site→ℕ}
    {tag : n.result.graph.Site→Bool} (received : ParticleRows he T c N n count tag)
    (X : BitDescription N) (head : HEq X (selectedParticleDescription he T c B)) (old : LocalParticles B (fun v=>(T.records v).length) T.hub) :
    LocalParticles (BitDescription.follow n X) count tag := by
  revert X
  induction received with
  | stage key flag pos tags k g q previous used chunks inc packed same =>
    intro X head
    have actual := eq_of_heq head
    subst X
    let rows := BitDescription.scannedRows he T
    let z := fun _ : rows.pairs => T.z
    let hz : ∀ j, 0 < z j := fun _ => T.unitPos
    let profile := rows.profile c
    let m := MarkedWorld.repetitions W G rows.pick z hz rows.fit rows.pack profile key flag k g q
    let cut := MarkedWorld.repetition_width W G rows.pick z hz rows.fit rows.pack profile key flag k g q previous used chunks
    have prior : B.Tokenized T.records := old.nodes
    have step := BitDescription.Tokenized.selected B T.records prior G rows.pick z hz rows.fit
      (fun _=>le_refl T.z) rows.pack profile
    have grouped := BitDescription.Tokenized.coalesced _ _ step key flag k g
    refine ⟨BitDescription.Tokenized.split _ _ grouped m q cut,?_,?_⟩
    · apply W.selected_exterior_balance G rows.pick z hz rows.fit rows.pack profile pos flag inc used packed key q m cut _ same
      simpa only [←tags] using old.balance
    · apply W.selected_exterior_owners G rows.pick z hz rows.fit rows.pack profile pos flag inc used packed key q m cut _ same
      intro i
      change (flag∘pos) (W.graph.attach i)=true
      rw [←tags]
      exact old.attached i
  | named n prior s e ih =>
    intro X head
    exact (ih X head).renamed s e |>.castRow (n.appendNames_result s e) (append_description n X s e)

theorem ParticleRows.read {n : Normalize ((T.result he).state c)} {count : n.result.graph.Site→ℕ}
    {tag : n.result.graph.Site→Bool} (received : ParticleRows he T c _ n count tag)
    (old : LocalParticles B (fun v=>(T.records v).length) T.hub) :
    LocalParticles (BitDescription.follow n (BitDescription.scanned he T B c)) count tag :=
  received.readFrom he T c B (BitDescription.scanned he T B c) (BitDescription.scanned_anchor he T B c) old

end
end Hierarchy.DescentSixParty

end OAI
