import OAI.Computability.BorderVNP.CubeISAOwnedScatterRow
import OAI.Computability.BorderVNP.CubeScatterChoiceTape

/-! # Realizing a complete chronological choice tape on a fixed packet row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.PacketRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned Physical.VertexIndex VPVNP.BurstRAM VPVNP.MotifBase
open DiagonalResidueRAM Tally ChoiceTape

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

/-- Replace just the bit assignments while retaining the selected ranks and physical layout. -/
def withWords (x : Packet n d blocks → Ends n → Fin (h*b) → Bool)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (D.select p).2 e) → Bool) :=
  { D with demand := x, supply := z }

/-- Both routed input cursors depend only on the public selectors, even if every private bit
is changed. -/
theorem withWords_cursors (x z) (m : Memory w) (k : ℕ) :
    ((D.withWords x z).before m k).sel = (D.before m k).sel ∧
    ((D.withWords x z).before m k).cross = (D.before m k).cross := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    rw [before,before]
    change (match RoutingISA.OwnedVertex.packetAtNat D.axis D.pair k with
      | none => _ | some p => (D.withWords x z).visit p _).sel = _ ∧ _
    split <;> simp_all [visit,withWords,crossLength]

/-- Recovered private fields still meet the initial source conditions as long as every routed
position agrees with its original requirement. -/
theorem prepared_withWords {src : Set ℕ} (m : Memory w) (ready : D.PreparedRow src m) (x z)
    (routed : ∀ p, (D.body p).map Position.routed = ((D.withWords x z).body p).map Position.routed) :
    (D.withWords x z).PreparedRow src m := by
  intro t ok
  let p := D.packet t ok
  have same : (D.withWords x z).cursor p ((D.withWords x z).before m t.val) = D.cursor p (D.before m t.val) := by
    unfold cursor
    rw [(D.withWords_cursors x z m t.val).1,(D.withWords_cursors x z m t.val).2]
    rfl
  change Prepared src (selectorPositions (D.select p) ++ (D.withWords x z).body p)
    ((D.withWords x z).cursor p ((D.withWords x z).before m t.val)) m
  rw [same]
  exact (ready t ok).of_routed (by simp only [List.map_append,routed,p])

/-- Count the private digit slots of the packet at each actual candidate. -/
def privateWidth (t : Fin (packetTrials n d blocks)) :=
  if ok : packetTrialValid t then
    let p := D.packet t ok
    privateCount (bodyModes b s (D.select p) D.axis (ownerBit D.axis p.1.2 D.high))
  else 0

/-- Bit fields off the visited row or off its owned side retain their original assignments.
In particular, all incoming crossing supplies are preserved. -/
def KeepsExterior (x : Packet n d blocks → Ends n → Fin (h*b) → Bool)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (D.select p).2 e) → Bool) : Prop :=
  ∀ p, (p.1.1 D.axis ≠ D.pair → x p = D.demand p ∧ z p = D.supply p) ∧
    (∀ e j, finTwoEquiv ((if e.2 then stop e.1 else start e.1) D.axis) ≠ ownerBit D.axis p.1.2 D.high →
      x p e j = D.demand p e j) ∧
    (∀ e j, e.2 = D.axis ∨ finTwoEquiv (e.1 D.axis) ≠ ownerBit D.axis p.1.2 D.high → z p e j = D.supply p e j)

/-- Every prescribed tape admits a physical demand/supply assignment whose native row consumes
its entire predicted prefix. Unvisited or non-owned values stay fixed. -/
theorem realize_tape (tape : ℕ → Bool) :
    ∃ x z, D.KeepsExterior x z ∧
      (∀ p, (D.body p).map Position.routed = ((D.withWords x z).body p).map Position.routed) ∧
      rowChoices packetTrialValid (D.withWords x z).choices =
        segment tape 0 (offset D.privateWidth (packetTrials n d blocks)) := by
  classical
  let modes (p : Packet n d blocks) := bodyModes b s (D.select p) D.axis (ownerBit D.axis p.1.2 D.high)
  let rank (p : Packet n d blocks) (hp : p.1.1 D.axis = D.pair) :=
    ((packetRowEquiv D.axis D.pair).symm ⟨p,hp⟩).val
  let rect (p : Packet n d blocks) := bodyPositions (b := b) (s := s) (D.select p) D.axis (ownerBit D.axis p.1.2 D.high)
  have draw (p : Packet n d blocks) :
      ∃ x z, (p.1.1 D.axis ≠ D.pair → x = D.demand p ∧ z = D.supply p) ∧
        (∀ e j, finTwoEquiv ((if e.2 then stop e.1 else start e.1) D.axis) ≠ ownerBit D.axis p.1.2 D.high →
          x e j = D.demand p e j) ∧
        (∀ e j, e.2 = D.axis ∨ finTwoEquiv (e.1 D.axis) ≠ ownerBit D.axis p.1.2 D.high → z e j = D.supply p e j) ∧
        (D.body p).map Position.routed = (rect p x z).map Position.routed ∧
        ∀ hp : p.1.1 D.axis = D.pair, (rect p x z).map Position.digit =
          fill tape (offset D.privateWidth (rank p hp).val) (modes p) := by
    by_cases hp : p.1.1 D.axis = D.pair
    · have read := fill_spec tape (offset D.privateWidth (rank p hp).val) (modes p)
      obtain ⟨x,z,ds,hx,hz,agree⟩ := bodyDigits_recover (D.select p) D.axis (ownerBit D.axis p.1.2 D.high)
        _ read.1 (D.demand p) (D.supply p)
      exact ⟨x,z,fun no => (no hp).elim,hx,hz,agree,fun _ => ds⟩
    · exact ⟨_,_,fun _ => ⟨rfl,rfl⟩,fun _ _ _ => rfl,fun _ _ _ => rfl,rfl,fun h => (hp h).elim⟩
  choose x z unchanged hx hz routed digits using draw
  refine ⟨x,z,fun p => ⟨unchanged p,hx p,hz p⟩,routed,?_⟩
  apply row_segment
  intro t
  by_cases ok : packetTrialValid t
  · let p := D.packet t ok
    have hp : p.1.1 D.axis = D.pair := (packetRowEquiv D.axis D.pair ⟨t,ok⟩).property
    have inv : rank p hp = t := congrArg Subtype.val ((packetRowEquiv D.axis D.pair).symm_apply_apply ⟨t,ok⟩)
    have hd := digits p hp
    rw [inv] at hd
    rw [ite_eq_left ok,choices,dite_eq_left ok,privateWidth,dite_eq_left ok]
    change ((rect p (x p) (z p)).map Position.digit).flatMap Digit.choices = segment tape _ (privateCount (modes p))
    rw [hd,(fill_spec ..).2]
  · simp [ok,privateWidth,ChoiceTape.segment]

end Cube.Scatter.PacketRowData

end BorderVNP
end Computability
end OAI
