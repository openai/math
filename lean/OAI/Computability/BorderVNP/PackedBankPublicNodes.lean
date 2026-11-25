import OAI.Computability.BorderVNP.PackedBankRoundSites

/-!
# The public part of each sparse site directory

A public entry names each stored one-copy box. Its factors and sweeps are
delivered privately. The public serializer counts the row fields, wiring
guards, and box names throughout the same stable sorting and sewing history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep CellSparse InheritedBank
open scoped Classical

/-- Words and guards of the public records and one public name per opaque box. -/
def Site.publicNodes (s : Site) : ℕ :=
  (Packet.fieldList Packet.record s.rows).length + Directory.recordNodes s.rows + s.boxes.length

/-- Every serialized public row word is included in the public bound. -/
theorem Site.packetRows_le_publicNodes (s : Site) :
    (Packet.fieldList Packet.record s.rows).length ≤ s.publicNodes := by unfold publicNodes; omega

/-- The bound on the full stored program also bounds its public fields. -/
theorem Site.publicNodes_le_staticNodes (s : Site) : s.publicNodes ≤ s.staticNodes := by
  unfold publicNodes staticNodes Directory.tableNodes
  omega

/-- Adding intervals costs only their public equalities and guards. The old
opaque table contents and one-copy sweeps are carried separately. -/
theorem Site.publicNodes_retain (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).publicNodes = s.publicNodes + 1034*cuts.length := by
  have h := s.staticNodes_retain n cuts
  simp only [Site.staticNodes,s.retain_blocks,show (s.retain n cuts).boxes = s.boxes from rfl] at h
  unfold publicNodes
  rw [show (s.retain n cuts).boxes = s.boxes from rfl]
  omega

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
  (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (binName : S → ℕ) (position : e.Entry → ℕ)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

variable {ns ne np : ℕ} (siteID : (L e p bin perm positive first q).Site ↪ Fin ns)
  (edgeID : (L e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
  (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)

/-- A physical sorting and sewing stage propagates the public count even when
the immutable private arrays at retained sites are much larger than the
input public allowance. A new template site has a fixed birth charge. -/
theorem roundSites_public_charged (prior : p.layout.Site → ℕ)
    (hin : ∀ v, (old v).incoming = incoming p.layout v)
    (hold : ∀ v, (old v).publicNodes ≤ prior v)
    (hlen : ∀ v, (cuts v).length = tieRows (L e p bin perm positive first q)
      (gathered e p bin perm positive first q (.inl v)) (.inl v))
    (v : (L e p bin perm positive first q).Site) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts v).publicNodes ≤
      nextPrior e p bin perm positive first q prior v := by
  change SiteShape e p S at v
  rcases v with v | v
  · dsimp only [roundSites,nextPrior,Sum.elim_inl]
    rw [Site.publicNodes_retain,hlen]
    exact Nat.add_le_add (hold v) (Nat.mul_le_mul_right _ (by decide : 1034 ≤ 1100))
  · have hs := roundSites_charged e p bin perm positive first q binName position siteID edgeID portID old cuts
      (fun u => (old u).staticNodes) (fun u => (old u).expandedLoad) hin (fun _ => ⟨le_rfl,le_rfl⟩) hlen (.inr v)
    exact (Site.publicNodes_le_staticNodes _).trans hs.1

end Packing.Inherited

end BorderVNP
end Computability
end OAI
