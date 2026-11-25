import OAI.Computability.BorderVNP.PackedBankInheritedCharges

/-! # Exact tie count at an inherited site of a selected crossing

Old incident cable–band pairs are in bijection with the live successor wires
read by the old table. A cut self-loop uses its source hook. Every attached
external port contributes one additional tie.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep Shortening.SeedIntervals Inherited
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
  (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm) (v : p.layout.Site)

private noncomputable abbrev L := (output e p bin perm positive first q).layout
private noncomputable abbrev selected := (partition p.layout bin perm m).selected

/-- The live wire IDs tied to the inherited slab at this old site. -/
abbrev TiedWires := {c : (L e p bin perm positive first q).Edge //
  gathered e p bin perm positive first q (.inl v) c ∧
    ((L e p bin perm positive first q).src c = .inl v ∨ (L e p bin perm positive first q).dst c = .inl v)}

private noncomputable def toTie (z : Incident p.layout v × Band D) :
    TiedWires e p bin perm positive first q v :=
  let wire := oldBandWire e p bin perm positive first q v z.1 z.2
  ⟨wire.val,by
    dsimp only [wire]
    unfold oldBandWire
    split
    · split
      · exact trivial
      · assumption
    · exact trivial,wire.property⟩

/-- Every distinct old cable–band pair names exactly one tied physical successor
wire at this site, including empty bands and the source side of a cut loop. -/
noncomputable def tiedWiresEquiv : (Incident p.layout v × Band D) ≃ TiedWires e p bin perm positive first q v := by
  apply Equiv.ofBijective (toTie e p bin perm positive first q v)
  constructor
  · intro s t h
    apply oldBandWire_injective e p bin perm positive first q v
    exact Subtype.ext (congrArg (fun z : TiedWires e p bin perm positive first q v => z.val) h)
  · rintro ⟨wire,hok,hat⟩
    rcases wire with (c | c) | c | z
    · have hs : p.layout.src c.val.1 = v := by
        rcases hat with hs | hd
        · exact Sum.inl.inj hs
        · cases hd
      refine ⟨(⟨c.val.1,Or.inl hs⟩,c.val.2),Subtype.ext ?_⟩
      have hmem : (c.val.1,c.val.2) ∈ selected (m := m) p bin perm := c.property
      simp only [toTie,oldBandWire,dite_eq_left hmem,dite_eq_left hs]
      rfl
    · have hd : p.layout.dst c.val.1 = v := by
        rcases hat with hd | h
        · exact Sum.inl.inj hd
        · cases h
      have hs : p.layout.src c.val.1 ≠ v := hok
      refine ⟨(⟨c.val.1,Or.inr hd⟩,c.val.2),Subtype.ext ?_⟩
      have hmem : (c.val.1,c.val.2) ∈ selected (m := m) p bin perm := c.property
      simp only [toTie,oldBandWire,dite_eq_left hmem,dite_eq_right hs]
      rfl
    · have hinc : p.layout.src c.val.1 = v ∨ p.layout.dst c.val.1 = v :=
        hat.imp Sum.inl.inj Sum.inl.inj
      refine ⟨(⟨c.val.1,hinc⟩,c.val.2),Subtype.ext ?_⟩
      have hmem : (c.val.1,c.val.2) ∉ selected (m := m) p bin perm := c.property
      simp only [toTie,oldBandWire,dite_eq_right hmem]
      rfl
    · exact False.elim hok

/-- Exact number of inherited band ties and external-port ties charged at the
old site, expressed in terms of its original local packet. -/
theorem old_tieRows [Fintype P] :
    tieRows (L e p bin perm positive first q) (gathered e p bin perm positive first q (.inl v)) (.inl v) =
      Fintype.card (Incident p.layout v) * Fintype.card (Band D) + Fintype.card {t : P // p.layout.attach t = v} := by
  let G := L e p bin perm positive first q
  let ports : {t : P // G.attach t = .inl v} ≃ {t : P // p.layout.attach t = v} :=
    Equiv.subtypeEquivRight fun _ => ⟨Sum.inl.inj,congrArg Sum.inl⟩
  have hw := Fintype.card_congr (tiedWiresEquiv e p bin perm positive first q v)
  rw [Fintype.card_prod] at hw
  exact congrArg₂ (· + ·) hw.symm (Fintype.card_congr ports)

end Packing.InheritedBank

end BorderVNP
end Computability
end OAI
