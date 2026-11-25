import OAI.Computability.BorderVNP.PackedCells
import Mathlib.Data.Fin.Embedding

/-! # Uniform directed neighbor cables in Proposition 7.2

On each allowed directed neighbor pair a single public cable carries a word of width
`H`. The local tables read the private subwords and pin every unused bit to zero at
both endpoints. Thus the directory and the public cable widths depend only on the host.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped Classical
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {Q : Type} [Fintype Q] (source target : Q → N.Site) (H : ℕ)

/-- The public directory has one equal-width cable for each directed host channel.
External ports and site positions keep the numbering of the cell network. -/
abbrev uniformGrid : Network D P bits where
  Site := N.Site
  Edge := Q
  finiteSite := N.finiteSite
  finiteEdge := inferInstance
  src := source
  dst := target
  width := fun _ => H
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

/-- A private assignment of fine wires to public channels. Each fine wire uses a
channel with precisely its endpoints, and the full bit load fits on the public cable. -/
structure ChannelPacking where
  /-- Which public cable carries a fine wire. -/
  channel : N.Edge → Q
  /-- The fine source is the initial public endpoint. -/
  src_eq : ∀ e, source (channel e) = N.src e
  /-- The fine target is the terminal public endpoint. -/
  dst_eq : ∀ e, target (channel e) = N.dst e
  /-- A channel can accommodate all its bits, counting every wire at its own width. -/
  load_le : ∀ q, (∑ e : {e : N.Edge // channel e = q}, N.width e.val) ≤ H

variable {N source target H}

namespace ChannelPacking

variable (c : N.ChannelPacking source target H)

private abbrev WireBit := (e : N.Edge) × Fin (N.width e)
private abbrev FiberBit (q : Q) := {p : WireBit (N := N) // c.channel p.1 = q}

private def bitsEquiv (q : Q) : c.FiberBit q ≃
    ((e : {e : N.Edge // c.channel e = q}) × Fin (N.width e.val)) where
  toFun p := ⟨⟨p.val.1, p.property⟩, p.val.2⟩
  invFun p := ⟨⟨p.1.val, p.2⟩, p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def slot (q : Q) : c.FiberBit q ↪ Fin H :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by
    rw [Fintype.card_congr (c.bitsEquiv q), Fintype.card_sigma]
    simpa using c.load_le q))

/-- Each original bit receives a distinct public address on its own directed channel. -/
noncomputable def address : ((e : N.Edge) × Fin (N.width e)) ↪ Q × Fin H :=
  ((Equiv.sigmaFiberEquiv (fun p : WireBit (N := N) => c.channel p.1)).symm.toEmbedding.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl Q) c.slot)).trans
      (Equiv.sigmaEquivProd Q (Fin H)).toEmbedding

/-- Fill used addresses from the private assignment, and all other addresses with zero. -/
noncomputable def pack (a : N.Assignment) : (N.uniformGrid source target H).Assignment :=
  fun q i => Function.extend c.address (fun p => a p.1 p.2) (fun _ => false) (q,i)

/-- Read every private wire word at its address on the assigned public cable. -/
noncomputable def unpack (z : (N.uniformGrid source target H).Assignment) : N.Assignment :=
  fun e i => z (c.channel e) (c.address ⟨e,i⟩).2

/-- Packing and then reading a private wire recovers its entire word. -/
theorem unpack_pack (a : N.Assignment) : c.unpack (c.pack a) = a := by
  funext e i
  exact c.address.injective.extend_apply (fun p => a p.1 p.2) (fun _ => false) ⟨e,i⟩

/-- The unused positions of this channel must carry zero. -/
def ZeroPad (q : Q) (word : Fin H → Bool) : Prop :=
  ∀ i, (q,i) ∉ Set.range c.address → word i = false

/-- A padded global assignment is precisely the packed version of its private words. -/
theorem zeroPad_iff (z : (N.uniformGrid source target H).Assignment) :
    (∀ q, c.ZeroPad q (z q)) ↔ z = c.pack (c.unpack z) := by
  constructor
  · intro hz
    funext q i
    by_cases h : (q,i) ∈ Set.range c.address
    · obtain ⟨p, hp⟩ := h
      change Function.uncurry z (q,i) = Function.extend c.address _ _ (q,i)
      rw [← hp, c.address.injective.extend_apply]
      rfl
    · exact (hz q i h).trans (Function.extend_apply' (f := c.address) (fun p => c.unpack z p.1 p.2) (fun _ => false) (q,i) h).symm
  · intro hz q i hi
    rw [show z q i = c.pack (c.unpack z) q i from congrFun (congrFun hz q) i]
    exact Function.extend_apply' (f := c.address) (fun p => c.unpack z p.1 p.2) (fun _ => false) (q,i) hi

variable {R : Type*} [CommSemiring R]

/-- At a cell each incident cable is checked for zero padding. The cell then evaluates
its original table on its incident subwords and its own external ports. -/
noncomputable def tables (table : N.Tables R) : (N.uniformGrid source target H).Tables R :=
  fun v a x =>
    if ∀ q : {q : Q // source q = v ∨ target q = v}, c.ZeroPad q.val (a q) then
      table v (fun e i => a ⟨c.channel e.val,
        e.property.imp ((c.src_eq e.val).trans) ((c.dst_eq e.val).trans)⟩ (c.address ⟨e.val,i⟩).2) x
    else 0

private theorem prod_tables (table : N.Tables R) (z : (N.uniformGrid source target H).Assignment)
    (x : Ports bits) :
    (∏ v, (N.uniformGrid source target H).read (c.tables table) z x v) =
      if ∀ q, c.ZeroPad q (z q) then ∏ v, N.read table (c.unpack z) x v else 0 := by
  classical
  by_cases h : ∀ q, c.ZeroPad q (z q)
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    exact ite_eq_left (fun q : {q : Q // source q = v ∨ target q = v} => h q.val)
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨q,hq⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ (source q))
    exact ite_eq_right (fun hall => hq (hall ⟨q, Or.inl rfl⟩))

/-- Bundling parallel fine wires into one padded cable per allowed directed neighbor
preserves every tensor entry, in particular over any polynomial semiring of private entries. -/
theorem value_uniformGrid (table : N.Tables R) (x : Ports bits) :
    (N.uniformGrid source target H).value (c.tables table) x = N.value table x := by
  classical
  unfold value
  simp_rw [c.prod_tables]
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter (fun z => ∀ q, c.ZeroPad q (z q)) =
      Finset.univ.image c.pack := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨c.unpack z, ((c.zeroPad_iff z).mp hz).symm⟩
    · rintro ⟨a, rfl⟩
      exact (c.zeroPad_iff _).mpr (congrArg c.pack (c.unpack_pack a).symm)
  have inj : Function.Injective c.pack := fun a b hab =>
    (c.unpack_pack a).symm.trans ((congrArg c.unpack hab).trans (c.unpack_pack b))
  rw [himg, Finset.sum_image inj.injOn]
  simp_rw [c.unpack_pack]

end ChannelPacking

end Crossing.Network

end BorderVNP
end Computability
end OAI
