import OAI.Computability.BorderVNP.TransmissionTableSafety

/-!
# Sender acceptance is independent of preceding local choices

The sender reads an origin and an exterior input selected by an immutable routing table.
Only destination slots are writable during the sparse directory scan. Protecting those two
input regions fixes the acceptance of a sender row before any locally shared bits are guessed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM
open private selected_remote remote peerWord from OAI.Computability.BorderVNP.TransmissionSafe

variable {w : ℕ}

/-- For a data sender, the local team is the first endpoint and the second endpoint differs. -/
theorem Range.sender_endpoints {r : Range w} {self : Word w}
    (sel : r.selected self = some (some .sendData)) : self = r.teamA ∧ r.teamA ≠ r.teamB := by
  obtain ⟨hne, ha | hb⟩ := selected_remote sel (by trivial)
  · exact ⟨ha.1,hne⟩
  · exact (hne (show r.teamB = r.teamA from hb.2).symm).elim

/-- An immutable schedule gives the same physical address for an arbitrary fitted relay leg. -/
theorem KeepsSchedule.routedAddress {pub : Arg → ℕ} {R : ℕ} {m m' : ℕ → ℕ}
    (keep : KeepsSchedule pub R m m') (teams : frameField pub m 1 = R)
    (u v y : Fin R) (q : ℕ) :
    routedAddress pub m' u v y q = routedAddress pub m u v y q := by
  have hfront : m' (tripleIndex (frameField pub m 17) R u v y) = m _ :=
    keep _ (.inr (.inl ⟨u,v,y,rfl⟩))
  have htotal : m' (pairIndex (frameField pub m 18) R v u) = m _ :=
    keep _ (.inr (.inr ⟨v,u,rfl⟩))
  simp only [BorderVNP.RoutingISA.routedAddress, legPosition, keep.field (by decide : 0 ≤ 25),
    keep.field (by decide : 1 ≤ 25), keep.field (by decide : 3 ≤ 25), keep.field (by decide : 4 ≤ 25),
    keep.field (by decide : 5 ≤ 25), keep.field (by decide : 17 ≤ 25),
    keep.field (by decide : 18 ≤ 25), teams, hfront, htotal]

/-- Any earlier writes outside the routing schedule leave the actual endpoint selected for
a sender at the same address, including the ordinal division and the cyclic relay choice. -/
theorem Range.senderAddress_of_keeps {r : Range w} {pub : Arg → Word w} {m m' : Memory w}
    {f : BroadcastFrame} (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (keep : KeepsSchedule (readings pub) f.teams (readings m) (readings m'))
    (self : Word w) (hs : self.val = f.team) (sel : r.selected self = some (some .sendData))
    (hB : r.teamB.val < f.teams) (j : ℕ) :
    r.senderAddress pub m' j = r.senderAddress pub m j := by
  obtain ⟨rfl, hd⟩ := r.sender_endpoints sel
  let u : Fin f.teams := ⟨f.team,fit.own⟩
  let v : Fin f.teams := ⟨r.teamB.val,hB⟩
  have huv : u ≠ v := fun e => hd (Fin.ext (hs.trans (congrArg Fin.val e)))
  let z := Routing.relay fit.three huv (r.ordinal.val+j)
  have hrelay : endpointRelay f.teams f.team r.teamB.val (r.ordinal.val+j) = z.val :=
    endpointRelay_eq fit.three huv _
  have eq := keep.routedAddress im.2.1 u z v ((r.ordinal.val+j)/(f.teams-2))
  simpa only [Range.senderAddress, keep.field (by decide : 0 ≤ 25),
    keep.field (by decide : 1 ≤ 25), im.1, im.2.1, hrelay] using eq

/-- A protected address lies outside every destination interval actually written for
this descriptor and team. Unused destination fields are immaterial. -/
def Range.protectsCell (r : Range w) (self : Word w) (a : ℕ) : Prop :=
  ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
    (r.bank self d).val+r.width.val ≤ 2^w ∧
      (a < (r.bank self d).val ∨ (r.bank self d).val+r.width.val ≤ a)

private theorem Range.apply_protected {r : Range w} {self : Word w} {a : ℕ}
    (protect : r.protectsCell self a) (pub : Arg → Word w) (m : Memory w) (bits : ℕ → Bool) :
    r.apply self pub m bits a = m a := by
  cases sel : r.selected self with
  | none => simp [Range.apply,sel]
  | some role =>
    cases role with
    | none => simp [Range.apply,sel,finishedMemory]
    | some mode =>
      simp only [Range.apply, sel, Option.elim_some, finishedMemory]
      exact rangeMemory_eq_of_outside mode pub (r.bank self) m bits r.width.val a
        (fun d hd => (protect mode sel d hd).1) (fun d hd => (protect mode sel d hd).2)

/-- A directory prefix preserves a protected source or exterior bit through the true
memory changes of every earlier incident row. -/
theorem tableMemory_protected (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (bits : ℕ → ℕ → Bool) (k a : ℕ)
    (protect : ∀ i < k, (rows i).protectsCell self a) : tableMemory rows self pub m bits k a = m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (Range.apply_protected (protect k (by omega)) pub _ _).trans (ih fun i hi => protect i (by omega))

/-- The sender constraints in the prefix memory equal the constraints on the original
literal/substitution and physical wire words when their two read addresses are protected. -/
theorem table_senderMatches_stable {f : BroadcastFrame} (rows : ℕ → Range w) (self : Word w)
    (pub : Arg → Word w) (m : Memory w) (bits : ℕ → ℕ → Bool) (k : ℕ)
    (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val) (hs : self.val = f.team)
    (sep : ∀ i < k, (rows i).scheduleSeparated self pub m f.teams)
    (peer : (rows k).teamB.val < f.teams)
    (protect : (rows k).selected self = some (some .sendData) → ∀ j < (rows k).width.val,
      ∀ i < k, (rows i).protectsCell self ((rows k).source.val+j) ∧
        (rows i).protectsCell self ((rows k).senderAddress pub m j)) :
    (rows k).senderMatches self pub (tableMemory rows self pub m bits k) ↔
      (rows k).senderMatches self pub m := by
  have keep := tableMemory_keepsSchedule rows self pub m bits f.teams k sep
  apply forall_congr'
  intro sel
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [Range.senderAddress_of_keeps im fit keep self hs sel peer j,
    tableMemory_protected rows self pub m bits k ((rows k).source.val+j) (fun i hi => (protect sel j hj i hi).1),
    tableMemory_protected rows self pub m bits k ((rows k).senderAddress pub m j) (fun i hi => (protect sel j hj i hi).2)]

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
