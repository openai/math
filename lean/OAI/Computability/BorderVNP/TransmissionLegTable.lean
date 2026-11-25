import OAI.Computability.BorderVNP.TransmissionLegRoom
import OAI.Computability.BorderVNP.RoutingISARelayLoops
import OAI.Computability.BorderVNP.RoutingISATableOrdinalEquiv

/-! # Physical address safety from the actual transmission tables

A descriptor's loaded ordinal plus its local index belongs to its unordered
pair's demand. Every quotient inspected by a relay has an original bit on
each of the two incident legs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- The offset and total directories read after scheduling name two completely
addressable intervals, of cubic and square length respectively. -/
theorem TableLayout.Image.directoryFits {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before mem : ℕ → ℕ} (image : l.Image row before mem) (al : l.Allocated w)
    (pub : Arg → ℕ) (hf : pub 0 = l.frame) (loaded : l.frameFields before) :
    frameField pub mem 17 + l.teams^3 ≤ 2^w ∧ frameField pub mem 18 + l.teams^2 ≤ 2^w := by
  have frame (i : ℕ) (hi : i < 21) : frameField pub mem i = before (l.frame+i) := by
    rw [frameField, hf]
    have inside := l.contains_offset (a := .frame) hi
    exact image.outside _ (al.separate .frame .widths _ (by decide) inside)
      (al.separate .frame .ordinals _ (by decide) inside)
      (al.separate .frame .offsets _ (by decide) inside)
      (al.separate .frame .used _ (by decide) inside)
  rw [frame 17 (by decide), frame 18 (by decide), loaded.2.2.2.2.1, loaded.2.2.2.2.2.1]
  exact ⟨al.fits .offsets, al.fits .used⟩

/-- Every actual quotient of a scheduled pair gives two fitted addresses at its
relay, with the opposite endpoint supplying the second hop. -/
private theorem relayQuotientRooms (f : BroadcastFrame) {w : ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (im : f.At pub mem) (fit : f.Fits w (pub 0)) {width : Fin f.teams → Fin f.teams → ℕ}
    (tab : AddressTables fit.three width pub mem)
    (tripleFit : frameField pub mem 17 + f.teams^3 ≤ 2^w)
    (pairFit : frameField pub mem 18 + f.teams^2 ≤ 2^w)
    (capacity : ∀ u v, f.header + Routing.legLoad fit.three width u v +
      Routing.legLoad fit.three width v u ≤ f.capacity) (u y : Fin f.teams) (hu : u ≠ y)
    (q : ℕ) (hq : q < Routing.scheduledLength u y ⟨f.team,fit.own⟩ (Routing.demand width u y)) :
    LegRoom w pub mem u f.team y q ∧ LegRoom w pub mem y f.team u q := by
  let v : Fin f.teams := ⟨f.team,fit.own⟩
  let e := Routing.ordinalEquiv fit.three u y v (Routing.demand width u y)
  let j := e.symm ⟨q,hq⟩
  let bit : Routing.Hop fit.three width u v := ⟨y,j⟩
  have quotient : j.val / (f.teams-2) = q :=
    (Routing.ordinalEquiv_val fit.three u y v _ j).symm.trans (congrArg Fin.val (e.apply_symm_apply _))
  have path : j.val ∈ Routing.pairBits fit.three u y v (Routing.demand width u y) := j.property
  have hpath : j.val ∈ (Finset.range (Routing.demand width u y)).filter
      (fun k => Routing.relay fit.three hu k = v) := by
    simpa only [Routing.pairBits, dite_eq_left hu] using path
  have routed := (Finset.mem_filter.mp hpath).2
  have ne := Routing.relay_ne_endpoints fit.three hu j.val
  rw [routed] at ne
  rw [← quotient]
  exact ⟨hopLegRoom f im fit tab tripleFit pairFit (Or.inr rfl) ne.1.symm (capacity u v) bit,
    hopLegRoom f im fit tab tripleFit pairFit (Or.inr rfl) ne.2.symm (capacity y v)
      (Routing.otherHop fit.three width bit)⟩

/-- The native triangular loop's two-sided word-space contract follows from
the allocated table image and the physical block capacity of equation (8.2). -/
theorem TableLayout.Image.relayRooms {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before mem : ℕ → ℕ} (image : l.Image row before mem) (al : l.Allocated w)
    (pub : Arg → ℕ) (hf : pub 0 = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (im : f.At pub mem) (fit : f.Fits w (pub 0))
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity) :
    RelayRooms w l.teams (fun u y => l.partnerLength row u f.team y) pub mem f.team := by
  have tab := image.addressTables al pub hf loaded
  obtain ⟨tripleFit,pairFit⟩ := image.directoryFits al pub hf loaded
  rcases f with ⟨team,teams,processors,literal,link,header,dst⟩
  have hR : teams = l.teams := im.2.1.symm.trans tab.teams
  subst teams
  intro u hu y huy hy q hq
  let U : Fin l.teams := ⟨u,hu⟩
  let Y : Fin l.teams := ⟨y,hy⟩
  let V : Fin l.teams := ⟨team,fit.own⟩
  change q < l.partnerLength row U V Y at hq
  rw [l.partnerLength_eq row U V Y] at hq
  exact relayQuotientRooms _ im fit tab tripleFit pairFit capacity U Y
    (fun h => (Nat.ne_of_lt huy) (congrArg Fin.val h)) q hq

/-- A nonlocal descriptor's stored ordinal and local bit index are always below
the demand for its pair, in either endpoint orientation. -/
theorem TableLayout.Image.recordBit_lt_demand {l : TableLayout} {row : ℕ → TableRow}
    {before mem : ℕ → ℕ} (image : l.Image row before mem) {u y : Fin l.teams}
    (hu : u ≠ y) {i k : ℕ} (hi : i < l.count) (hk : k < (row i).width)
    (ends : (row i).first = u.val ∧ (row i).second = y.val ∨
      (row i).first = y.val ∧ (row i).second = u.val) :
    mem (l.ordinals+i)+k < Routing.demand (l.widthMatrix row) u y := by
  rw [image.ordinals i hi, Routing.demand, ite_eq_right hu]
  have ne : u.val ≠ y.val := fun e => hu (Fin.ext e)
  have hrow : (row i).first ≠ (row i).second := by
    rcases ends with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rw [ha,hb] <;> first | exact ne | exact ne.symm
  have mono : Monotone (@Fin.val l.teams) := fun _ _ e => e
  have hb := (Nat.add_lt_add_left hk (l.ordinal row i)).trans_le (l.ordinal_add_width_le row hi hrow)
  rcases ends with ⟨ha,hb'⟩ | ⟨ha,hb'⟩
  · simpa only [TableLayout.widthMatrix, TableLayout.pairKey, ha, hb', mono.map_min, mono.map_max] using hb
  · simpa only [TableLayout.widthMatrix, TableLayout.pairKey, ha, hb', mono.map_min, mono.map_max,
      min_comm y.val u.val, max_comm y.val u.val] using hb

/-- At either endpoint of a nonlocal seven-word record, the directory lookup
at the stored ordinal plus any local bit offset has word room at every step. -/
theorem TableLayout.Image.endpointRecordRoom {l : TableLayout} {row : ℕ → TableRow} {w : ℕ}
    {before mem : ℕ → ℕ} (image : l.Image row before mem) (al : l.Allocated w)
    (pub : Arg → ℕ) (hf : pub 0 = l.frame) (loaded : l.frameFields before)
    (f : BroadcastFrame) (im : f.At pub mem) (fit : f.Fits w (pub 0))
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (peer : Fin l.teams) (hd : f.team ≠ peer.val) {i k : ℕ}
    (hi : i < l.count) (hk : k < (row i).width)
    (ends : (row i).first = f.team ∧ (row i).second = peer.val ∨
      (row i).first = peer.val ∧ (row i).second = f.team) :
    let j := mem (l.ordinals+i)+k
    LegRoom w pub mem (frameField pub mem 0)
      (endpointRelay (frameField pub mem 1) (frameField pub mem 0) peer j)
      peer (j/(frameField pub mem 1-2)) := by
  have tab := image.addressTables al pub hf loaded
  obtain ⟨tripleFit,pairFit⟩ := image.directoryFits al pub hf loaded
  rcases f with ⟨team,teams,processors,literal,link,header,dst⟩
  have hR : teams = l.teams := im.2.1.symm.trans tab.teams
  subst teams
  let u : Fin l.teams := ⟨team,fit.own⟩
  exact endpointLegRoom _ im fit tab tripleFit pairFit (fun v _ => capacity u v) peer hd _
    (image.recordBit_lt_demand (u := u) (fun e => hd (congrArg Fin.val e)) hi hk ends)

end RoutingISA

end BorderVNP
end Computability
end OAI
