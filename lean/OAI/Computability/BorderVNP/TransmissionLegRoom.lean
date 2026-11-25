import OAI.Computability.BorderVNP.RoutingISAAddressFit
import OAI.Computability.BorderVNP.RoutingISAPaddingSchedule

/-! # Word-space bounds for the physical transmission legs

The offset and total tables give the exact rank in each oriented leg. Both
orientations, after the common header, fit in the physical link block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

private theorem rowMajor_lt {a b m n : ℕ} (ha : a < m) (hb : b < n) :
    a*n+b < m*n := by
  calc
    a*n+b < (a+1)*n := by rw [Nat.add_mul, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ ha

/-- A routed hop on an incident physical link fits the triple and pair tables,
the assigned two-direction block, and the initialized processor address space.
The caller can be either the endpoint or its relay. -/
theorem hopLegRoom (f : BroadcastFrame) {w : ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (im : f.At pub mem) (fit : f.Fits w (pub 0)) {width : Fin f.teams → Fin f.teams → ℕ}
    (tab : AddressTables fit.three width pub mem)
    (tripleFit : frameField pub mem 17 + f.teams^3 ≤ 2^w)
    (pairFit : frameField pub mem 18 + f.teams^2 ≤ 2^w) {u v : Fin f.teams}
    (caller : f.team = u.val ∨ f.team = v.val) (distinct : u ≠ v)
    (block : f.header + Routing.legLoad fit.three width u v +
      Routing.legLoad fit.three width v u ≤ f.capacity) (bit : Routing.Hop fit.three width u v) :
    LegRoom w pub mem u v bit.1 (bit.2.val / (f.teams-2)) := by
  obtain ⟨h0, h1, _, h3, h4, h5, _⟩ := im
  have hbase : pub 0 + 18 < 2^w := by have := fit.frame; have := fit.out; omega
  have hinput := fit.input
  have hstride : f.stride < 2^w :=
    (Nat.le_mul_of_pos_left _ fit.procs).trans_lt (by omega : f.processors*f.stride < 2^w)
  have hlink : f.link ≤ f.stride :=
    (Nat.le_mul_of_pos_left f.link (by have := fit.three; omega : 0 < f.teams-1)).trans
      (Nat.le_add_left ..)
  have hcap : f.capacity < 2^w := by
    rw [BroadcastFrame.capacity, Nat.mul_comm]
    exact (Nat.mul_le_mul_left f.processors hlink).trans_lt (by omega)
  have hteam : u.val ≠ v.val := fun e => distinct (Fin.ext e)
  let partner := if f.team = u.val then v.val else u.val
  have hp : partner < f.teams := by unfold partner; split <;> exact Fin.isLt _
  have hd : partner ≠ f.team := by
    unfold partner
    rcases caller with h | h <;> simp [h, hteam, Ne.symm hteam]
  let pos := legPosition pub mem u v bit.1 (bit.2.val / (f.teams-2))
  have hpos : pos < f.capacity := by
    dsimp only [pos]
    rw [tab.legPosition_eq, h5]
    have hr := (Routing.legEquiv fit.three width u v bit).isLt
    split <;> omega
  have ht : (u.val*f.teams+v.val)*f.teams+bit.1.val < f.teams^3 := by
    simpa only [pow_succ, pow_zero, one_mul] using
      rowMajor_lt (rowMajor_lt u.isLt v.isLt) bit.1.isLt
  have hpidx : v.val*f.teams+u.val < f.teams^2 := by
    simpa only [pow_two] using rowMajor_lt v.isLt u.isLt
  refine ⟨hbase, by rw [h1]; have := fit.three; omega, h4 ▸ fit.width, ?_, ?_, ?_, ?_,
    hpos.trans hcap, ?_⟩
  · simpa only [h0] using hd
  · simpa only [h1, h3, h4, BroadcastFrame.stride] using hstride
  · simp only [tripleIndex, h1]
    omega
  · intro _
    simp only [pairIndex, h1]
    omega
  · have ha := f.addr_lt_input fit hp hd hpos
    simpa only [routedAddress, h0, h1, h3, h4, BroadcastFrame.addr, partner, pos] using
      ha.trans_le (hinput.trans (by omega : pub 0 ≤ 2^w))

/-- The endpoint's actual cyclic relay and floor quotient select an in-range
hop for every ordinal of its demand. -/
theorem endpointLegRoom (f : BroadcastFrame) {w : ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (im : f.At pub mem) (fit : f.Fits w (pub 0)) {width : Fin f.teams → Fin f.teams → ℕ}
    (tab : AddressTables fit.three width pub mem)
    (tripleFit : frameField pub mem 17 + f.teams^3 ≤ 2^w)
    (pairFit : frameField pub mem 18 + f.teams^2 ≤ 2^w)
    (capacity : ∀ v : Fin f.teams, v.val ≠ f.team → f.usedPrefix fit width v ≤ f.capacity)
    (peer : Fin f.teams) (hd : f.team ≠ peer.val) (j : ℕ)
    (hj : j < Routing.demand width ⟨f.team,fit.own⟩ peer) :
    LegRoom w pub mem (frameField pub mem 0)
      (endpointRelay (frameField pub mem 1) (frameField pub mem 0) peer j)
      peer (j/(frameField pub mem 1-2)) := by
  let u : Fin f.teams := ⟨f.team,fit.own⟩
  have ends : u ≠ peer := fun e => hd (congrArg Fin.val e)
  let v := Routing.relay fit.three ends j
  have relay_ne : v ≠ u := (Routing.relay_ne_endpoints fit.three ends j).1
  have bit : j ∈ Routing.pairBits fit.three u peer v (Routing.demand width u peer) := by
    simpa only [Routing.pairBits, dite_eq_left ends, Finset.mem_filter, Finset.mem_range, v, and_true] using hj
  let hop : Routing.Hop fit.three width u v := ⟨peer,⟨j,bit⟩⟩
  have room := hopLegRoom f im fit tab tripleFit pairFit (Or.inl rfl) relay_ne.symm
    (capacity v (fun e => relay_ne (Fin.ext e))) hop
  rw [im.1, im.2.1, endpointRelay_eq fit.three ends]
  exact room

end RoutingISA

end BorderVNP
end Computability
end OAI
