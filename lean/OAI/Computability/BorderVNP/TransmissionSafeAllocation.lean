import OAI.Computability.BorderVNP.TransmissionReady

/-! # Read-only schedule allocation and the exact sender acceptance condition -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Exclusive upper bound on the routing frame, cubic offsets and oriented totals. -/
def scheduleCeiling (pub : Arg → ℕ) (mem : ℕ → ℕ) (R : ℕ) : ℕ :=
  max (pub 0+26) (max (frameField pub mem 17+R^3) (frameField pub mem 18+R^2))

private theorem two_digits_lt {a b R : ℕ} (ha : a < R) (hb : b < R) : a*R+b < R^2 :=
  calc a*R+b < a*R+R := Nat.add_lt_add_left hb _
       _ = (a+1)*R := (Nat.succ_mul ..).symm
       _ ≤ R^2 := by simpa only [pow_two] using Nat.mul_le_mul_right R ha

/-- All actually addressed schedule words lie below the aggregate allocation bound. -/
theorem scheduleRead_lt_ceiling {pub : Arg → ℕ} {mem : ℕ → ℕ} {R a : ℕ}
    (hr : scheduleRead pub mem R a) : a < scheduleCeiling pub mem R := by
  rcases hr with ⟨i,hi,rfl⟩ | ⟨u,v,j,rfl⟩ | ⟨u,v,rfl⟩
  · unfold scheduleCeiling
    omega
  · have uv := two_digits_lt u.isLt v.isLt
    have span : (u.val*R+v.val)*R+j.val < R^3 :=
      calc (u.val*R+v.val)*R+j.val < (u.val*R+v.val)*R+R := Nat.add_lt_add_left j.isLt _
           _ = (u.val*R+v.val+1)*R := (Nat.succ_mul ..).symm
           _ ≤ R^3 := by simpa only [pow_succ R 2] using Nat.mul_le_mul_right R uv
    unfold tripleIndex scheduleCeiling
    omega
  · have uv := two_digits_lt u.isLt v.isLt
    unfold pairIndex scheduleCeiling
    omega

/-- Placing the written cell-input ranges after the routing tables establishes
disjointness for every intermediate lookup without any hypothesis about its execution. -/
theorem Range.scheduleSeparated_of_above (r : Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (teams : ℕ)
    (bounds : ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
      scheduleCeiling (readings pub) (readings m) teams ≤ (r.bank self d).val ∧
        (r.bank self d).val+r.width.val ≤ 2^w) : r.scheduleSeparated self pub m teams := by
  intro mode sel d hd
  obtain ⟨lo, fit⟩ := bounds mode sel d hd
  exact ⟨fit, fun _ h => Or.inl ((scheduleRead_lt_ceiling h).trans_le lo)⟩

/-- Any accepted row forces the explicit physical sender checks, bit for bit. -/
theorem Range.senderMatches_of_allowed {r : Range w} {self : Word w} {pub : Arg → Word w}
    {m : Memory w} {bits : ℕ → Bool} (ok : r.allowed self pub m bits)
    (fit : r.selected self = some (some .sendData) → r.source.val+r.width.val ≤ 2^w) :
    r.senderMatches self pub m := by
  intro hs j hj
  obtain ⟨role, sel, permits⟩ := ok
  have hr : role = some .sendData := Option.some.inj (sel.symm.trans hs)
  let t := Function.update (r.bank self) (16 : Reg) (Fin.ofNat _ j)
  have row : rangeBank t = r := by cases r; rfl
  have permit := permits .sendData hr j hj t row rfl rfl rfl (Function.update_self ..)
  rw [rangeMemory_send] at permit
  have matchBit := permit.2
  have ht : (t 16).val = j := by rw [show t 16 = Fin.ofNat _ j from Function.update_self ..,
    Fin.val_ofNat, Nat.mod_eq_of_lt (hj.trans r.width.isLt)]
  have h12 : (t 12).val = r.source.val := rfl
  have h10 : (t 10).val = r.teamB.val := rfl
  have h15 : (t 15).val = r.ordinal.val := rfl
  rw [Fin.val_add, h12, ht, Nat.mod_eq_of_lt (by have := fit hs; omega), endpointNat_eq] at matchBit
  simpa only [Range.senderAddress, h10, h15, ht] using matchBit

/-- Under the checked schedule and numeric allocations, the sole remaining acceptance
condition is comparison with the prescribed source bits on a transmitting team. -/
theorem Range.allowed_iff_senderMatches {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m : Memory w} {r : Range w} (a : Schedule f width pub m)
    (span : ScheduledRange f width r) (self : Word w) (hs : self.val = f.team)
    (kind : r.kind = 0 ∨ r.kind = 1) (sep : r.scheduleSeparated self pub m f.teams)
    (sourceFit : r.selected self = some (some .sendData) → r.source.val+r.width.val ≤ 2^w)
    (bits : ℕ → Bool) : r.allowed self pub m bits ↔ r.senderMatches self pub m :=
  ⟨fun h => Range.senderMatches_of_allowed h sourceFit, fun h =>
    r.allowed_of_tables a span self hs kind sep sourceFit h bits⟩

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
