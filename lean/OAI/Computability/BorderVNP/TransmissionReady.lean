import OAI.Computability.BorderVNP.TransmissionSafe
import OAI.Computability.BorderVNP.TransmissionRowSafety

/-!
# Actual bit acceptance on a scheduled native range

The only physical data test beyond the address and allocation conditions is the
sender's equality between the prepared source word and its exterior-link bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The destinations written in each active role fit and do not overlap the routing
frame, prefix table, or oriented-load table. Other regions need no allocation here. -/
def Range.scheduleSeparated (r : Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (teams : ℕ) : Prop :=
  ∀ mode, r.selected self = some (some mode) → ∀ d ∈ mode.destinations,
    (r.bank self d).val+r.width.val ≤ 2^w ∧
      ∀ a, scheduleRead (readings pub) (readings m) teams a →
        a < (r.bank self d).val ∨ (r.bank self d).val+r.width.val ≤ a

/-- Every selected role and every genuine in-range offset has safe endpoint arithmetic.
This includes intermediate memory after all earlier updates in this range. -/
theorem Range.arithmeticSafe_of_tables {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m : Memory w} {r : Range w} (a : Schedule f width pub m)
    (span : ScheduledRange f width r) (self : Word w) (hs : self.val = f.team)
    (sep : r.scheduleSeparated self pub m f.teams) : r.arithmeticSafe self pub m := by
  intro mode sel bits j hj t row _ _ _ hjreg
  have h11 : r.bank self 11 = r.width := rfl
  have hk : j ≤ (r.bank self 11).val := h11 ▸ hj.le
  have keep := rangeMemory_keepsSchedule (R := f.teams) mode pub (r.bank self) m bits j hk
    (fun d hd => h11 ▸ (sep mode sel d hd).1)
    (fun addr haddr d hd => h11 ▸ (sep mode sel d hd).2 addr haddr)
  have hjw : j < 2^w := hj.trans r.width.isLt
  apply Role.addressSafe_of_schedule (a.of_keeps keep) span self hs mode sel t row
  simpa only [hjreg, Fin.val_ofNat, Nat.mod_eq_of_lt hjw] using hj

/-- Address of the physical relay bit against which a data sender compares its origin,
computed from the ordinal and the real immutable offset tables. -/
def Range.senderAddress (r : Range w) (pub : Arg → Word w) (m : Memory w) (j : ℕ) : ℕ :=
  let p := readings pub
  let a := readings m
  let me := frameField p a 0
  let R := frameField p a 1
  let ordinal := r.ordinal.val+j
  routedAddress p a me (endpointRelay R me r.teamB.val ordinal) r.teamB.val (ordinal/(R-2))

/-- A sending data row must agree at every bit with the exterior endpoint words chosen
for this contraction. These are the actual fields tested by the native sender. -/
def Range.senderMatches (r : Range w) (self : Word w) (pub : Arg → Word w) (m : Memory w) : Prop :=
  r.selected self = some (some .sendData) → ∀ j < r.width.val,
    m (r.source.val+j) = m (r.senderAddress pub m j)

/-- A descriptor with either allowed kind always selects a well-defined action, including
a skipped action when the caller is neither of the two endpoints. -/
theorem Range.selected_of_kind (r : Range w) (self : Word w) (hk : r.kind = 0 ∨ r.kind = 1) :
    ∃ role, r.selected self = some role := by
  change ∃ role : Option Role, (if r.kind = 0 then
    (if self = r.teamA then (if r.teamA = r.teamB then some (some .sharedHere) else some (some .receiveA))
     else (if self = r.teamB then some (some .receiveB) else some none))
    else if r.kind = 1 then
      (if self = r.teamA then (if r.teamA = r.teamB then some (some .dataHere) else some (some .sendData))
       else (if self = r.teamB then some (some .receiveB) else some none))
    else none) = some role
  split_ifs <;> simp_all

private theorem sender_check {pub : Arg → Word w} {m : Memory w} {r : Range w}
    {self : Word w} {t : Bank w} {j : ℕ} (row : rangeBank t = r)
    (hj : j < r.width.val) (h16 : t 16 = Fin.ofNat _ j)
    (fit : r.source.val+r.width.val ≤ 2^w)
    (sel : r.selected self = some (some .sendData)) (hmatch : r.senderMatches self pub m) :
    m (t 12+t 16).val = m (endpointNat 10 pub t m) := by
  have src : (t 12).val = r.source.val := congrArg (fun (s : Range w) => s.source.val) row
  have peer : (t 10).val = r.teamB.val := congrArg (fun (s : Range w) => s.teamB.val) row
  have ord : (t 15).val = r.ordinal.val := congrArg (fun (s : Range w) => s.ordinal.val) row
  have cursor : (t 16).val = j := by rw [h16, Fin.val_ofNat, Nat.mod_eq_of_lt (hj.trans r.width.isLt)]
  rw [Fin.val_add, src, cursor, Nat.mod_eq_of_lt (by omega), endpointNat_eq]
  simpa only [ord, cursor, peer, Range.senderAddress] using hmatch sel j hj

/-- Concrete table bounds and disjoint destinations imply the exact row acceptance
hypothesis of the native forward interpreter, whenever the prescribed sender check holds. -/
theorem Range.allowed_of_tables {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    {pub : Arg → Word w} {m : Memory w} {r : Range w} (a : Schedule f width pub m)
    (span : ScheduledRange f width r) (self : Word w) (hs : self.val = f.team)
    (kind : r.kind = 0 ∨ r.kind = 1) (sep : r.scheduleSeparated self pub m f.teams)
    (sourceFit : r.selected self = some (some .sendData) → r.source.val+r.width.val ≤ 2^w)
    (hmatch : r.senderMatches self pub m) (bits : ℕ → Bool) : r.allowed self pub m bits := by
  have safe := r.arithmeticSafe_of_tables a span self hs sep
  obtain ⟨role,select⟩ := r.selected_of_kind self kind
  refine ⟨role,select,?_⟩
  rintro mode rfl j hj t row team one zero cursor
  have harith := safe mode select bits j hj t row team one zero cursor
  cases mode with
  | sendData =>
    rw [rangeMemory_send] at harith ⊢
    exact ⟨harith, sender_check row hj cursor (sourceFit select) select hmatch⟩
  | receiveA | receiveB | dataHere | sharedHere => exact harith

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
