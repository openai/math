import OAI.Computability.BorderVNP.TransmissionProgram
import OAI.Computability.BorderVNP.TransmissionInverseScan

/-! # Endpoint arithmetic and physical sender agreement at a directory row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Address safety for each potentially selected role on every actual prefix memory.
A malformed row need not select a role, and sender equality is established by the
returning comparison. -/
def Range.arithmeticSafe (row : Range w) (self : Word w) (pub : Arg → Word w) (m : Memory w) : Prop :=
  ∀ mode, row.selected self = some (some mode) → ∀ bits : ℕ → Bool, ∀ j < row.width.val,
    ∀ t : Bank w, rangeBank t = row → t 0 = self → t 1 = 1 → t 2 = 0 → t 16 = Fin.ofNat _ j →
      mode.addressSafe pub t (rangeMemory mode pub (row.bank self) m bits j)

private theorem bank_atCursor (s : Bank w) (j : ℕ) (t : Bank w)
    (ht : sameRange (Function.update s 16 (Fin.ofNat _ j)) t) :
    rangeBank t = rangeBank s ∧ t 0 = s 0 ∧ t 1 = s 1 ∧ t 2 = s 2 ∧ t 16 = Fin.ofNat _ j := by
  have h (i : Reg) (hi : i.val < 16) : t i = s i :=
    (ht i hi.le).trans (Function.update_of_ne (fun he => by subst i; omega) ..)
  refine ⟨?_, h 0 (by decide), h 1 (by decide), h 2 (by decide), (ht 16 (by decide)).trans (Function.update_self ..)⟩
  simp only [rangeBank, h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide),
    h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]

/-- The frame-level bound supplies the address-safety contract used to invert a scan. -/
theorem Range.safeScan {row : Range w} {self : Word w} {pub : Arg → Word w} {m : Memory w} {s : Bank w}
    (safe : row.arithmeticSafe self pub m) (hr : rangeBank s = row)
    (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0) (mode : Role)
    (sel : decision.role s = some (some mode)) : SafeScan mode pub s m := by
  intro bits j hj t ht
  obtain ⟨hb,ha,hone,hzero,hcursor⟩ := bank_atCursor s j t ht
  have width : s 11 = row.width := congrArg Range.width hr
  rw [Range.memory_eq hr hself h1 h0]
  exact safe mode ((Range.role_eq hr hself h1 h0).symm.trans sel) bits j (width ▸ hj) t
    (hb.trans hr) (ha.trans hself) (hone.trans h1) (hzero.trans h0) hcursor

/-- A returned scan verifies the sender's equality for the descriptor, independently of
the scratch registers chosen to read that descriptor. -/
theorem Range.allowed_of_ready {row : Range w} {self : Word w} {pub : Arg → Word w} {m : Memory w}
    {s : Bank w} {bits : ℕ → Bool} {role : Option Role}
    (safe : row.arithmeticSafe self pub m) (hr : rangeBank s = row)
    (hself : s 0 = self) (h1 : s 1 = 1) (h0 : s 2 = 0)
    (sel : row.selected self = some role) (ok : Ready role pub s m bits) :
    row.allowed self pub m bits := by
  refine ⟨role,sel, ?_⟩
  intro mode he j hj t ht hteam hone hzero hoff
  subst role
  have hs := safe mode sel bits j hj t ht hteam hone hzero hoff
  cases mode with
  | sharedHere | dataHere | receiveA | receiveB => exact hs
  | sendData =>
    refine ⟨hs, ?_⟩
    let v := Function.update s 16 (Fin.ofNat _ j)
    have width : s 11 = row.width := congrArg Range.width hr
    have hcheck := (ok .sendData rfl j (width ▸ hj) v (fun _ _ => rfl)).2
    have hv : rangeBank v = row := (bank_atCursor s j v (fun _ _ => rfl)).1.trans hr
    have heq := ht.trans hv.symm
    have h10 : t 10 = v 10 := congrArg Range.teamB heq
    have h12 : t 12 = v 12 := congrArg Range.source heq
    have h15 : t 15 = v 15 := congrArg Range.ordinal heq
    have h16 : t 16 = v 16 := by simpa [v] using hoff
    rw [Range.memory_eq hr hself h1 h0] at hcheck
    simpa only [endpointNat_eq, h10, h12, h15, h16] using hcheck

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
