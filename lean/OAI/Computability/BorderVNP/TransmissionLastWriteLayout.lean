import OAI.Computability.BorderVNP.TransmissionLastWrite
import OAI.Computability.BorderVNP.TransmissionSenderStable

/-! # Last writers from disjoint allocated destination intervals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM
open private dest_ne_cursor from OAI.Computability.BorderVNP.TransmissionReadPreservation

variable {w : ℕ}

private theorem writes_iff_mem (mode : Role) (s : Bank w) (a : ℕ) :
    mode.writes s a ↔ ∃ d ∈ mode.destinations, a = (s d + s 16).val := by
  cases mode <;> simp [Role.writes,Role.destinations,or_and_right,exists_or]

/-- For a fitted slot, the actual write set is the list of selected destination bases
translated by the ordinary natural offset. -/
theorem Role.writes_bitBank_iff (mode : Role) (r : Range w) (team : Word w) {k a : ℕ}
    (hk : k < r.width.val)
    (fit : ∀ d ∈ mode.destinations, (r.bank team d).val + r.width.val ≤ 2^w) :
    mode.writes (r.bitBank team k) a ↔ ∃ d ∈ mode.destinations, a = (r.bank team d).val + k := by
  rw [writes_iff_mem]
  have addr (d : Reg) (hd : d ∈ mode.destinations) :
      (r.bitBank team k d + r.bitBank team k 16).val = (r.bank team d).val + k := by
    have room := fit d hd
    simp only [Range.bitBank,Function.update_of_ne (dest_ne_cursor hd),Function.update_self,
      Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (hk.trans r.width.isLt),Nat.mod_eq_of_lt (by omega :
        (r.bank team d).val + k < 2^w)]
  exact ⟨fun ⟨d,hd,h⟩ => ⟨d,hd,h.trans (addr d hd)⟩,
    fun ⟨d,hd,h⟩ => ⟨d,hd,h.trans (addr d hd).symm⟩⟩

/-- An allocated read-only cell is absent from every selected in-range bit handler's
physical write set. -/
theorem Range.protectsCell.not_writes {r : Range w} {team : Word w} {a k : ℕ}
    (protect : r.protectsCell team a) {mode : Role} (sel : r.selected team = some (some mode))
    (hk : k < r.width.val) : ¬mode.writes (r.bitBank team k) a := by
  rw [mode.writes_bitBank_iff r team hk (fun d hd => (protect mode sel d hd).1)]
  rintro ⟨d,hd,h⟩
  have := (protect mode sel d hd).2
  omega

/-- Natural interval layout certifies the last writer of a consumer slot. A co-located
wire may use exactly the same base for its two destinations. Every other destination in
the row must be disjoint from the nominated span, and subsequent rows must protect the slot. -/
theorem LastWrite.of_intervals {rows : ℕ → Range w} {team : Word w} {count i : ℕ}
    {mode : Role} {j a : ℕ} (row_lt : i < count) (slot_lt : j < (rows i).width.val)
    (sel : (rows i).selected team = some (some mode)) (d : Reg) (hd : d ∈ mode.destinations)
    (address : a = ((rows i).bank team d).val + j)
    (fit : ∀ e ∈ mode.destinations, ((rows i).bank team e).val + (rows i).width.val ≤ 2^w)
    (apart : ∀ e ∈ mode.destinations,
      ((rows i).bank team e).val = ((rows i).bank team d).val ∨
      ((rows i).bank team e).val + (rows i).width.val ≤ ((rows i).bank team d).val ∨
      ((rows i).bank team d).val + (rows i).width.val ≤ ((rows i).bank team e).val)
    (later : ∀ n, i < n → n < count → (rows n).protectsCell team a) :
    LastWrite rows team count i mode j a := by
  refine ⟨row_lt,slot_lt,sel,(mode.writes_bitBank_iff (rows i) team slot_lt fit).mpr ⟨d,hd,address⟩,?_,?_⟩
  · intro k hjk hk
    rw [mode.writes_bitBank_iff (rows i) team hk fit]
    rintro ⟨e,he,ha⟩
    have := apart e he
    omega
  · intro n hin hn next hnext k hk
    exact (later n hin hn).not_writes hnext hk

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
