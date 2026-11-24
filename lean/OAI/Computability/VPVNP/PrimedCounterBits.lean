import OAI.Computability.VPVNP.PrimedCounterStack
import OAI.Computability.VPVNP.RAMWordBits

/-!
# Fixed-width binary choices for a primed node

The root degree on the stack determines how many words to read. Each location,
split or child state has one little-endian encoding. A choice word outside its
required range, or a call with excess or missing bits, is rejected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM ParseGrammar

variable {n m s w : ℕ}

/-- Canonical little-endian representation of an in-range natural. -/
def digits (w k : ℕ) : List Bool := wordBits (Fin.ofNat (2^w) k)

/-- Consume a word and check the upper bound on its value. -/
def takeBounded (w bound : ℕ) (bits : List Bool) : Option (Fin bound × List Bool) := do
  let (v, tail) ← takeWord w bits
  if hv : v.val < bound then return (⟨v.val, hv⟩, tail) else none

theorem takeBounded_eq (bound : ℕ) (hfit : bound ≤ 2^w) (bits : List Bool)
    (i : Fin bound) (tail : List Bool) :
    takeBounded w bound bits = some (i, tail) ↔ bits = digits w i.val ++ tail := by
  constructor
  · intro h
    cases hr : takeWord w bits with
    | none => simp [takeBounded, hr] at h
    | some v =>
      obtain ⟨v, rest⟩ := v
      by_cases hv : v.val < bound
      · simp [takeBounded, hr, hv] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [digits] using (takeWord_eq_some_iff ..).1 hr
      · simp [takeBounded, hr, hv] at h
  · rintro rfl
    let a : Word w := ⟨i.val, i.isLt.trans_le hfit⟩
    have ha : Fin.ofNat (2^w) i.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    have hr : takeWord w (digits w i.val ++ tail) = some (a,tail) :=
      (takeWord_eq_some_iff ..).2 (by rw [digits, ha])
    simp [takeBounded, hr, a, i.isLt]

/-- Exactly the branch bits consumed in one node call. No discriminator is guessed. -/
def encodeToken (w : ℕ) : Token m (Fin s) → List Bool
  | .terminal j => digits w j.val
  | .binary b i j => digits w b ++ digits w i.val ++ digits w j.val

theorem length_encodeToken_le (t : Token m (Fin s)) : (encodeToken w t).length ≤ 3 * w := by
  cases t <;> simp [encodeToken, digits] <;> omega

/-- The dynamic range check at a node. -/
def Legal (d : ℕ) : Token m (Fin s) → Prop
  | .terminal _ => d = 0
  | .binary b _ _ => b < d

/-- Each call must exhaust precisely the choices for its pending node. -/
def readToken (w m s d : ℕ) (bits : List Bool) : Option (Token m (Fin s)) := do
  if d = 0 then
    let (j, rest) ← takeBounded w m bits
    if rest.isEmpty then return .terminal j else none
  else
    let (b, bits) ← takeBounded w d bits
    let (i, bits) ← takeBounded w s bits
    let (j, rest) ← takeBounded w s bits
    if rest.isEmpty then return .binary b.val i j else none

theorem readToken_sound (hm : m ≤ 2^w) (hs : s ≤ 2^w) {d : ℕ} (hd : d ≤ 2^w)
    {bs : List Bool} {t : Token m (Fin s)} (hr : readToken w m s d bs = some t) :
    Legal d t ∧ bs = encodeToken w t := by
  by_cases hz : d = 0
  · cases hh : takeBounded w m bs with
    | none => simp [readToken, hz, hh] at hr
    | some v =>
      obtain ⟨j, rest⟩ := v
      simp [readToken, hz, hh] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hz, by simpa [encodeToken] using (takeBounded_eq m hm bs j []).1 hh⟩
  · cases hb : takeBounded w d bs with
    | none => simp [readToken, hz, hb] at hr
    | some v =>
      obtain ⟨b, xs⟩ := v
      cases hi : takeBounded w s xs with
      | none => simp [readToken, hz, hb, hi] at hr
      | some v =>
        obtain ⟨i, ys⟩ := v
        cases hj : takeBounded w s ys with
        | none => simp [readToken, hz, hb, hi, hj] at hr
        | some v =>
          obtain ⟨j, rest⟩ := v
          simp [readToken, hz, hb, hi, hj] at hr
          obtain ⟨rfl, rfl⟩ := hr
          rw [(takeBounded_eq d hd bs b xs).1 hb, (takeBounded_eq s hs xs i ys).1 hi,
            (takeBounded_eq s hs ys j []).1 hj]
          simp [Legal, encodeToken]

theorem readToken_encode (hm : m ≤ 2^w) (hs : s ≤ 2^w) {d : ℕ} (hd : d ≤ 2^w)
    (t : Token m (Fin s)) (hl : Legal d t) :
    readToken w m s d (encodeToken w t) = some t := by
  cases t with
  | terminal j =>
    subst d
    have hr := (takeBounded_eq m hm (digits w j.val) j []).2 (by simp)
    simp [readToken, encodeToken, hr]
  | binary b i j =>
    let split : Fin d := ⟨b, hl⟩
    have hz : d ≠ 0 := by change b < d at hl; omega
    have hb := (takeBounded_eq d hd (encodeToken w (.binary b i j : Token m (Fin s))) split
      (digits w i.val ++ digits w j.val)).2 (by simp [encodeToken, split, List.append_assoc])
    have hi := (takeBounded_eq s hs (digits w i.val ++ digits w j.val) i (digits w j.val)).2 rfl
    have hj := (takeBounded_eq s hs (digits w j.val) j []).2 (by simp)
    simp [readToken, hz, hb, hi, hj, split]

/-- A successful stack operation requires a legal node choice. -/
theorem legal_of_step {x : Fin m → Bool} {f : Frame n (Fin s)} {t : Token m (Fin s)}
    {out : Label n m (Fin s) × List (Frame n (Fin s))} (hh : step x f t = some out) : Legal f.1.val t := by
  obtain ⟨⟨k, hk⟩, h⟩ := f
  cases k <;> cases t <;> simp_all [step, Legal]
  exact hh.choose

/-- Binary decoding and stack traversal together, with one branch-bit list per call. -/
def decodeVisits (w : ℕ) (x : Fin m → Bool) :
    List (Frame n (Fin s)) → List (List Bool) → Option (List (Token m (Fin s)))
  | [], [] => some []
  | [], _ :: _ | _ :: _, [] => none
  | f :: stack, bs :: more => do
    let t ← readToken w m s f.1.val bs
    let (_, children) ← step x f t
    let ts ← decodeVisits w x (children ++ stack) more
    return t :: ts

theorem decodeVisits_sound (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (stack : List (Frame n (Fin s))) (bs : List (List Bool))
    (ts : List (Token m (Fin s))) (hd : decodeVisits w x stack bs = some ts) :
    bs = ts.map (encodeToken w) ∧ (scan x stack ts).isSome := by
  induction bs generalizing stack ts with
  | nil =>
    cases stack <;> simp [decodeVisits] at hd
    subst ts
    exact ⟨rfl, rfl⟩
  | cons b bs ih =>
    cases stack with
    | nil => simp [decodeVisits] at hd
    | cons f stack =>
      cases hr : readToken w m s f.1.val b with
      | none => simp [decodeVisits, hr] at hd
      | some t =>
        cases hstep : step x f t with
        | none => simp [decodeVisits, hr, hstep] at hd
        | some v =>
          obtain ⟨a, children⟩ := v
          cases hrest : decodeVisits w x (children ++ stack) bs with
          | none => simp [decodeVisits, hr, hstep, hrest] at hd
          | some rest =>
            simp [decodeVisits, hr, hstep, hrest] at hd
            subst ts
            obtain ⟨he, hscan⟩ := ih _ _ hrest
            have he' := (readToken_sound hm hs (f.1.isLt.le.trans hn) hr).2
            refine ⟨by simp [he', he], ?_⟩
            cases hsc : scan x (children ++ stack) rest <;> simp_all [scan]

theorem decodeVisits_encode (hm : m ≤ 2^w) (hs : s ≤ 2^w) (hn : n ≤ 2^w)
    (x : Fin m → Bool) (stack : List (Frame n (Fin s))) (ts : List (Token m (Fin s)))
    (hsc : (scan x stack ts).isSome) : decodeVisits w x stack (ts.map (encodeToken w)) = some ts := by
  induction ts generalizing stack with
  | nil => cases stack <;> simp_all [scan, decodeVisits]
  | cons t ts ih =>
    cases stack with
    | nil => simp [scan] at hsc
    | cons f stack =>
      cases hh : step x f t with
      | none => simp [scan, hh] at hsc
      | some v =>
        obtain ⟨a, children⟩ := v
        have hs' : (scan x (children ++ stack) ts).isSome := by
          cases h : scan x (children ++ stack) ts <;> simp_all [scan]
        have hr := readToken_encode hm hs (f.1.isLt.le.trans hn) t (legal_of_step hh)
        simp [decodeVisits, hr, hh, ih _ hs']

end PrimedCounter

end VPVNP
end Computability
end OAI
