import OAI.Computability.BorderVNP.TransmissionPinsRead
import OAI.Computability.BorderVNP.TransmissionStraight

/-! # The native one-bit equality test on the identity branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem afterDet {c d s m es t mt fs u mu}
    (first : Runs pub macros c s m es t mt) (det : c.deterministic = true)
    (both : Runs pub macros (.seq c d) s m fs u mu) :
    ∃ gs, Runs pub macros d t mt gs u mu := by
  cases both with
  | atom h => cases h
  | seq r tail =>
    obtain ⟨_, rfl, rfl⟩ := first.unique_of_deterministic det r
    exact ⟨_, tail⟩

private theorem requireEq_sound {i j s m es t mt} (r : Runs pub macros (requireEq i j) s m es t mt) :
    s i = s j := by
  by_contra hn
  cases r with
  | atom h => cases h
  | ifEq h =>
    rw [ite_eq_right hn] at h
    cases h with | atom h => cases h

/-- The physical comparison has the same truth value as the equality of the two
addressed memory words. On success the sole persistent register change is the increment. -/
private theorem compareOne (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (h : Ready L x s)
    (hl : 0 < L.literal) (ha : livePinAddress L.teams L.literal L.link x < 2^w)
    (hb : L.starbase+x < 2^w) (hx : x+1 < 2^w) :
    ((∃ es t mt, Runs pub macros identityPinStep s m es t mt) →
      m (livePinAddress L.teams L.literal L.link x) = m (L.starbase+x)) ∧
    (m (livePinAddress L.teams L.literal L.link x) = m (L.starbase+x) →
      ∃ es t, Runs pub macros identityPinStep s m es t m ∧ Ready L (x+1) t) := by
  obtain ⟨es, a, first, _, ready, read⟩ := fetchLivePin_run L x pub macros m s h hl ha
  let b := Function.update a (16 : Reg) (a 11 + a 6)
  let c := Function.update b (15 : Reg) (m (b 16).val)
  have add : Runs pub macros (.binary .add 16 11 6) a m [tick w] b m :=
    Runs.localStep m rfl rfl
  have load := Runs.load pub macros 15 16 b m
  have addr : (b 16).val = L.starbase + x := by
    change (Function.update a (16 : Reg) _ 16).val = _
    rw [Function.update_self, Fin.val_add]
    change (readings a 11 + readings a 6) % (2^w) = _
    rw [ready.starbase, ready.cursor, Nat.mod_eq_of_lt hb]
  have actual : c 14 = m (livePinAddress L.teams L.literal L.link x) := by
    simpa (config := { decide := true }) [c, b] using (Fin.ext read : a 14 = _)
  have refVal : c 15 = m (L.starbase+x) := by simp [c, addr]
  constructor
  · rintro ⟨fs, u, mu, both⟩
    obtain ⟨gs, tail⟩ := afterDet first (by decide) both
    obtain ⟨ks, tail⟩ := afterDet add (by decide) tail
    obtain ⟨js, tail⟩ := afterDet load (by decide) tail
    change Runs _ _ (.seq (requireEq 14 15) (.binary .add 6 6 1)) c m _ _ _ at tail
    cases tail with
    | atom hc => cases hc
    | seq chk _ => exact actual.symm.trans ((requireEq_sound chk).trans refVal)
  · intro eqWord
    have same : c 14 = c 15 := actual.trans (eqWord.trans refVal.symm)
    have chk : Runs pub macros (requireEq 14 15) c m [tick w, tick w] c m :=
      .ifEq (by rw [ite_eq_left same]; exact Runs.localStep _ rfl rfl)
    let t := Function.update c (6 : Reg) (c 6 + c 1)
    have inc : Runs pub macros (.binary .add 6 6 1) c m [tick w] t m := Runs.localStep _ rfl rfl
    refine ⟨_, t, first.seq (add.seq (load.seq (chk.seq inc))), ?_⟩
    have hcursor : (a 6).val = x := ready.cursor
    have hone : (a 1).val = 1 := ready.one
    cases ready
    constructor <;> simp_all (config := { decide := true }) [t, c, b, readings,
      Fin.val_add, Nat.mod_eq_of_lt hx]

/-- If the actual live pin equals the advised reference word, the native step returns
with the cursor advanced and its tick cost bounded by the fixed code size. -/
theorem identityPinStep_run (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (h : Ready L x s)
    (hl : 0 < L.literal) (ha : livePinAddress L.teams L.literal L.link x < 2^w)
    (hb : L.starbase+x < 2^w) (hx : x+1 < 2^w)
    (he : m (livePinAddress L.teams L.literal L.link x) = m (L.starbase+x)) :
    ∃ es t, Runs pub macros identityPinStep s m es t m ∧
      traceCost es ≤ identityPinStep.slots ∧ Ready L (x+1) t := by
  obtain ⟨es,t,r,post⟩ := (compareOne L x pub macros m s h hl ha hb hx).2 he
  exact ⟨es,t,r,r.cost_le_slots (by decide),post⟩

/-- Every returning comparison confirms equality at the actual addresses, preserves
all memory and advances the cursor exactly once within the same fixed tick bound. -/
theorem identityPinStep_sound (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (h : Ready L x s)
    (hl : 0 < L.literal) (ha : livePinAddress L.teams L.literal L.link x < 2^w)
    (hb : L.starbase+x < 2^w) (hx : x+1 < 2^w) {es t mt}
    (r : Runs pub macros identityPinStep s m es t mt) :
    m (livePinAddress L.teams L.literal L.link x) = m (L.starbase+x) ∧
      mt = m ∧ Ready L (x+1) t ∧ traceCost es ≤ identityPinStep.slots := by
  obtain ⟨necessity, sufficient⟩ := compareOne L x pub macros m s h hl ha hb hx
  have same := necessity ⟨_, _, _, r⟩
  obtain ⟨fs,u,rr,post⟩ := sufficient same
  obtain ⟨_,rfl,rfl⟩ := rr.unique_of_deterministic (by decide) r
  exact ⟨same, rfl, post, r.cost_le_slots (by decide)⟩

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
