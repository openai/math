import OAI.Computability.BorderVNP.TransmissionPinsIdentityStep
import OAI.Computability.BorderVNP.TransmissionPinsEffects

/-! # Native identity check on all secondary pins of the designated team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Each live and reference bit read by the identity loop has a representable address. -/
structure IdentityFits (L : Layout) (w : ℕ) : Prop where
  /-- The processor layout permits division by the literal width. -/
  literal : 0 < L.literal
  /-- The flattened physical pin address fits. -/
  live : ∀ i < L.width, livePinAddress L.teams L.literal L.link i < 2^w
  /-- The advised reference array address fits. -/
  reference : ∀ i < L.width, L.starbase+i < 2^w

/-- Equality of the physical live and advised reference words at one genuine position. -/
def pinMatch (L : Layout) (m : Memory w) (i : ℕ) : Prop :=
  m (livePinAddress L.teams L.literal L.link i) = m (L.starbase+i)

private theorem identityLoop_runs (L : Layout) (fit : IdentityFits L w) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (k x : ℕ) (s : Bank w)
    (ready : Ready L x s) (remaining : x+k = L.width)
    (matched : ∀ i, x ≤ i → i < L.width → pinMatch L m i) :
    ∃ es t, Runs pub macros (.whileLt 6 8 identityPinStep) s m es t m ∧
      traceCost es ≤ 1+k*(1+identityPinStep.slots) ∧ Ready L L.width t := by
  induction k generalizing x s with
  | zero =>
    have he : x = L.width := by simpa using remaining
    have eq : s 6 = s 8 := Fin.ext (ready.cursor.trans (he.trans ready.width.symm))
    exact ⟨_,s,.whileDone (by simp [eq]),by change 1 ≤ 1+0*(1+identityPinStep.slots); simp, he ▸ ready⟩
  | succ k ih =>
    have hx : x < L.width := by omega
    have guard : s 6 < s 8 := by
      change readings s 6 < readings s 8
      rwa [ready.cursor,ready.width]
    have hw : L.width < 2^w := ready.width ▸ (s 8).isLt
    obtain ⟨es,t,step,cost,post⟩ := identityPinStep_run L x pub macros m s ready fit.literal
      (fit.live x hx) (fit.reference x hx) (by omega) (matched x le_rfl hx)
    obtain ⟨fs,u,loop,time,finish⟩ := ih (x+1) t post (by omega)
      (fun i hi hj ↦ matched i (by omega) hj)
    refine ⟨_,u,.whileStep guard step loop,?_,finish⟩
    change 1 + traceCost (es++fs) ≤ _
    rw [Transmission.cost_append, Nat.succ_mul]
    omega

private theorem identityLoop_sound (L : Layout) (fit : IdentityFits L w) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (k x : ℕ) (s : Bank w)
    (ready : Ready L x s) (remaining : x+k = L.width) {es t mt}
    (r : Runs pub macros (.whileLt 6 8 identityPinStep) s m es t mt) :
    ∀ i, x ≤ i → i < L.width → pinMatch L m i := by
  induction k generalizing x s es with
  | zero => omega
  | succ k ih =>
    have hx : x < L.width := by omega
    have guard : s 6 < s 8 := by
      change readings s 6 < readings s 8
      rwa [ready.cursor,ready.width]
    have hw : L.width < 2^w := ready.width ▸ (s 8).isLt
    cases r with
    | atom h => cases h
    | whileDone h => contradiction
    | whileStep _ step loop =>
      obtain ⟨here, rfl, post, _⟩ := identityPinStep_sound L x pub macros m s ready fit.literal
        (fit.live x hx) (fit.reference x hx) (by omega) step
      intro i hi hj
      rcases eq_or_lt_of_le hi with he | ht
      · exact he ▸ here
      · exact ih (x+1) _ post (by omega) loop i ht hj

/-- The designated team must match its actual pin with the advised pin at every genuine
position. The remaining teams skip this comparison. -/
def IdentityMatches (L : Layout) (m : Memory w) : Prop :=
  L.team = 0 → ∀ i < L.width, pinMatch L m i

/-- Matching inputs return within the fixed setup cost and one bounded native step per bit. -/
theorem checkIdentityPins_run (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) (fit : L.team = 0 → IdentityFits L w) (matched : IdentityMatches L m) :
    ∃ es t, Runs pub macros checkIdentityPins s m es t m ∧
      traceCost es ≤ pinSetup.slots + 2 + L.width*(1+identityPinStep.slots) := by
  obtain ⟨fs, a, setup, bound, ready⟩ := pinSetup_run L pub macros m s frame hframe ht hs hc
  have test : a 0 = a 2 ↔ L.team = 0 := by
    rw [Fin.ext_iff]
    exact ready.team ▸ ready.zero ▸ Iff.rfl
  by_cases h0 : L.team = 0
  · obtain ⟨gs,t,loop,cost,_⟩ := identityLoop_runs L (fit h0) pub macros m L.width 0 a ready
      (Nat.zero_add _) (fun i _ hi ↦ matched h0 i hi)
    refine ⟨_,t,.seq setup (.ifEq (by rw [ite_eq_left (test.mpr h0)]; exact loop)), ?_⟩
    rw [Transmission.cost_append]
    change traceCost fs + (1 + traceCost gs) ≤ _
    omega
  · refine ⟨_,a,.seq setup (.ifEq (by rw [ite_eq_right (test.not.mpr h0)]; exact Runs.localStep _ rfl rfl)), ?_⟩
    rw [Transmission.cost_append]
    change traceCost fs + 2 ≤ _
    omega

/-- Exact normal-return condition for the full native pin check, including its frame
initialization and its branch on the team number. -/
theorem checkIdentityPins_iff (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) (fit : L.team = 0 → IdentityFits L w) :
    (∃ es t mt, Runs pub macros checkIdentityPins s m es t mt) ↔ IdentityMatches L m := by
  obtain ⟨es, a, setup, _, ready⟩ := pinSetup_run L pub macros m s frame hframe ht hs hc
  have test : a 0 = a 2 ↔ L.team = 0 := by
    rw [Fin.ext_iff]
    exact ready.team ▸ ready.zero ▸ Iff.rfl
  constructor
  · rintro ⟨gs,t,mt,r⟩ ht0
    have eq := test.mpr ht0
    unfold checkIdentityPins at r
    cases r with
    | atom h => cases h
    | seq initRun branch =>
      obtain ⟨_, rfl, rfl⟩ := setup.unique_of_deterministic (by decide) initRun
      cases branch with
      | atom h => cases h
      | ifEq tail =>
        rw [ite_eq_left eq] at tail
        exact fun i hi ↦ identityLoop_sound L (fit ht0) pub macros m L.width 0 a ready
          (Nat.zero_add _) tail i (Nat.zero_le _) hi
  · intro matched
    obtain ⟨fs,u,run,_⟩ := checkIdentityPins_run L pub macros m s frame hframe ht hs hc fit matched
    exact ⟨fs,u,m,run⟩

/-- On every returning native check the original memory is intact, the trace has no
private choices and the charged ticks are linear in the genuine width. -/
theorem checkIdentityPins_effects (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) (fit : L.team = 0 → IdentityFits L w) {es t mt}
    (r : Runs pub macros checkIdentityPins s m es t mt) :
    mt = m ∧ es.flatMap TeamRAM.Event.choices = [] ∧
      traceCost es ≤ pinSetup.slots + 2 + L.width*(1+identityPinStep.slots) := by
  have matched := (checkIdentityPins_iff L pub macros m s frame hframe ht hs hc fit).mp ⟨_,_,_,r⟩
  obtain ⟨gs,u,rr,bound⟩ := checkIdentityPins_run L pub macros m s frame hframe ht hs hc fit matched
  obtain ⟨rfl,_,rfl⟩ := rr.unique_of_deterministic (by decide) r
  exact ⟨rfl,noChoices r (by decide),bound⟩

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
