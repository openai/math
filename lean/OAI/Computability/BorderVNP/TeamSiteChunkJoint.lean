import OAI.Computability.BorderVNP.TeamSiteChunkSchedule

/-!
# Finite-PC charged rows of the unique native execution transcript

The quantitative native path correspondence fixes not just a word-PC handoff
chain, but the actual finite-PC charged execution in each block. Arbitrary
signed private choices, old-word guesses, and globally compared memory records
are retained in the same transcript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamLocalClock Filter

variable {w p r k a teams h : ℕ}

/-- Local accepting path replay is invariant under finite-PC encoding, including the
precise sign and old-word data required at each continuation. -/
theorem local_encode (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (fits : p ≤ 2^w) (s : TeamOpcode.State w p r) (es : List (TeamRAM.Event w)) :
    TeamRAM.Local (Model.wordFetch P pub lib) (Model.encode s) es ↔ TeamRAM.Local (P.fetch pub lib) s es := by
  induction es generalizing s with
  | nil =>
    change Model.wordFetch P pub lib (Model.encode s) = .accept ↔ P.fetch pub lib s = .accept
    rw [Model.fetch_encode P pub lib fits]
    cases P.fetch pub lib s <;> simp [Model.mapControl]
  | cons e xs ih =>
    simp only [TeamRAM.Local, Model.fetch_encode P pub lib fits, Model.action_mapControl, Model.advance_mapControl]
    apply and_congr_right
    intro _
    cases ha : (P.fetch pub lib s).advance e.choices e.old with
    | none => simp
    | some z =>
      obtain ⟨next,sg⟩ := z
      simp [ih]

/-- A valid joint signed-RAM transcript directly supplies finite-PC charged rows for
every physical processor, with its own admitted bursts, precise clock and terminal frame. -/
theorem joint_chargedRows (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (fits : p ≤ 2^w) (s : TeamOpcode.State w p r)
    (t : Joint w r teams h) {hr : 0 < teams} {I : ℕ} {header : ℕ → Word w} {es : List (TeamRAM.Event w)}
    {bits : List (List Bool)} {place : Equiv.Perm (Fin (2^(h+Nat.clog 2 teams)))}
    (valid : t.Valid hr H.val (Model.wordFetch P pub lib) (Model.encode s) limit I header es bits place)
    (bounds : ∀ e ∈ es, e.action.extra ≤ cap.val) (time : cost es ≤ limit.val) :
    ChargedRows P pub lib H limit cap (initial (packed w s.pc.val) s.reg) t.history.chunks t.frames := by
  have flat := valid.1.2.1
  have path := (local_encode P pub lib fits s es).mp valid.2.1
  apply (chargedRows_iff P pub lib H limit cap fits s _ _ (flat ▸ path)
    (fun e he => bounds e (flat ▸ he)) (flat ▸ time)).mpr
  exact ⟨valid.1.2.2.1,valid.2.2.2.2.1⟩

/-- At the paper's quantitative team clock the native finite-PC accepting path is
equivalent to one joint transcript with both actual finite-PC charged rows and the
globally checked signed memory and successor data. -/
theorem eventually_execute_iff_charged {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3/2) :
    ∀ᶠ n : ℕ in atTop, ∀ teams : ℕ, ∀ hr : 0 < teams, ∀ {w p r k a : ℕ}
      (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a),
      p ≤ 2^w → ∀ (start : TeamOpcode.State w p r) (H limit cap : Word w),
      H.val = TeamScales.block ξ n → limit.val = TeamScales.ticks ξ teams n → cap.val = TeamScales.width n (1/2) →
      ∀ I : ℕ, I ≤ teams*(3*H.val) →
      ∀ (header : ℕ → Word w) (es : List (TeamRAM.Event w)) (bits : List (List Bool)),
      (∀ e ∈ es, e.action.extra ≤ cap.val) → cost es ≤ limit.val →
      let h := Nat.clog 2 (4*H.val)
      ∀ place : Equiv.Perm (Fin (2^(h+Nat.clog 2 teams))),
        TeamRAM.execute (P.fetch pub lib) start (RAMMemory.initialMemory I header) bits = some es ↔
        ∃! t : Joint w r teams h,
          t.Valid hr H.val (Model.wordFetch P pub lib) (Model.encode start) limit I header es bits place ∧
          ChargedRows P pub lib H limit cap (initial (packed w start.pc.val) start.reg) t.history.chunks t.frames := by
  filter_upwards [Model.eventually_execute_iff_joint hξ hξ'] with n native
  intro teams hr w p r k a P pub lib fits start H limit cap hH hlim hcap I hI header es bits bounds time h place
  have raw := native teams hr P pub lib fits start limit hlim I (hH ▸ hI) header es bits
    (fun e he => hcap ▸ bounds e he) time
  rw [← hH] at raw
  rw [raw place]
  apply existsUnique_congr
  intro t
  exact ⟨fun ht => ⟨ht,joint_chargedRows P pub lib H limit cap fits start t ht bounds time⟩,fun ht => ht.1⟩

end TeamSite

end BorderVNP
end Computability
end OAI
