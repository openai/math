import OAI.Computability.BorderVNP.TeamSiteTimedMacro

/-! # Exact RAM path spellings for the fixed timed private table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Macro

open VPVNP.BurstRAM TeamPrivateTape TeamPrivateCall TeamPrivateFragment TeamPrivateTimeout
variable {Q Γ : Type} {m g w : ℕ} (M : TeamSite.Macro Q Γ m g) (mark : Γ)

/-- Exact bounded physical paths witnessing all three return weights on an arbitrary burst. -/
theorem timedEval_iff (N : ℕ) (vs : List (Word w)) (bits : List Bool) (s : TeamRAM.Sign) :
    M.timedEval mark N vs bits = some s ↔ ∃ n ≤ N, ∃ out u,
      Run (M.timedTable mark) n M.start (M.timedInitial mark N vs) bits out u ∧ sign out = s := by
  constructor
  · intro h
    obtain ⟨⟨out,u⟩, hval, hout⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨n, hn, hr⟩ := evaluate_spec hval
    exact ⟨n,by omega,out,u,hr,hout⟩
  · rintro ⟨n,hn,out,u,hr,rfl⟩
    simp [timedEval,evaluate_of_run hr (Nat.lt_succ_of_le hn)]

private theorem sign_some_iff (z : Option (Option Bool)) (b : Bool) :
    z.map sign = some (sign (some b)) ↔ z.join = some b := by
  rcases z with _ | (_ | (_ | _)) <;> cases b <;> decide

/-- For each nonzero sign and every burst and choice string, the fixed timed program
recognizes exactly the original native paths with that sign. -/
theorem timedEval_signed (hmark : M.alphabet.blank ≠ mark) (N : ℕ) (vs : List (Word w))
    (bits : List Bool) (s : TeamRAM.Sign) (hs : s ≠ .zero) :
    M.timedEval mark N vs bits = some s ↔ M.eval (N+1) vs bits = some s := by
  let ts := input M.alphabet.blank M.digit M.inputTape (inputBits vs)
  let timed := symbolEval (TeamPrivateTimeout.table M.alphabet.blank mark M.table)
    M.alphabet.blank (N+1) M.start (M.timedSymbols mark N vs) bits
  let raw := symbolEval M.table M.alphabet.blank (N+1) M.start ts bits
  have ht : M.timedEval mark N vs bits = timed.map sign := by
    simpa only [timedEval,timedTable,timedInitial,timed,Option.map_map,Function.comp_def] using
      congrArg (Option.map sign) (symbolEval_tracks M.alphabet _ (N+1) M.start (M.timedSymbols mark N vs) bits)
  have hr : M.eval (N+1) vs bits = raw.map sign := by
    simpa only [Macro.eval,Macro.initial,raw,ts,Option.map_map,Function.comp_def] using
      congrArg (Option.map sign) (symbolEval_tracks M.alphabet M.table (N+1) M.start ts bits)
  have he : timed.join = raw.join := symbolEval_signed M.alphabet.blank mark M.table hmark N M.start [] ts bits
  obtain ⟨b, rfl⟩ : ∃ b, s = sign (some b) := by
    cases s with
    | plus => exact ⟨false,rfl⟩
    | minus => exact ⟨true,rfl⟩
    | zero => contradiction
  rw [ht,hr,sign_some_iff,sign_some_iff,he]

end TeamSite.Macro

end BorderVNP
end Computability
end OAI
