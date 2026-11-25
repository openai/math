import OAI.Computability.BorderVNP.TransmissionScan
import OAI.Computability.BorderVNP.TransmissionDirectory

/-! # Sparse role selection on a physical team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The small decision tree at the entry to a range. An unrelated team skips its payload. -/
inductive Decision where
  | skip | invalid
  | active (mode : Role)
  | test (x y : Reg) (yes no : Decision)

/-- Compile the decisions to physical comparison instructions. -/
def Decision.code : Decision → Code
  | .skip => .nop
  | .invalid => .reject
  | .active m => scan m.bitCode
  | .test x y a b => .ifEq x y a.code b.code

/-- Interpret the same decisions on the current team, tag, and endpoint words.
The outer option rejects malformed tags; the inner option omits nonincident ranges. -/
def Decision.role (s : Bank w) : Decision → Option (Option Role)
  | .skip => some none
  | .invalid => none
  | .active m => some (some m)
  | .test x y a b => if s x = s y then a.role s else b.role s

/-- Maximum number of comparisons before reaching the selected role. -/
def Decision.depth : Decision → ℕ
  | .test _ _ a b => 1+max a.depth b.depth
  | _ => 0

/-- The actual team-side tests for shared and data intervals. -/
def decision : Decision :=
  .test 8 2
    (.test 0 9 (.test 9 10 (.active .sharedHere) (.active .receiveA))
      (.test 0 10 (.active .receiveB) .skip))
    (.test 8 1
      (.test 0 9 (.test 9 10 (.active .dataHere) (.active .sendData))
        (.test 0 10 (.active .receiveB) .skip))
      .invalid)

/-- The emitted decision tree is the one used by the native evaluator. -/
theorem decision_code : decision.code = dispatch := rfl

/-- Memory after skipping or processing this range. -/
def finishedMemory (role : Option Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    (bits : ℕ → Bool) : Memory w :=
  role.elim m fun mode => rangeMemory mode pub s m bits (s 11).val

/-- The bit-dependent cost is charged to the selected endpoint only. -/
def payloadCost (role : Option Role) (len : ℕ) : ℕ :=
  role.elim 0 fun mode => len*(mode.bitCode.slots+2)

/-- A range selected at the current team has safe arithmetic and passes all sender checks
in the sequence of true memories. An unselected range needs no payload checks. -/
def Ready (role : Option Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) (bits : ℕ → Bool) : Prop :=
  ∀ mode, role = some mode → ∀ j < (s 11).val, ∀ t, sameRange (Function.update s 16 (Fin.ofNat _ j)) t →
    mode.permits pub t (rangeMemory mode pub s m bits j)

/-- Dispatch executes the chosen scan and preserves every lower register except its offset.
The total bound charges the number of comparisons even for skipped ranges. -/
theorem Decision.run {D : Decision} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bits : ℕ → Bool) {role : Option Role}
    (hrole : D.role s = some role) (h1 : s 1 = 1) (h0 : s 16 = 0)
    (ok : Ready role pub s m bits) :
    ∃ es t, Runs pub macros D.code s m es t (finishedMemory role pub s m bits) ∧
      (∀ i : Reg, i.val < 16 → t i = s i) ∧ traceCost es ≤ D.depth + payloadCost role (s 11).val + 1 := by
  induction D with
  | invalid => cases hrole
  | skip =>
    cases hrole
    exact ⟨_,_,Runs.localStep _ rfl rfl,fun _ _ => rfl,le_rfl⟩
  | active mode =>
    cases hrole
    obtain ⟨es,t,r,hl,hc⟩ := scan_runs mode pub macros s m bits h1 h0 (ok mode rfl)
    refine ⟨es,t,r,fun i hi => ?_,by simpa [Decision.depth,payloadCost] using hc⟩
    exact (hl i hi.le).trans (Function.update_of_ne (fun he => by subst i; omega) ..)
  | test x y a b iha ihb =>
    by_cases eq : s x = s y
    · have hr : a.role s = some role := by simpa [Decision.role,eq] using hrole
      obtain ⟨es,t,r,hl,hc⟩ := iha hr
      refine ⟨_,t,.ifEq (by rw [ite_eq_left eq]; exact r),hl,?_⟩
      change 1 + traceCost es ≤ 1 + max a.depth b.depth + _ + 1
      omega
    · have hr : b.role s = some role := by simpa [Decision.role,eq] using hrole
      obtain ⟨es,t,r,hl,hc⟩ := ihb hr
      refine ⟨_,t,.ifEq (by rw [ite_eq_right eq]; exact r),hl,?_⟩
      change 1 + traceCost es ≤ 1 + max a.depth b.depth + _ + 1
      omega

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
