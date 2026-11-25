import OAI.Computability.BorderVNP.RoutingISAPaddingProof
import OAI.Computability.BorderVNP.TeamScales

/-! # The zero suffix after both scheduled legs

The native suffix starts after the oriented leg loads of the round-robin allocation. Equation
(7.2) bounds the total length of all scans using just the exterior budget of the current team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Sum of the common header and the two round-robin leg lengths in this physical block. -/
def BroadcastFrame.usedPrefix (f : BroadcastFrame) {w b : ℕ} (fit : f.Fits w b)
    (width : Fin f.teams → Fin f.teams → ℕ) (v : Fin f.teams) : ℕ :=
  let u : Fin f.teams := ⟨f.team,fit.own⟩
  f.header + Routing.legLoad fit.three width u v + Routing.legLoad fit.three width v u

private theorem pairIndex_lt {u v R base w : ℕ} (hu : u < R) (hv : v < R)
    (fit : base+R^2 ≤ 2^w) : pairIndex base R u v < 2^w := by
  have h := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hu)
  rw [Nat.succ_mul] at h
  unfold pairIndex
  rw [pow_two] at fit
  omega

/-- The table-driven padding start is the ordinary load formula when the prefix table
contains the round-robin schedule of the public transmission list. -/
theorem BroadcastFrame.paddingFrom_eq_usedPrefix {w b : ℕ} (f : BroadcastFrame) (fit : f.Fits w b)
    {width : Fin f.teams → Fin f.teams → ℕ} {pub : Arg → ℕ} {mem : ℕ → ℕ}
    (tab : AddressTables fit.three width pub mem) (v : Fin f.teams) :
    f.paddingFrom mem (frameField pub mem 18) v = f.usedPrefix fit width v := by
  let u : Fin f.teams := ⟨f.team,fit.own⟩
  exact congrArg₂ (· + ·) (congrArg (f.header + ·) (tab.total u v)) (tab.total v u)

/-- Correctness of the actual padding instructions on the mathematical routing table:
every position after the header and both oriented legs is zero. -/
theorem checkPadding_schedule {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (width : Fin f.teams → Fin f.teams → ℕ)
    (tables : AddressTables fit.three width (readings pub) (readings m))
    (pairRoom : frameField (readings pub) (readings m) 18 + f.teams^2 ≤ 2^w)
    (allocated : ∀ v : Fin f.teams, v.val ≠ f.team → f.usedPrefix fit width v ≤ f.capacity) :
    NativeLinkCheck pub macros checkPadding s m
      (f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots)
      (∀ v : Fin f.teams, v.val ≠ f.team → f.ZeroFrom (readings m) (f.usedPrefix fit width v) v) := by
  let base := frameField (readings pub) (readings m) 18
  have spec (v : Fin f.teams) : f.paddingFrom (readings m) base v = f.usedPrefix fit width v :=
    f.paddingFrom_eq_usedPrefix fit tables v
  have h := checkPadding_check f pub macros s m image fit base rfl
    (fun _ hi _ => ⟨pairIndex_lt fit.own hi pairRoom,pairIndex_lt hi fit.own pairRoom⟩)
    (fun i hi hne => (spec ⟨i,hi⟩).le.trans (allocated ⟨i,hi⟩ hne))
  constructor
  · intro valid
    exact h.complete fun i hi hne => (spec ⟨i,hi⟩).symm ▸ valid ⟨i,hi⟩ hne
  · intro es t mt run
    obtain ⟨hm,ho⟩ := h.sound run
    exact ⟨hm,fun v hne => spec v ▸ ho v v.isLt hne⟩

/-- With the actual rounded per-partner field width, the number of scan ticks is linear in
the exterior budget of (7.2) and the team count, independently of literal or pin lengths. -/
theorem BroadcastFrame.linkCheckTicks_le_exterior (f : BroadcastFrame) (ξ : ℝ) (n setup extra : ℕ)
    (hlink : f.link = TeamScales.link ξ f.teams n) :
    f.linkCheckTicks setup extra ≤ (setup+extra+(zeroScanBody.slots+1)+6) *
      (TeamScales.exterior ξ f.processors n + f.teams+1) := by
  let X := TeamScales.exterior ξ f.processors n
  let nbits := TeamScales.width n (1-ξ)
  let total := X+f.teams+1
  let perBit := zeroScanBody.slots+1
  have hcap : f.teams*f.capacity ≤ X := by
    change f.teams*(f.link*f.processors) ≤ f.processors*nbits
    have h := Nat.div_mul_le_self nbits f.teams
    change f.link = nbits/f.teams at hlink
    rw [hlink]
    calc
      _ = f.processors * (nbits/f.teams*f.teams) := by ring
      _ ≤ f.processors * nbits := Nat.mul_le_mul_left _ h
  have hsetup := Nat.le_mul_of_pos_right (setup+1) (Nat.zero_lt_succ (X+f.teams))
  have hteam : (extra+5)*f.teams ≤ (extra+5)*total :=
    Nat.mul_le_mul_left _ (by dsimp [total]; omega)
  have hbits : perBit*(f.teams*f.capacity) ≤ perBit*total :=
    Nat.mul_le_mul_left _ (by dsimp [total]; omega)
  calc
    f.linkCheckTicks setup extra = (setup+1) + (extra+5)*f.teams + perBit*(f.teams*f.capacity) := by
      simp only [BroadcastFrame.linkCheckTicks,perBit]
      ring
    _ ≤ (setup+1)*total + (extra+5)*total + perBit*total :=
      Nat.add_le_add (Nat.add_le_add hsetup hteam) hbits
    _ = _ := by change _ = (setup+extra+perBit+6)*total; ring

end RoutingISA

end BorderVNP
end Computability
end OAI
