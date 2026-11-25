import OAI.Computability.BorderVNP.RoutingISAHeader
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-!
# Fitted data for the common-prefix reader

All fields below are read from the actual initialized scratch frame. The
processor input comes before that frame; the header copy comes after it.
Consequently copying even the last prefix bit preserves both the frame and
the original physical slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Seven natural parameters consumed by the finite common-prefix reader. -/
structure BroadcastFrame where
  /-- Number of the team running the evaluator. -/
  team : ℕ
  /-- Total number of teams. -/
  teams : ℕ
  /-- Processor count per team. -/
  processors : ℕ
  /-- Length of each literal and each extra pin field. -/
  literal : ℕ
  /-- Exterior field width per processor and other team. -/
  link : ℕ
  /-- Number of common prefix bits per unordered physical block. -/
  header : ℕ
  /-- Address of the private copy of the common header. -/
  dst : ℕ

/-- Number of input words belonging to one processor. -/
def BroadcastFrame.stride (f : BroadcastFrame) : ℕ := 2*f.literal + (f.teams-1)*f.link

/-- Capacity of one whole physical link block. -/
def BroadcastFrame.capacity (f : BroadcastFrame) : ℕ := f.link*f.processors

/-- Public reference partner for this team. -/
def BroadcastFrame.partner (f : BroadcastFrame) : ℕ := if f.team = 0 then 1 else 0

/-- The seven fields have the declared values in the addressed memory image. -/
def BroadcastFrame.At (f : BroadcastFrame) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop :=
  frameField pub mem 0 = f.team ∧ frameField pub mem 1 = f.teams ∧
  frameField pub mem 2 = f.processors ∧ frameField pub mem 3 = f.literal ∧
  frameField pub mem 4 = f.link ∧ frameField pub mem 5 = f.header ∧ frameField pub mem 25 = f.dst

/-- Numeric word, input, and allocation bounds used at startup. -/
structure BroadcastFrame.Fits (f : BroadcastFrame) (w frameBase : ℕ) : Prop where
  /-- The relay pool is nonempty. -/
  three : 2 < f.teams
  /-- The caller is a live team. -/
  own : f.team < f.teams
  /-- At least one physical processor. -/
  procs : 0 < f.processors
  /-- Positive exterior link width. -/
  width : 0 < f.link
  /-- A branch bit occurs in the common prefix. -/
  branch : 0 < f.header
  /-- The entire common prefix occurs in every block. -/
  cap : f.header ≤ f.capacity
  /-- The packed frame follows all processor input words. -/
  input : f.processors*f.stride ≤ frameBase
  /-- The broadcast copy does not overlap the frame. -/
  frame : frameBase+31 ≤ f.dst
  /-- All addresses, including the end sentinel, fit at the physical word width. -/
  out : f.dst+f.header < 2^w

/-- Registers initialized by `headerSetup` and retained throughout the scan. -/
def BroadcastFrame.Stable (f : BroadcastFrame) (s : Reg → ℕ) : Prop :=
  s 0 = 0 ∧ s 1 = 1 ∧ s 2 = f.team ∧ s 3 = f.teams ∧ s 4 = f.link ∧
  s 5 = f.processors ∧ s 6 = f.header ∧ s 7 = f.capacity ∧ s 8 = f.partner ∧
  s 9 = f.dst ∧ s 14 = 2

/-- Flat physical input address in this team's processor segment. -/
def BroadcastFrame.addr (f : BroadcastFrame) (partner bit : ℕ) : ℕ :=
  physicalBitAddress f.team f.teams f.literal f.link partner bit

/-- The reference partner differs from the caller and is a real team. -/
theorem BroadcastFrame.partner_spec (f : BroadcastFrame) (h : 2 < f.teams) :
    f.partner ≠ f.team ∧ f.partner < f.teams := by
  unfold partner
  split <;> omega

/-- Every allocated physical block bit precedes the scratch frame. -/
theorem BroadcastFrame.addr_lt_input (f : BroadcastFrame) {w b : ℕ} (fit : f.Fits w b)
    {v j : ℕ} (hv : v < f.teams) (hd : v ≠ f.team) (hj : j < f.capacity) :
    f.addr v j < f.processors*f.stride := by
  have hj' : j < f.processors * f.link := by simpa only [capacity, Nat.mul_comm] using hj
  obtain ⟨hdiv,_,hu⟩ := physicalBitAddress_bounds fit.own hv hd fit.width hj'
  have hh := Nat.mul_le_mul_right f.stride (Nat.succ_le_of_lt hdiv)
  rw [Nat.succ_mul] at hh
  change physicalBitAddress f.team f.teams f.literal f.link v j < _
  change _ < j/f.link*f.stride + f.literal + (f.teams-1)*f.link at hu
  have hls : f.literal + (f.teams-1)*f.link ≤ f.stride := by dsimp [stride]; omega
  omega

private theorem readFrameSafeFixed {w : ℕ} (d : Reg) (f : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) :
    (readFrame d 62 63 f).safeReadOnly w pub mem s ↔ pub 0+f.val < 2^w := by
  simp (config := { decide := true }) [readFrame, Code.block, Code.safeReadOnly, Code.evalNat,
    addressOpFits]
  omega

/-- The fixed header setup computes the capacity and the reference partner on
the true shared memory and satisfies all guards. -/
theorem headerSetup_run {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val) :
    ∃ es t, Runs pub macros headerSetup s m es t m ∧ traceCost es ≤ headerSetup.slots ∧
      f.Stable (readings t) := by
  obtain ⟨h0,h1,h2,_,h4,h5,h25⟩ := image
  have hframe : (pub 0).val+25 < 2^w := by have := fit.frame; have := fit.out; omega
  have hframe' : readings pub 0+25 < 2^w := hframe
  have hpair : f.link ≤ f.stride := by
    have h := Nat.le_mul_of_pos_left f.link (by have := fit.three; omega : 0 < f.teams-1)
    exact h.trans (Nat.le_add_left ..)
  have hcap : f.link*f.processors < 2^w := by
    calc
      _ = f.processors*f.link := Nat.mul_comm ..
      _ ≤ f.processors*f.stride := Nat.mul_le_mul_left _ hpair
      _ ≤ (pub 0).val := fit.input
      _ < 2^w := by omega
  have hraw := fit.cap
  change f.header ≤ f.link*f.processors at hraw
  have hteamPos : 0 < f.teams := by have := fit.three; omega
  have hw : w ≠ 0 := by rintro rfl; simp at hframe
  have hs : headerSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    by_cases ht : f.team = 0 <;>
      simp (config := {decide := true}) [headerSetup, Code.block, Code.safeReadOnly, Code.evalNat,
        readFrameSafeFixed, readFrameFixed, requireLt, addressOpFits, addressOp, h0,h1,h2,h4,h5,h25,
        ht, fit.three, fit.own, hteamPos, fit.procs, fit.width, fit.branch, not_lt.mpr hraw, hcap, hw] <;> omega
  obtain ⟨es,t,run,cost,hr⟩ := headerSetup.runReadOnly pub macros m s hs
  refine ⟨es,t,run,cost,?_⟩
  rw [hr]
  by_cases ht : f.team = 0 <;>
    simp (config := {decide := true}) [headerSetup, Code.block, Code.evalNat, readFrameFixed, requireLt,
      addressOp, BroadcastFrame.Stable, BroadcastFrame.capacity, BroadcastFrame.partner, h0,h1,h2,h4,h5,
      h25, ht, fit.three, fit.own, fit.procs, fit.width, fit.branch, not_lt.mpr hraw]

end RoutingISA

end BorderVNP
end Computability
end OAI
