import OAI.Hierarchy.DescentEpochAdviceLayoutNumbers
import OAI.Hierarchy.DescentPackedEpochShelfLayout

namespace OAI
/-! # The immutable packed profile header on an original ballot -/

namespace Hierarchy
open Computability.VPVNP.BurstRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section

namespace DescentPackedProfileValidity
open DescentSIMDLookup DescentTerminalEpochFlags

def bad (C grain used : ℕ) (key : Cell (DescentTerminalEpochBits.width C*grain)) : ℕ :=
  if ∀i : Fin grain,SeatValid C used (digit (DescentTerminalEpochBits.width C) i.val key.val) i.val then 0 else 1

def startsWord (grain r : ℕ) := r*grain

end DescentPackedProfileValidity

namespace DescentPackedProfileInstall
open DescentPackedProfileValidity DescentPackedProfileTape

def advice (lo C grain a : ℕ) :=
  if a < (dict lo C grain).base then bankShift C grain (a-lo)
  else
    let raw:=a-(dict lo C grain).base
    let limit:=2^(DescentTerminalEpochBits.width C*grain)
    bad C grain (raw/limit) ⟨raw%limit,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Every bit in this common column is a fixed literal independent of the
selector, the number of reached rows, and the current execution. -/
def install {W : ℕ} (lo C grain : ℕ) (m : Memory W) : Memory W :=
  fillSegment lo (end_ lo C grain-lo) (fun a=>(advice lo C grain a:Word W)) m

theorem before {W : ℕ} (lo C grain : ℕ) (m : Memory W) {a : ℕ} (low : a < lo) :
    install lo C grain m a=m a := by simp [install,fillSegment,not_le.mpr low]

def prepare {A : Type} {C seats W : ℕ} (lo grain : ℕ) (pin : DescentTerminalEpochBits.Pins C seats→A)
    (z : A→Bool) (old : Memory W) : Memory W :=
  let start:=(startsBank lo seats grain).base
  let src:=memory pin z W lo grain old
  fillSegment start (slots seats grain) (fun a=>(startsWord grain (a-start):Word W)) src

end DescentPackedProfileInstall

namespace DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileInstall DescentPackedProfileTape
variable {A : Type} {w : ℕ}

def rawTape (r : ℕ) (z : A→Bool) : ℕ→List (Source A)→Memory w→Memory w
  | _,[],m=>m
  | lo,s::ss,m=>rawTape r z (lo+space r s) ss (prepare lo r s.pin z m)

theorem prepare_low (r lo : ℕ) (s : Source A) (z : A→Bool) (m : Memory w) {a : ℕ} (small : a < lo) :
    prepare lo r s.pin z m a=m a := by
  have h : lo ≤ (startsBank lo s.seats r).base:=Nat.le_add_right _ _
  simp [prepare,fillSegment,show ¬(startsBank lo s.seats r).base ≤ a by omega,
    DescentPackedProfileTape.low s.pin z w lo r m small]

theorem raw_low (r : ℕ) (z : A→Bool) (lo : ℕ) (ss : List (Source A)) (m : Memory w) {a : ℕ} (h : a < lo) :
    rawTape r z lo ss m a=m a := by
  induction ss generalizing lo m with
  | nil=>rfl
  | cons s ss ih=>
    rw [rawTape,ih _ _ (by omega),prepare_low r lo s z m h]

def header (lo C r : ℕ) (ss : List (Source A)) (z : A→Bool) (m : Memory w) :=
  install (lo+extent r ss) C r (rawTape r z lo ss m)

theorem frame (lo C r : ℕ) (ss : List (Source A)) (z : A→Bool) (m : Memory w) {a : ℕ} (small : a < lo) :
    header lo C r ss z m a=m a :=
  (before _ _ _ _ (by omega)).trans (raw_low r z lo ss m small)

end DescentPackedEpochShelves
end
end Hierarchy

end OAI
