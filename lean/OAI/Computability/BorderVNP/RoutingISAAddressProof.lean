import OAI.Computability.BorderVNP.RoutingISAAddress
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # The addressed word returned by each routing fragment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Natural value stored at a field of the physically addressed input frame. -/
def frameField (pub : Arg → ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (pub 0 + i)

private theorem readFrameNat {d a b : Reg} (ha : a ≠ b) (f : Word 8) (pub : Arg → ℕ)
    (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (readFrame d a b f).evalNat pub mem s =
      Function.update (Function.update (Function.update s b f.val) a (pub 0 + f.val)) d
        (frameField pub mem f.val) := by
  simp [readFrame, Code.block, Code.evalNat, addressOp, frameField, Function.update_comm ha,
    ha]

/-- The evaluator scratch registers 62 and 63 hold the frame address and field offset. -/
theorem readFrameFixed (d : Reg) (f : Word 8) (pub : Arg → ℕ)
    (mem : ℕ → ℕ) (s : Reg → ℕ) :
    (readFrame d 62 63 f).evalNat pub mem s =
      Function.update (Function.update (Function.update s 63 f.val) 62 (pub 0 + f.val)) d
        (frameField pub mem f.val) :=
  readFrameNat (by decide) f pub mem s

/-- Symbolic calculation at the output of the physical-address fragment. -/
theorem physicalAddress_evalNat (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    physicalAddress.evalNat pub mem s 48 =
      physicalBitAddress (frameField pub mem 0) (frameField pub mem 1)
        (frameField pub mem 3) (frameField pub mem 4) (s 30) (s 31) := by
  by_cases side : s 30 < frameField pub mem 0 <;>
    simp (config := { decide := true }) [physicalAddress, Code.block, readFrameFixed, Code.evalNat,
      addressOp, physicalBitAddress, side, Nat.mul_comm, Nat.add_comm]

/-- Address of the beginning of the interval in the row-major triple table. -/
def tripleIndex (base teams a b c : ℕ) : ℕ := ((a*teams+b)*teams+c)+base

/-- Address of an ordered block total in the row-major pair table. -/
def pairIndex (base teams a b : ℕ) : ℕ := (a*teams+b)+base

/-- Position within the concatenated partner block of a bit with local quotient
`q`. The first positions are the common broadcast. The reverse-oriented data
follow the whole forward-oriented leg. -/
def legPosition (pub : Arg → ℕ) (mem : ℕ → ℕ) (endpoint relay other q : ℕ) : ℕ :=
  let R := frameField pub mem 1
  let front := mem (tripleIndex (frameField pub mem 17) R endpoint relay other)
  let total := mem (pairIndex (frameField pub mem 18) R relay endpoint)
  (front + q + frameField pub mem 5) + (if relay < endpoint then total else 0)

/-- Address calculated at either end of an oriented physical leg. -/
def routedAddress (pub : Arg → ℕ) (mem : ℕ → ℕ) (endpoint relay other q : ℕ) : ℕ :=
  let team := frameField pub mem 0
  physicalBitAddress team (frameField pub mem 1) (frameField pub mem 3) (frameField pub mem 4)
    (if team = endpoint then relay else endpoint) (legPosition pub mem endpoint relay other q)

/-- The table address uses the true triple-prefix and oriented total read from
memory and then the physical layout at the calling end of the link. -/
theorem legAddress_evalNat (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    legAddress.evalNat pub mem s 48 = routedAddress pub mem (s 32) (s 33) (s 34) (s 35) := by
  by_cases reverse : s 33 < s 32 <;> by_cases localEnd : frameField pub mem 0 = s 32 <;>
    simp (config := { decide := true }) [legAddress, Code.block, readFrameFixed, Code.evalNat,
      physicalAddress_evalNat, pairAddress, tripleAddress, addressOp, routedAddress, legPosition,
      pairIndex, tripleIndex, reverse, localEnd]

/-- The ordinal is assigned cyclically among the `R-2` relays after skipping the
two ends, in increasing order. -/
def endpointRelay (R first other j : ℕ) : ℕ :=
  Routing.skip (max first other) (Routing.skip (min first other) (j % (R-2)))

/-- The endpoint code chooses the scheduled relay and passes the quotient, with
both skipped endpoint numbers interpreted in increasing order. -/
theorem endpointAddress_evalNat (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    endpointAddress.evalNat pub mem s 48 =
      routedAddress pub mem (frameField pub mem 0)
        (endpointRelay (frameField pub mem 1) (frameField pub mem 0) (s 30) (s 31))
        (s 30) (s 31 / (frameField pub mem 1 - 2)) := by
  by_cases side : frameField pub mem 0 < s 30
  · by_cases first : s 31 % (frameField pub mem 1 - 2) < frameField pub mem 0 <;>
      by_cases second : Routing.skip (frameField pub mem 0) (s 31 % (frameField pub mem 1 - 2)) < s 30 <;>
      simp only [Routing.skip, first, ite_true, ite_false] at second <;>
      simp (config := { decide := true }) [endpointAddress, Code.block, readFrameFixed, Code.evalNat,
        legAddress_evalNat, skipRegister, addressOp, endpointRelay, min_eq_left side.le, max_eq_right side.le,
        Routing.skip, side, first, second]
  · by_cases first : s 31 % (frameField pub mem 1 - 2) < s 30 <;>
      by_cases second : Routing.skip (s 30) (s 31 % (frameField pub mem 1 - 2)) < frameField pub mem 0 <;>
      simp only [Routing.skip, first, ite_true, ite_false] at second <;>
      simp (config := { decide := true }) [endpointAddress, Code.block, readFrameFixed, Code.evalNat,
        legAddress_evalNat, skipRegister, addressOp, endpointRelay, min_eq_right (le_of_not_gt side),
        max_eq_left (le_of_not_gt side), Routing.skip, side, first, second]

/-- The numeric endpoint calculation agrees with the order embedding of the
entire allowed relay pool. -/
theorem endpointRelay_eq {R : ℕ} (hR : 2 < R) {u other : Fin R} (h : u ≠ other) (j : ℕ) :
    endpointRelay R u other j = (Routing.relay hR h j).val := (Routing.relay_formula hR h j).symm

/-- The shared offset tables occupy the frame-designated regions and contain the
natural prefix and total of every list. -/
structure AddressTables {R : ℕ} (hR : 2 < R) (width : Fin R → Fin R → ℕ)
    (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Team count as read from frame field one. -/
  teams : frameField pub mem 1 = R
  /-- Row-major triple entries contain the prefix of the opposite endpoint. -/
  front (u v y : Fin R) :
    mem (tripleIndex (frameField pub mem 17) R u v y) = Routing.baseOffset width u v y
  /-- Row-major ordered-pair entries contain the complete oriented leg length. -/
  total (u v : Fin R) : mem (pairIndex (frameField pub mem 18) R u v) = Routing.legLoad hR width u v

/-- The physical position of a scheduled bit is its ordinal in the leg bijection,
following the header and the earlier orientation of the same block. -/
theorem AddressTables.legPosition_eq {R : ℕ} {hR : 2 < R} {width : Fin R → Fin R → ℕ}
    {pub : Arg → ℕ} {mem : ℕ → ℕ} (h : AddressTables hR width pub mem) {u v : Fin R}
    (bit : Routing.Hop hR width u v) :
    legPosition pub mem u v bit.1 (bit.2.val / (R-2)) =
      (Routing.legEquiv hR width u v bit).val + frameField pub mem 5 +
      (if v < u then Routing.legLoad hR width v u else 0) := by
  simp only [legPosition, h.teams, h.front, h.total, Routing.lookup_address]
  rfl

variable {w : ℕ}

/-- A genuine read-only returned path, including the charged ticks, protected
registers and the native accepting execution of the assembled word table. -/
def AddressRun (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (c : Code) (result : ℕ) : Prop :=
  ∃ es t, Runs pub macros c s m es t m ∧ traceCost es ≤ c.slots ∧ (t 48).val = result ∧
    (∀ i : Reg, i.val < 30 → t i = s i) ∧
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es

private theorem addressRun_of_eval {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {m : Memory w} {s : Bank w} {c : Code} {result : ℕ}
    (safe : c.safeReadOnly w (readings pub) (readings m) (readings s)) (hc : c.protects 30 = true)
    (value : c.evalNat (readings pub) (readings m) (readings s) 48 = result) :
    AddressRun pub macros m s c result := by
  obtain ⟨es,t,run,cost,agree⟩ := c.runReadOnly pub macros m s safe
  exact ⟨es,t,run,cost,(congrFun agree 48).trans value,
    fun i hi => Fin.ext ((congrFun agree i).trans (c.evalNat_protected _ _ _ hc i hi)),run.execute⟩

/-- Native physical address computation returns the literal–exterior–pin layout address. -/
theorem physicalAddress_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (safe : physicalAddress.safeReadOnly w (readings pub) (readings m) (readings s)) :
    let field := frameField (readings pub) (readings m)
    AddressRun pub macros m s physicalAddress
      (physicalBitAddress (field 0) (field 1) (field 3) (field 4) (s 30).val (s 31).val) :=
  addressRun_of_eval safe (by decide) (physicalAddress_evalNat ..)

/-- Native leg address computation uses the two physical schedule tables. -/
theorem legAddress_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (safe : legAddress.safeReadOnly w (readings pub) (readings m) (readings s)) :
    AddressRun pub macros m s legAddress
      (routedAddress (readings pub) (readings m) (s 32).val (s 33).val (s 34).val (s 35).val) :=
  addressRun_of_eval safe (by decide) (legAddress_evalNat ..)

/-- Native endpoint address computation places the demand bit on its round-robin leg. -/
theorem endpointAddress_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (m : Memory w)
    (s : Bank w) (safe : endpointAddress.safeReadOnly w (readings pub) (readings m) (readings s)) :
    let field := frameField (readings pub) (readings m)
    AddressRun pub macros m s endpointAddress
      (routedAddress (readings pub) (readings m) (field 0)
        (endpointRelay (field 1) (field 0) (s 30).val (s 31).val) (s 30).val ((s 31).val / (field 1 - 2))) :=
  addressRun_of_eval safe (by decide) (endpointAddress_evalNat ..)

end RoutingISA

end BorderVNP
end Computability
end OAI
