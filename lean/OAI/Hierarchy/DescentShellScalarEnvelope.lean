import OAI.ThreeFlat.Routing.CallPoolBudget
import OAI.Hierarchy.DescentTerminalCalibratedRowArithmetic
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! A common address exponent for every integral terminal row budget with the same word-sized scalar fields. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentTerminalGraphVolume DescentDatedAddressBook ThreeFlat.Routing Filter

structure ShellNumbers where
  time : ℕ
  sites : ℕ
  volume : ℕ
  pins : ℕ
  coefficient : ℕ
  homes : ℕ
  bin : ℕ
  p : ℕ
  q : ℕ
  outside : ℕ

def ShellNumbers.Fits (v : ShellNumbers) (bound : ℕ) := v.time≤bound ∧ v.sites≤bound ∧ v.volume≤bound ∧
  v.pins≤bound ∧ v.coefficient≤bound ∧ v.homes≤bound ∧ v.bin≤bound ∧ v.p≤bound ∧ v.q≤bound ∧ v.outside≤bound

def ShellNumbers.size (v : ShellNumbers) :=
  let wires := integralFrontier v.time v.sites v.volume v.pins v.coefficient
  let pool := rowBudget v.p v.q v.bin wires (v.volume*v.pins) v.homes 3 / v.bin * v.bin
  v.homes+pool+v.pins*v.outside+(poolBatchCount wires (v.q*v.p)+pool)

theorem shell_numbers_uniform (c : ℕ) : ∃K : ℕ,∀ᶠ h : ℕ in atTop,∀v : ShellNumbers,
    v.Fits (2^(c*h)) → v.size≤2^(K*h) := by
  let Sample (h : ℕ) := {v : ShellNumbers // v.Fits (2^(c*h))}
  have scalar (p : ShellNumbers→ℕ) (fit : ∀v : ShellNumbers,∀b,v.Fits b→p v≤b) :
      Bounded (fun h (x : Sample h)=>p x.val) := ⟨c,Eventually.of_forall fun h x=>fit x.val _ x.property⟩
  have time:=scalar ShellNumbers.time (fun _ _ a=>a.1)
  have sites:=scalar ShellNumbers.sites (fun _ _ a=>a.2.1)
  have pop:=scalar ShellNumbers.volume (fun _ _ a=>a.2.2.1)
  have pins:=scalar ShellNumbers.pins (fun _ _ a=>a.2.2.2.1)
  have coeff:=scalar ShellNumbers.coefficient (fun _ _ a=>a.2.2.2.2.1)
  have homes:=scalar ShellNumbers.homes (fun _ _ a=>a.2.2.2.2.2.1)
  have bins:=scalar ShellNumbers.bin (fun _ _ a=>a.2.2.2.2.2.2.1)
  have p:=scalar ShellNumbers.p (fun _ _ a=>a.2.2.2.2.2.2.2.1)
  have q:=scalar ShellNumbers.q (fun _ _ a=>a.2.2.2.2.2.2.2.2.1)
  have ext:=scalar ShellNumbers.outside (fun _ _ a=>a.2.2.2.2.2.2.2.2.2)
  let cc (n : ℕ) := Bounded.const (ι:=Sample) n
  let wires:=((((cc 1).add ((cc 2).mul coeff)).mul pop).mul (sites.add (time.mul pins))).div (y:=fun _ x=>x.val.time)
  let batch:=((cc 3).mul (((cc 2).mul wires).add (pop.mul pins))).div (y:=fun _ x=>x.val.q*x.val.p)
  let gross:=((cc 2).mul (batch.add (homes.mul (cc (3+3))))).add bins
  have rows:=(gross.of_le (y:=fun _ x=>rowBudget x.val.p x.val.q x.val.bin
    (integralFrontier x.val.time x.val.sites x.val.volume x.val.pins x.val.coefficient)
    (x.val.volume*x.val.pins) x.val.homes 3/x.val.bin*x.val.bin)
    (fun _ _=>Nat.div_mul_le_self ..))
  have dense:=((wires.add (q.mul p)).sub (y:=fun _ _=>1)).div (y:=fun _ x=>x.val.q*x.val.p)
  obtain ⟨K,capped⟩:=((homes.add rows).add (pins.mul ext)).add (dense.add rows)
  exact ⟨K,capped.mono fun _ bound v admissible=>bound ⟨v,admissible⟩⟩

end Hierarchy.DescentSixParty.SeedNamed

end OAI
