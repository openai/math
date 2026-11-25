import OAI.Hierarchy.DescentPrivateFeeBudget
import OAI.Hierarchy.DescentChronologicalPrivate
import Mathlib.Data.Nat.Log

namespace OAI
/-! # The native binary scalar multiplicity has a single uniformly bounded accumulator -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentHistoryOrder GadgetNetwork
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {q ε : ℝ} {S : AtomSchedule} {k i₀ z₀ D₀ i z D w hist : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
variable {target : Reached W G q ε S k i z D w hist}

theorem Path.private_budget (he : 0≤ε) (path : Path start target) :
    q*(w:ℝ)*(path.privateCharge:ℝ)≤(i:ℝ)*((privateRate G:ℝ)*(2^k:ℕ)*ε) :=by
  have nonnegative : 0≤(privateRate G:ℝ)*(2^k:ℕ)*ε:=by positivity
  induction path with
  | here=>simp only [Path.privateCharge,Nat.cast_zero,mul_zero];positivity
  | ordinary prev ticket ih=>
    rw [Path.privateCharge,Nat.cast_add,mul_add,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact add_le_add ih ticket.fee_budget
  | reset prev b ih=>
    change q * (w : ℝ) * ((prev.privateCharge + mergeFee b.reblock : ℕ) : ℝ) ≤ _
    rw [reset_reblock_fee,Nat.add_zero,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    exact ih.trans (le_add_of_nonneg_right nonnegative)
end
end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice DescentHistoryOrder GadgetNetwork
open Catalyst Computability.BorderVNP.Crossing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s
include X G S n h C f g p in
/-- The copy count and initial graph size account for the global counter. Its remaining factors are
the number of scheduled transitions, a single local alphabet constant and the grouping radix. -/
theorem private_max {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) :
    privateMass (NativeBranch.archive X G S b hp).bit≤privateMax G S p :=by
  rw [archive_private X G S b hp]
  have bound := b.path.private_budget he
  have hs : 0<s :=b.source.atoms ▸ b.source.valid.atom
  have ht : 0<S.epochPower :=Nat.two_pow_pos _
  have sw : (0:ℝ)<s:=by exact_mod_cast hs
  have wp : (0:ℝ)<(wire:ℕ):=by positivity
  have tp : (1:ℝ)≤S.epochPower:=by exact_mod_cast ht
  have cancel : q*(wire:ℝ)=1/(s:ℝ) :=by field_simp
  have scaled : 1 / (s : ℝ) * (b.path.privateCharge : ℝ) ≤
      (S.length : ℝ) * ((privateRate G : ℝ) * (2^k : ℕ) * ε) := calc
    _ = q * ((wire : ℕ) : ℝ) * (b.path.privateCharge : ℝ) :=
      congrArg (fun a : ℝ => a * (b.path.privateCharge : ℝ)) (by simpa only [Nat.cast_pow] using cancel.symm)
    _ ≤ _ := bound
  have factor : ε≤((S.initialSites*S.copies:ℕ):ℝ) :=
    div_le_self (by positivity) tp
  have bound' := scaled.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left factor (by positivity : 0≤(privateRate G:ℝ)*(2^k:ℕ))) (by positivity : 0≤(S.length:ℝ)))
  have result := mul_le_mul_of_nonneg_left bound' sw.le
  rw [←mul_assoc,←mul_assoc,mul_one_div_cancel sw.ne',one_mul] at result
  unfold privateMax
  rw [radix]
  push_cast at result ⊢
  exact_mod_cast (by simpa only [Nat.cast_pow,Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using result :
    (b.path.privateCharge:ℝ)≤(S.length:ℝ)*(privateRate G:ℝ)*((2^k:ℕ):ℝ)*
      S.initialSites*((S.copies:ℝ)*s))

include X G S n h C f g p in
theorem private_word {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) :
    privateMass (NativeBranch.archive X G S b hp).bit<2^(Nat.log 2 (privateMax G S p)+1) :=
  (private_max X G S b hp).trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

end
end Hierarchy.DescentSixParty.NativeBranch

end OAI
