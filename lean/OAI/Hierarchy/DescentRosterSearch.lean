import OAI.Hierarchy.DescentRosterCandidate
import OAI.Hierarchy.DescentColonySearchHardware

namespace OAI
/-! # The all-multiplier search from the rectangular neighbor bank

At every public candidate slot, the program reads the same neighbor directory
from native memory. It writes the original candidate ledger, then executes the
original dense score gather and first-minimum scan over those computed words.
-/
noncomputable section
namespace Hierarchy.DescentColonies.RosterSearch
open DescentGL DescentBinaryField DescentGLScoreRAM ProtocolRAM NativeBatch
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {G k : ℕ}

def steps (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ)
    (i : Fin (2^k-1)) : Code w :=
  RosterCandidate.code w ℓ Δ adj (AllSeedsRAM.slot G (2^ℓ) k base i.val) D cap a ptr (seedAt k i)

def stage (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) : Code w :=
  Code.seq (steps w ℓ Δ adj base D cap a ptr) (2^k-1) le_rfl

def search (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) : Procedure w × ℕ :=
  let job := stage w ℓ Δ adj base D cap a ptr
  let dense := AllSeedsRAM.gatherBase G (2^ℓ) k base
  let final := AllSeedsRAM.winningBase G (2^ℓ) k base
  let expr := AllSeedsRAM.gather G (2^ℓ) k base
  let bank := Bank.mk dense k
  let keys := MultiplierMinimumRAM.keys k
  ((job.text.seq (scan w dense (2^k) expr)).seq (DescentFirstMinimumRAM.code w final bank keys),
    job.ticks+(4+2^k*(2*expr.work+4))+DescentFirstMinimumRAM.ticks final bank keys)

private theorem seq_against {w N : ℕ} (row original : Fin N → Code w) (good : Memory w→Prop)
    (run : ∀i m,good m → (row i).text.Exec m ((original i).after m) (row i).ticks)
    (stable : ∀i m,good m → good ((original i).after m)) (m : Memory w) (initial : good m)
    (n : ℕ) (hn : n≤N) :
    (Code.seq row n hn).text.Exec m ((Code.seq original n hn).after m) (Code.seq row n hn).ticks ∧
      good ((Code.seq original n hn).after m) := by
  induction n with
  | zero =>
    refine ⟨?_,initial⟩
    intro labels registers slots machine
    exact Code.exec_empty m machine
  | succ n ih =>
    let i : Fin N := ⟨n,hn⟩
    obtain ⟨elapsed,held⟩ := ih (show n≤N by omega)
    refine ⟨?_,stable i _ held⟩
    intro labels registers slots machine
    exact Procedure.Exec.then elapsed (run i _ held) machine

private theorem directory_before {H Δ adj base : ℕ} (v : Fin H) (j : Fin Δ) (prior : adj+H*Δ≤base) :
    adj+v.val*Δ+j.val<base := by
  have slot := Nat.mul_le_mul_right Δ v.isLt
  rw [Nat.succ_mul] at slot
  have := j.isLt
  omega

private theorem room_for_slots (G H k base w : ℕ)
    (room : AllSeedsRAM.winningBase G H k base+(2^k-1)<2^w) :
    AllSeedsRAM.slot G H k base (2^k-1)<2^w := by
  have count := Nat.mul_le_mul_right (AllSeedsRAM.stride G H k) (Nat.sub_le (2^k) 1)
  have band := Nat.le_pow_clog (by decide : 1<2) ((2^k)*AllSeedsRAM.stride G H k)
  have firstBank : AllSeedsRAM.slot G H k base (2^k-1)≤AllSeedsRAM.gatherBase G H k base :=
    Nat.add_le_add_left (count.trans band) base
  have packed : AllSeedsRAM.gatherBase G H k base≤AllSeedsRAM.winningBase G H k base := Nat.le_add_right ..
  exact (firstBank.trans (packed.trans (Nat.le_add_right ..))).trans_lt room

/-- Retain the entire memory computed by the ordinary all-seed stage, including
intermediate rows. The neighbor addresses remain available at every candidate. -/
theorem exec_eq (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ)
    (rs : DynamicSplit.Roster ℓ Δ) (m : Memory w)
    (stored : DynamicSplit.Stored adj rs m) (prior : adj+(2^ℓ)*Δ≤base)
    (old : ∀g i,ptr g i+2^k≤base) (room : AllSeedsRAM.winningBase G (2^ℓ) k base+(2^k-1)<2^w)
    (wide : 2^(ℓ+k)<2^w) :
    (search w ℓ Δ adj base D cap a ptr).1.Exec m
      (AllSeedsRAM.afterSearch base D cap a (DynamicSplit.incoming rs) ptr m)
      (search w ℓ Δ adj base D cap a ptr).2 := by
  let dyn := steps w ℓ Δ adj base D cap a ptr
  let orig := AllSeedsRAM.steps w base D cap a (DynamicSplit.incoming rs) ptr
  let good := fun M : Memory w => DynamicSplit.Stored adj rs M
  have safe := room_for_slots G (2^ℓ) k base w room
  have row (i : Fin (2^k-1)) (M : Memory w) (h : good M) :
      (dyn i).text.Exec M ((orig i).after M) (dyn i).ticks := by
    let slot := AllSeedsRAM.slot G (2^ℓ) k base i.val
    have fits : CandidateRAM.output G (2^ℓ) k slot+1<2^w := by
      change AllSeedsRAM.last G (2^ℓ) k base i.val+1<2^w
      rw [AllSeedsRAM.next]
      exact (AllSeedsRAM.mono _ _ _ _ i.isLt).trans_lt safe
    have offset : base≤ slot := Nat.le_add_right ..
    intro labels registers slots machine
    exact RosterCandidate.exec_eq ℓ Δ adj slot D cap a ptr (seedAt k i) rs M h
      (fun g v=>(old g v).trans offset) (prior.trans offset) wide fits machine
  have held (i : Fin (2^k-1)) (M : Memory w) (h : good M) : good ((orig i).after M) := by
    intro v j
    exact (CandidateRAM.below _ _ _ _ _ _ _ M _ ((directory_before v j prior).trans_le
      (Nat.le_add_right ..))).trans (h v j)
  let last := AllSeedsRAM.winningBase G (2^ℓ) k base
  let dense := AllSeedsRAM.gatherBase G (2^ℓ) k base
  let after := (AllSeedsRAM.stage w base D cap a (DynamicSplit.incoming rs) ptr).after m
  let expr := AllSeedsRAM.gather G (2^ℓ) k base
  let keys := MultiplierMinimumRAM.keys k
  let jobs := stage w ℓ Δ adj base D cap a ptr
  have ledger : jobs.text.Exec m after jobs.ticks :=
    (seq_against dyn orig good row held m stored (2^k-1) le_rfl).1
  have denseFit : dense+2^k<2^w := by change (dense+2^k)+(2^k-1)<2^w at room; omega
  have size : 2^AllSeedsRAM.bitsNeeded G (2^ℓ) k < 2^w := by
    change base+2^AllSeedsRAM.bitsNeeded G (2^ℓ) k+2^k<2^w at denseFit
    exact ((Nat.le_add_left _ base).trans (Nat.le_add_right _ (2^k))).trans_lt denseFit
  let sealed := image dense (2^k) expr after
  have packed : (scan w dense (2^k) expr).Exec after sealed (4+2^k*(2*expr.work+4)) :=
    scan_exec dense (2^k) expr after ⟨⟨Nat.two_pow_pos _,size,le_rfl⟩,lookupRow_fits ..⟩ denseFit
  have finish : last+keys.length<2^w := by
    simpa [last,keys,MultiplierMinimumRAM.keys,length_nonzeroWords] using room
  let bank := Bank.mk dense k
  have bankSize : (Bank.mk dense k).size<2^w := (Nat.le_add_left (2^k) dense).trans_lt denseFit
  have win : (DescentFirstMinimumRAM.code w last bank keys).Exec sealed
      (DescentFirstMinimumRAM.after last bank sealed keys) (DescentFirstMinimumRAM.ticks last bank keys) :=
    DescentFirstMinimumRAM.exec bank sealed keys (show (Bank.mk dense k).Fits w last from ⟨Nat.two_pow_pos _,bankSize,le_rfl⟩) finish
    (by have := Nat.two_pow_pos k; omega)
  have gathered : (jobs.text.seq (scan w dense (2^k) expr)).Exec m sealed
      (jobs.ticks+(4+2^k*(2*expr.work+4))) := by
    intro labels registers slots machine
    exact Procedure.Exec.then ledger packed machine
  intro labels registers slots machine
  exact Procedure.Exec.then gathered win machine

/-- All candidates are compiled from the public dimensions of the directory. -/
theorem bounded (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) :
    CandidateRAM.Bounded (search w ℓ Δ adj base D cap a ptr).1 (search w ℓ Δ adj base D cap a ptr).2 := by
  apply CandidateRAM.seq_bound
  · apply CandidateRAM.seq_bound
    · apply CandidateRAM.batch_bound (steps w ℓ Δ adj base D cap a ptr)
      intro i
      exact RosterCandidate.bounded ..
    · exact CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos _)
  · exact DescentFirstMinimumRAM.code_bound ..

/-- Unrolling all public seeds incurs one candidate cost per nonzero word.
Gathering and selecting the first minimum read a further linear number of
words with the dense address-table lookup charged explicitly. -/
theorem clock_le (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ)
    (unit : ℕ) (one : ∀ i, (steps w ℓ Δ adj base D cap a ptr i).ticks≤unit) :
    (search w ℓ Δ adj base D cap a ptr).2 ≤
      (4+(2^k)*unit)+(4+2^k*(2*(6+5*2^k)+4))+(4+70*2^k) := by
  let r := 2^k
  have jobs := Code.clock_seq (steps w ℓ Δ adj base D cap a ptr) unit one (r-1) le_rfl
  have table : (AllSeedsRAM.gather G (2^ℓ) k base).work=6+5*r := by
    simp [r,AllSeedsRAM.gather,Expr.work,lookupRow_work]; omega
  have cheap := DescentFirstMinimumRAM.length_budget (AllSeedsRAM.winningBase G (2^ℓ) k base)
    (Bank.mk (AllSeedsRAM.gatherBase G (2^ℓ) k base) k) (MultiplierMinimumRAM.keys k)
  simp only [MultiplierMinimumRAM.keys,List.length_map,length_nonzeroWords] at cheap
  have len : r-1≤r := Nat.sub_le ..
  change (stage w ℓ Δ adj base D cap a ptr).ticks+
    (4+2^k*(2*(AllSeedsRAM.gather G (2^ℓ) k base).work+4))+
    DescentFirstMinimumRAM.ticks (AllSeedsRAM.winningBase G (2^ℓ) k base)
      (Bank.mk (AllSeedsRAM.gatherBase G (2^ℓ) k base) k) (MultiplierMinimumRAM.keys k) ≤ _
  rw [table]
  exact Nat.add_le_add (Nat.add_le_add_right (jobs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) _)) _)
    (cheap.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ len) _))

/-- RAM time, including all multiplier trials and the first-minimum scan,
is linear in both population and group count and polynomial in the public
local multiplier alphabet. -/
theorem cost_le (w ℓ Δ adj base D cap : ℕ) (a : Bits k) (ptr : Fin G→Fin (2^ℓ)→ℕ) :
    (search w ℓ Δ adj base D cap a ptr).2 ≤ 2000*(G+1)*(2^ℓ+1)*(k+1)*(Δ+1)*(2^k+1)^5 := by
  let r := 2^k
  let H := 2^ℓ
  let unit := 1000*(G+1)*(H+1)*(k+1)*(Δ+1)*(r+1)^4
  have all := clock_le w ℓ Δ adj base D cap a ptr unit (fun i=>
    RosterCandidate.ticks_bound w ℓ Δ adj (AllSeedsRAM.slot G H k base i.val) D cap a ptr (seedAt k i))
  apply all.trans
  change (4+r*unit)+(4+r*(2*(6+5*r)+4))+(4+70*r)≤2000*(G+1)*(H+1)*(k+1)*(Δ+1)*(r+1)^5
  dsimp only [unit]
  zify
  apply sub_nonneg.mp
  ring_nf
  positivity

end Hierarchy.DescentColonies.RosterSearch

end
end OAI
