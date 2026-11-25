import OAI.Hierarchy.DescentColonyAllSeedsRAM

namespace OAI
/-! # The ordinary subround reads its chosen multiplier from native RAM -/

namespace Hierarchy.DescentColonies.AllSeedsRAM
open DescentGL DescentBinaryField ProtocolRAM NativeBatch
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing

variable {w G H k : ℕ}

def winningBase (G H k base : ℕ) := gatherBase G H k base+2^k

def search (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) :=
  let dense := gatherBase G H k base
  let job := stage w base D cap a incoming ptr
  let e := gather G H k base
  let keys := MultiplierMinimumRAM.keys k
  ((job.text.seq (scan w dense (2^k) e)).seq
    (DescentFirstMinimumRAM.code w (winningBase G H k base) ⟨dense,k⟩ keys),
   job.ticks+(4+2^k*(2*e.work+4))+DescentFirstMinimumRAM.ticks (winningBase G H k base) ⟨dense,k⟩ keys)

def afterSearch (base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (m : Memory w) : Memory w :=
  let dense := gatherBase G H k base
  let old := (stage w base D cap a incoming ptr).after m
  let packed := ProtocolRAM.image dense (2^k) (gather G H k base) old
  DescentFirstMinimumRAM.after (winningBase G H k base) ⟨dense,k⟩ packed (MultiplierMinimumRAM.keys k)

/-- The only non-public inputs to the multiplier selection are the previous
actual measured loads. Neither candidate scores nor a minimizing row are inputs. -/
theorem selection (base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (m : Memory w) (weights : Fin G→Fin H→Block k→ℕ) (hk : 0<k)
    (old : ∀g i,ptr g i+2^k≤base) (room : winningBase G H k base+(2^k-1)<2^w)
    (capFit : cap<2^w) (bill : G*(H*2^k)<2^w) (B : ℕ) (reserve : 2^k*B<2^w)
    (limit : ∀g v x,weights g v x≤B) (stored : ∀g i (x : Block k),m (ptr g i+x.val)=(weights g i x:Word w)) :
    let Q := uniformColonyScore incoming weights D cap a
    let program := search w base D cap a incoming ptr
    let out := afterSearch base D cap a incoming ptr m
    ∃ μ : Nonzero k,
      program.1.Exec m out program.2 ∧
      (scanMinimum Q (nonzeroWords k)).1=some (μ,Q μ) ∧
      (∀ν,Q μ≤Q ν) ∧
      out (winningBase G H k base+((2^k-1)-1))=(MultiplierMinimumRAM.key μ:Word w) ∧
      ∀u<base,out u=m u := by
  let job := stage w base D cap a incoming ptr
  let dense := gatherBase G H k base
  let lastBase := winningBase G H k base
  let e := gather G H k base
  let scored := ProtocolRAM.image dense (2^k) e (job.after m)
  let Q := uniformColonyScore incoming weights D cap a
  have denseFit : dense+2^k<2^w := by change (dense+2^k)+(2^k-1)<2^w at room;omega
  have bits : 2^k<2^w := by omega
  have times := Nat.mul_le_mul_right (stride G H k) (Nat.sub_le (2^k) 1)
  have space := Nat.le_pow_clog (by decide : 1<2) ((2^k)*stride G H k)
  have firstBank : slot G H k base (2^k-1)≤dense :=
    Nat.add_le_add_left (times.trans space) base
  have enough : slot G H k base (2^k-1)<2^w :=
    firstBank.trans_lt ((Nat.le_add_right dense (2^k)).trans_lt denseFit)
  have native : job.text.Exec m (job.after m) job.ticks := by
    intro labels registers slots machine
    exact run w base D cap a incoming ptr old enough m machine
  have recorded := read base D cap a incoming ptr m weights old enough bits.le capFit stored
    (fun μ g d _ v x=>CandidateRAM.interval_room weights a μ B limit reserve g d v x)
  obtain ⟨packedRun,rows⟩ := pack base D cap a incoming ptr (job.after m) Q denseFit recorded
  have scoreFit (μ : Nonzero k) : Q μ<2^w := by
    apply lt_of_le_of_lt _ bill
    unfold Q uniformColonyScore
    calc
      _ ≤ ∑ _ : Fin G,H*2^k := Finset.sum_le_sum fun i _=>by
        rw [←Scan.FinRows.score_eq_leafScore]
        exact PhysicalCensus.score_le ..
      _ = _ := by simp
  obtain ⟨_,first⟩ := scanMinimum_spec Q (nonzeroWords k)
  cases why : (scanMinimum Q (nonzeroWords k)).1 with
  | none =>
    rw [why] at first
    have z := congrArg List.length first
    have more : 1<2^k := Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt hk)
    simp [length_nonzeroWords] at z;omega
  | some p =>
    rw [why] at first
    obtain ⟨μ,c⟩ := p
    obtain ⟨cost,best⟩ := first
    change c=Q μ at cost
    subst c
    obtain ⟨pick,actual,_⟩ := MultiplierMinimumRAM.chosen scored dense Q
      (show (Bank.mk dense k).Fits w lastBase from ⟨Nat.two_pow_pos _,bits,le_rfl⟩)
      room scoreFit rows why
    have scoredRun : (job.text.seq (scan w dense (2^k) e)).Exec m scored
        (job.ticks+(4+2^k*(2*e.work+4))) := by
      intro labels registers slots machine
      exact Procedure.Exec.then native packedRun machine
    refine ⟨μ,?_,why,fun ν=>best ν (mem_nonzeroWords ν),actual,?_⟩
    · intro labels registers slots machine
      exact Procedure.Exec.then scoredRun pick machine
    intro u lo
    have below : u<dense := lo.trans_le (Nat.le_add_right ..)
    have saved := DescentFirstMinimumRAM.frame lastBase ⟨dense,k⟩ scored (MultiplierMinimumRAM.keys k) u
      (below.trans_le (Nat.le_add_right ..))
    have keep := Code.frame_seq (steps w base D cap a incoming ptr) u (fun j M=>
      CandidateRAM.below _ _ _ _ _ _ _ M u (lo.trans_le (Nat.le_add_right ..))) m (2^k-1) le_rfl
    exact saved.trans ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl below)).trans keep)

end Hierarchy.DescentColonies.AllSeedsRAM

end OAI
