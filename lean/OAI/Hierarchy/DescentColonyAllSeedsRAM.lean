import OAI.Hierarchy.DescentColonyCandidateRAM
import OAI.Hierarchy.DescentMultiplierMinimumRAM

namespace OAI
/-! # The native multiplier score ledger, before reading its first minimizer -/

namespace Hierarchy.DescentColonies.AllSeedsRAM
open DescentGL DescentBinaryField DescentGLScoreRAM ProtocolRAM NativeBatch
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {w G H k : ℕ}

def stride (G H k : ℕ) := G*CandidateRAM.stride H k+1

def slot (G H k base j : ℕ) := base+j*stride G H k

def last (G H k base j : ℕ) := CandidateRAM.output G H k (slot G H k base j)

theorem next (G H k base j : ℕ) : last G H k base j+1=slot G H k base (j+1) := by
  dsimp [last,slot,stride,CandidateRAM.output];ring

theorem mono (G H k base : ℕ) {i j : ℕ} (h : i≤j) : slot G H k base i≤ slot G H k base j :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

def steps (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ)
    (i : Fin (2^k-1)) : Code w :=
  CandidateRAM.code w (slot G H k base i.val) incoming ptr D cap a (seedAt k i)

def stage (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) :=
  Code.seq (steps w base D cap a incoming ptr) (2^k-1) le_rfl

theorem run (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : slot G H k base (2^k-1)<2^w) :
    (stage w base D cap a incoming ptr).exec := by
  apply Code.exec_seqAll
  intro i m
  apply CandidateRAM.run
  · exact fun g v=>(old g v).trans (Nat.le_add_right ..)
  · change last G H k base i.val+1<2^w
    rw [next]
    exact (mono G H k base i.isLt).trans_lt room

theorem read (base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H))
    (ptr : Fin G→Fin H→ℕ) (m : Memory w) (weight : Fin G→Fin H→Block k→ℕ)
    (old : ∀g i,ptr g i+2^k≤base) (room : slot G H k base (2^k-1)<2^w)
    (bits : 2^k≤2^w) (capRoom : cap<2^w)
    (loads : ∀g i (x : Block k),m (ptr g i+x.val)=(weight g i x:Word w))
    («partial» : ∀(μ : Nonzero k) g d,d<k→∀v x,(Scan.readWeights (multiplierLoad (weight g) a μ.val) d v x).sum<2^w) :
    ∀ i : Fin (2^k-1),(stage w base D cap a incoming ptr).after m (last G H k base i.val)=
      (uniformColonyScore incoming weight D cap a (seedAt k i):Word w) := by
  let jobs := steps w base D cap a incoming ptr
  let Init := fun M : Memory w=>∀g i (x : Block k),M (ptr g i+x.val)=(weight g i x:Word w)
  let Claim := fun i : Fin (2^k-1)=>fun M : Memory w=> M (last G H k base i.val)=
      (uniformColonyScore incoming weight D cap a (seedAt k i):Word w)
  have stable (j : Fin (2^k-1)) (n : Memory w) (hi : Init n) : Init ((jobs j).after n) := by
    intro g i x
    apply (CandidateRAM.below _ _ _ _ _ _ _ n _ ?_).trans (hi g i x)
    exact (by have := old g i;have := x.isLt; omega : ptr g i+x.val<base).trans_le (Nat.le_add_right ..)
  have fresh (i : Fin (2^k-1)) (n : Memory w) (hi : Init n) : Claim i ((jobs i).after n) := by
    apply CandidateRAM.published
    · exact fun g v=>(old g v).trans (Nat.le_add_right ..)
    · change last G H k base i.val+1<2^w
      rw [next]; exact (mono G H k base i.isLt).trans_lt room
    · exact bits
    · exact capRoom
    · exact hi
    · exact «partial» _
  have keep (i j : Fin (2^k-1)) (prior : i<j) (n : Memory w) (ok : Claim i n) : Claim i ((jobs j).after n) := by
    exact (CandidateRAM.below _ _ _ _ _ _ _ n _ (by
      have h := mono G H k base prior
      rw [←next] at h
      omega)).trans ok
  exact fun i=>(Code.read_seq jobs Init stable Claim fresh keep m loads _ le_rfl).2 i i.isLt

/-- Pack the candidate score words into a single naturally indexed bank.
Ordinal zero is a dummy. Every positive seed reads its own computed score. -/
def bitsNeeded (G H k : ℕ) := Nat.clog 2 ((2^k)*stride G H k)

def gatherBase (G H k base : ℕ) := base+2^bitsNeeded G H k

def offset (G H k j : ℕ) := (j-1)*stride G H k+G*CandidateRAM.stride H k

def gather (G H k base : ℕ) : Expr :=
  .lookup ⟨base,bitsNeeded G H k⟩ (lookupRow (2^k) (fun i=>offset G H k i.val))

theorem pack (base _D _cap : ℕ) (_a : Bits k) (_incoming : Fin H→List (Fin H))
    (_ptr : Fin G→Fin H→ℕ) (m : Memory w) (W : Nonzero k→ℕ)
    (room : gatherBase G H k base+2^k<2^w)
    (scores : ∀i : Fin (2^k-1),m (last G H k base i.val)=(W (seedAt k i):Word w)) :
    let g := gather G H k base
    (scan w (gatherBase G H k base) (2^k) g).Exec m (image (gatherBase G H k base) (2^k) g m)
      (4+2^k*(2*g.work+4)) ∧
    ∀μ : Nonzero k,image (gatherBase G H k base) (2^k) g m (gatherBase G H k base+MultiplierMinimumRAM.key μ)=
      (W μ:Word w) := by
  have size : 2^bitsNeeded G H k<2^w := calc
    _ ≤ base+2^bitsNeeded G H k := Nat.le_add_left _ _
    _ ≤ gatherBase G H k base+2^k := Nat.le_add_right _ _
    _ < _ := room
  have rows : 2^k<2^w := (Nat.le_add_left _ _).trans_lt room
  have fit : (gather G H k base).Fits w (gatherBase G H k base) :=
    ⟨⟨Nat.two_pow_pos _,size,le_rfl⟩,lookupRow_fits ..⟩
  refine ⟨?_,?_⟩
  · intro labels registers slots machine
    exact scan_exec (gatherBase G H k base) (2^k) (gather G H k base) m fit room machine
  intro μ
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (show μ∈List.ofFn (seedAt k) from mem_nonzeroWords μ)
  subst μ
  have index : i.val+1<2^k := by have := i.isLt;omega
  let j : Fin (2^k) := ⟨i.val+1,index⟩
  have f : offset G H k j.val<2^bitsNeeded G H k := by
    have hi := Nat.mul_le_mul_right (stride G H k) (show i.val+1≤2^k by omega)
    have upper := Nat.le_pow_clog (by decide : 1<2) ((2^k)*stride G H k)
    rw [Nat.succ_mul] at hi
    dsimp [offset,j,bitsNeeded,stride] at *
    omega
  have readAt : (gather G H k base).eval m (j.val:Word w)=(W (seedAt k i):Word w) := by
    simp only [gather,Expr.eval,lookupRow_eval m _ rows.le j,Bank.read,Bank.size,
      Fin.val_cast_of_lt (f.trans size),Nat.mod_eq_of_lt f]
    simpa [offset,j,last,slot,CandidateRAM.output,Nat.add_assoc] using scores i
  have key : MultiplierMinimumRAM.key (seedAt k i)=j.val := seedAt_code i
  rw [key]
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ m j).trans readAt

end Hierarchy.DescentColonies.AllSeedsRAM

end OAI
