import OAI.Hierarchy.DescentNamedTerminalPreflight

namespace OAI
/-! # Finite calibration of the actual issued terminal fields and original cohort census -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentTerminalLocalPortBook DescentSIMDLookup
noncomputable section
variable (x:Spec)

def quarterBits : ℕ :=
  max (x.paidBits*x.paidLanes) (max x.actorLanes
    (max (Nat.clog 2 (chunks x.groups x.paidLanes))
      (Nat.clog 2 (x.scalar.blocks*chunks x.groups x.actorLanes))))

def halfBits : ℕ :=
  max (x.frozenBits+x.cohortBits) (max x.externalBits
  (max (x.scalar.pointerBits*x.scalar.columns+Nat.clog 2 (x.scalar.columns+1))
  (max (3*x.scalar.countBits+2)
  (max (x.printBits*x.strips+Nat.clog 2 (x.strips+1))
  (max (x.cableCellBits*x.widthColumns+Nat.clog 2 (x.widthColumns+1))
  (max (Nat.clog 2 (Book.WeightShelf.words x.vertices x.arguments))
  (max (Nat.clog 2 x.controlBytes) (max (Nat.clog 2 x.controlShape.limit)
  (max (Nat.clog 2 (x.cableCap+1)) (Nat.clog 2 (2^x.cohortBits*x.publicGrains+1)))))))))))

def registerBits := max (2*x.halfBits) (4*x.quarterBits)
def scanScale := max 1 (max ((x.scalar.columns+16)*x.scalar.blocks)
  (max x.strips (max ((x.widthColumns+1)*x.degree) (2^x.cohortBits))))
def paidSize := x.paidRows+x.headerRows

/-- The exponent test is on the bits in the concrete register fields and immutable
keys. The remaining term is one scan of each charged host slot or physical row. -/
theorem calibrated (h rate paid:ℕ) (keys:x.registerBits≤h) (width:x.scanScale≤rate)
    (rows:x.paidSize≤paid) (ptr:0<x.scalar.columns) (strips:0<x.strips)
    (population:x.cohorts≤x.scalar.shops*2^x.cohortBits) : x.ScalarRoom h rate paid := by
  simp only [registerBits,max_le_iff] at keys
  have half:x.halfBits≤h/2:=by omega
  have quarter:x.quarterBits≤h/4:=by omega
  simp only [halfBits,max_le_iff] at half
  simp only [quarterBits,max_le_iff] at quarter
  simp only [scanScale,max_le_iff] at width
  rcases half with ⟨incoming,old,ptrBits,cntBits,bookBits,cableBits,weightBits,
    controlBits,shiftBits,grainBits,pubBits⟩
  obtain ⟨paidWidth,actorWidth,paidLen,actorLen⟩:=quarter
  obtain ⟨one,primitive,stripCount,cables,cohorts⟩:=width
  have lift (n j:ℕ) (low:Nat.clog 2 n≤j) : n≤2^j :=
    (Nat.le_pow_clog (by decide : 1<2) n).trans (Nat.pow_le_pow_right (by decide) low)
  have weight:=lift _ _ weightBits
  have volume:=population.trans (Nat.mul_le_mul_left x.scalar.shops cohorts)
  exact ⟨one,incoming,paidWidth,actorWidth,old,lift _ _ paidLen,lift _ _ actorLen,ptr,ptrBits,cntBits,
    strips,bookBits,cableBits,by omega,lift _ _ controlBits,lift _ _ shiftBits,lift _ _ grainBits,
    lift _ _ pubBits,primitive,stripCount,cables,by omega,rows⟩
end
end Hierarchy.DescentTerminalPreflightSpace.Spec

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

open DescentTerminalPreflightSpace
open Computability.BorderVNP.FragmentBucket
namespace Branch

variable {tail:ℕ} (base:S.baseGroups=2^tail) (L:PreflightFormat)
local notation "spec" => preflightSpec X G S k g p tail L
local notation "H" => S.hostSize S.length
local notation "f" => b.path.frozen
local notation "E" => Fintype.card (Port P X.width)
local notation "homes" => cohortHome X G S b hp base
open scoped BigOperators

include hp base b in
theorem preflight_population : (spec).cohorts≤H*2^(spec).cohortBits := by
  classical
  change E*2^(k*S.length)≤H*2^(8+S.capGain*S.length)
  rw [←b.path.frozen_age]
  calc
    E*2^f = Fintype.card (Fin (E*2^f)) := (Fintype.card_fin _).symm
    _ = ∑i:Fin H,Fintype.card {z // homes z=i} := by
      rw [←Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv homes).symm
    _ ≤ ∑_:Fin H,2^(8+S.capGain*S.length) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_congr (DescentTerminalCohortRanks.numbered homes i),Fintype.card_fin]
      exact cohort_cap X G S b hp base i
    _ = H*2^(8+S.capGain*S.length) := by simp

include hp base b in
theorem preflight_extent (h₀ origin:ℕ) (keys:(spec).registerBits≤h₀) (ptr:0<L.columns) :
    (spec).maskBase origin≤origin+512*(2^(h₀/2)+H*(spec).scanScale+(spec).paidSize+1) := by
  apply (spec).extent_rate h₀ (spec).scanScale (spec).paidSize origin
  exact (spec).calibrated _ _ _ keys le_rfl le_rfl ptr (preflight_strips X G S (k:=k) (g:=g)
    (p:=p) (tail:=tail) L) (preflight_population X G S b hp base L)
end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
