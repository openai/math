import OAI.Hierarchy.DescentNamedPreflightFormat

namespace OAI
/-! # Field widths of the reached pointer, scalar, socket, and directory RAM -/
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

open DescentCompiler.TerminalScale DescentTerminalPointerDigits
variable {tail:ℕ} (base:S.baseGroups=2^tail) (boundary:ℕ) (op:RotorSpec) (headers paid:ℕ)
local notation "fmt" => geometryFormat G S k g p tail boundary R op headers paid
local notation "issuedSpec" => preflightSpec X G S k g p tail fmt
local notation "cap" => (capCalendar G.b S.rounds g S.height).prod*256
local notation "N" => S.epochPower^S.localTokenExponent
local notation "K" => NativeBranch.privateSlotCapacity G S R
local notation "G₀" => S.groupCount S.length
local notation "V" => G₀*2^k
local notation "A₀" => NativeBranch.localLimit G S
local notation "initialWidth" => S.groupWidth k tail 0+k
local notation "frozen" => k*S.length
local notation "cb" => 8+S.capGain*S.length
local notation "raw" => DescentOperandWidth.recordBits G S k tail R 3 p
local notation "side" => DescentSignedCableCodec.width 3 cap
local notation "extent" => actualSpan G S op boundary p R
local notation "J" => S.height

include b hp base in
omit b in
theorem geometry_short_fields (u:ℕ) (positive:0<u)
    (ptrWidths:∀z∈[N,initialWidth,frozen+1,2^cb,Nat.clog 2 (N+1),Nat.clog 2 (K+1),raw,side],z≤u)
    (local_:∀z∈[cap,N,K],z≤u)
    (groupRoom:G₀≤u) (blockRoom:2^k≤u) (rowRoom:extent≤u)
    (pubFormat:Nat.clog 2 (boundary+1)≤u) (grain:G.b^(S.rounds*J)*G.b≤u) :
    ∀z∈(issuedSpec).shortFields,z≤16*u^3 := by
  simp only [List.forall_mem_cons] at ptrWidths local_
  obtain ⟨ns,mat,fr,band,nBits,argBits,ptr,edge,_⟩:=ptrWidths
  obtain ⟨capFit,nfit,afit,_⟩:=local_
  have h1:u≤u^2:=by simpa [pow_two] using Nat.le_mul_of_pos_right u positive
  have h2:u^2≤u^3:=Nat.pow_le_pow_right positive (by decide)
  have sq (x y:ℕ) (xx:x≤u) (yy:y≤u) : x*y≤u^2:=by simpa only [pow_two] using Nat.mul_le_mul xx yy
  have active:=sq _ _ groupRoom blockRoom
  have count:=sq _ _ groupRoom rowRoom
  have rare:0<G₀:=by simp [AtomSchedule.groupCount,base]
  have got:=width_by_group rare positive mat fr band ns nBits argBits ptr edge
  have atMost:G₀*u^2≤u^3:=by
    exact (Nat.mul_le_mul_right (u^2) groupRoom).trans_eq (pow_succ' u 2).symm
  have toks:=sq _ _ nfit afit
  have candidates:columns cap N K≤8*u^2+2*u:=by unfold columns;omega
  have rates:2^cb≤u:=band
  have initial_:cb≤u:=(Nat.lt_two_pow_self.le).trans rates
  have publicAux:G.b≤u:=by
    have hb:0<G.b:=by have:=G.paid;omega
    exact (Nat.le_mul_of_pos_left G.b (Nat.pow_pos hb)).trans grain
  have localRate:A₀≤2*u^2:=by
    change 2*G.b*2^cb≤2*u^2
    rw [Nat.mul_assoc];exact Nat.mul_le_mul_left 2 (sq _ _ publicAux band)
  have allPin:publicRate G S (p:=p) (k:=k) (tail:=tail)=V*(G.b^(S.rounds*J)*G.b):=by
    change 2^(S.groupWidth k tail S.length+k)*(S.firstWidth G.b p/p)=_
    rw [AtomSchedule.firstWidth,S.grain_initial,Nat.mul_assoc,Nat.mul_div_cancel_left _ hp]
    simp [AtomSchedule.groupWidth,AtomSchedule.groupCount,base,pow_add]
  have total:V*(G.b^(S.rounds*J)*G.b)≤u^3:=by
    simpa [pow_succ] using Nat.mul_le_mul active grain
  have full:V*extent≤u^3:=by simpa [pow_succ] using Nat.mul_le_mul active rowRoom
  have window:NativeBranch.binLimit (k:=k) S≤3*u^2+6:=by unfold NativeBranch.binLimit;omega
  have cab:=sq _ _ groupRoom edge
  have lengths : G₀ * max (max 1 (Nat.clog 2 (boundary+1))) side ≤ u^2 := sq _ _ groupRoom (max_le (max_le positive pubFormat) edge)
  have priceBits : Nat.clog 2 (p+1)≤raw:=
    ((Nat.clog_le_iff_le_pow (by decide : 1<2)).2
      (show p+1≤2^(Nat.log 2 p+1) from Nat.lt_pow_succ_log_self (by decide) _)).trans (Nat.le_max_right ..)
  have factor : S.censusExponent≤2*S.localTokenExponent:=by
    unfold AtomSchedule.censusExponent AtomSchedule.localTokenExponent AtomSchedule.localGrainExponent
      AtomSchedule.localCapacityExponent
    omega
  have exposure : J*S.censusExponent≤2*(J*S.localTokenExponent):=by
    calc
      J*S.censusExponent≤J*(2*S.localTokenExponent):=Nat.mul_le_mul_left J factor
      _ = 2*(J*S.localTokenExponent):=by ac_rfl
  have exponentFit : J*S.localTokenExponent≤N:=by
    unfold AtomSchedule.epochPower
    rw [←pow_mul]
    exact Nat.lt_two_pow_self.le
  have census : S.censusBits p≤3*u:=by
    unfold AtomSchedule.censusBits
    omega
  have chosen:=got.trans atMost
  have empty : ∀ z ∈ ([] : List ℕ), z ≤ 16*u^3 := by simp
  simp only [DescentTerminalPreflightSpace.Spec.shortFields,List.forall_mem_cons]
  change frozen≤_ ∧ cb≤_ ∧ 2^cb≤_ ∧ G₀≤_ ∧ G₀≤_ ∧ G₀≤_ ∧ S.censusBits p≤_ ∧ cb+1≤_ ∧
    2^k≤_ ∧ columns cap N K≤_ ∧ inputWidth G₀ N initialWidth frozen (2^cb) (Nat.clog 2 (N+1))
      (Nat.clog 2 (K+1)) raw side≤_ ∧ G₀*extent≤_ ∧ 3≤_ ∧ cap≤_ ∧ 2+G₀*side≤_ ∧ G.b≤_ ∧
    publicRate G S (p:=p) (k:=k) (tail:=tail)≤_ ∧ 2+G₀*max (max 1 (Nat.clog 2 (boundary+1))) side≤_ ∧
    V≤_ ∧ A₀≤_ ∧ NativeBranch.binLimit (k:=k) S≤_ ∧ max 1 (V*extent)≤_ ∧ (∀ z ∈ ([] : List ℕ), z ≤ 16*u^3)
  rw [allPin]
  simp only [max_le_iff]
  repeat' apply And.intro
  all_goals first | exact empty | omega
end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
