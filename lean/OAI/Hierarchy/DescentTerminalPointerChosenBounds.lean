import OAI.Hierarchy.DescentTerminalPointerReachedWidths
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! # Terminal pointer source widths on the actual remixed branch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "portCount" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (portCount*2^f)



local notation "homes" => cohortHome X G S b hp base
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "old" => b.origin.source
local notation "frozen" => (fun t:Cohort=>(finProdFinEquiv.symm t : Fin portCount×Fin (2^f)).2)
local notation "codeAt" => DescentTerminalFrozenRoster.book homes frozen

open DescentCompiler.TerminalScale DescentTerminalPointerDigits DescentSharedCableNames
local notation "tokens_" => S.epochPower^S.localTokenExponent
local notation "K_" => NativeBranch.privateSlotCapacity G S R
local notation "cap_" => DescentOperandWidth.publicCap S
local notation "bits_" => DescentOperandWidth.recordBits G S k tail R (A).degree p
local notation "side_" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "sup_" r_ => max (DescentOperandWidth.rate G S r_ 2) 4

include hp base in
/-- The real source dimensions used in the terminal pointer reader include the actual calendar,
the reset copy chart and the true operand-format width shared with the ordinary and reset writes. -/
theorem pointer_exponents (τ κ r₀ B h₀ : ℕ) (hb : 0<B) (epoch:S.height=Nat.log 2 h₀/(2*B))
    (limit:p≤h₀) (kBound:k≤κ*(S.height+1)) (res:tail=τ*(S.height+1))
    (drift:R+1≤ scale S.height r₀)
    (late:max (τ+κ*(S.rounds+2)) (max (DescentOperandWidth.rate G S r₀ 2+1) (2*B))≤2^(S.height+1)) :
    (∀z∈[tokens_,initialBits,f+1,cap_,Nat.clog 2 (tokens_+1),Nat.clog 2 (K_+1),bits_,side_],
        z≤ scale S.height (sup_ r₀)) ∧
    (∀z∈[(A).cap,tokens_,K_],z≤ scale S.height (sup_ r₀)) := by
  let J:=S.height
  let e:=sup_ r₀
  let M:=DescentOperandWidth.bound G S R (A).degree
  let E:=scale J e
  have up (u w : ℕ) (leq:u≤w) : scale J u≤ scale J w:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ leq)
  have three : (A).degree=3:=b.target.branch
  have small:(A).degree≤ scale J 2:=by
    rw [three];change 3≤2^(2*(J+1))
    exact (by decide : 3≤2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have val : M≤E:=(DescentOperandWidth.value_bound G S R (A).degree r₀ 2 drift small).trans
    (up _ _ (Nat.le_max_left ..))
  have raw : DescentOperandWidth.raw S≤M :=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have Kfit : K_≤E:=((Nat.le_max_left ..).trans (Nat.le_max_left ..)).trans val
  have capfit : cap_≤E:=by
    change 11*cap_+12≤M at raw
    omega
  have realCap : (A).cap≤cap_:=b.target.valid.capacity
  have countFit : tokens_≤K_:=by
    unfold NativeBranch.privateSlotCapacity
    have power:=Nat.pow_le_pow_right (Nat.two_pow_pos S.height : 0<S.epochPower)
      (Nat.le_add_left S.localTokenExponent (operandExponent G S))
    exact power.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have logfit (n : ℕ) : Nat.clog 2 (n+1)≤n:=(Nat.clog_le_iff_le_pow (by decide)).2 Nat.lt_two_pow_self
  have ptr : bits_≤ scale J 3 :=by
    rw [res]
    exact DescentOperandWidth.calendar_scale G S k τ κ R (A).degree r₀ 2 p h₀ B hb epoch limit kBound drift small late
  have stamp : initialBits≤bits_ :=by
    exact (((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_left ..) :
      S.stampBits k tail≤DescentOperandWidth.recordBits G S k tail R (A).degree p)
  have frozenFit : f+1≤E:=by
    have dims:=(trace).width
    have below : f≤ scale J 3:=(by omega : f≤ initialBits).trans (stamp.trans ptr)
    have factor : 1≤ scale J 3 :=Nat.two_pow_pos _
    have twice : 2≤ scale J 1 :=Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 1≤1*(J+1))
    have step : f+1≤ scale J 4 :=by
      rw [show 4=3+1 by decide,←scale_mul]
      exact (show f+1≤ scale J 3*2 by omega).trans (Nat.mul_le_mul_left _ twice)
    exact step.trans (up _ _ (Nat.le_max_right ..))
  have sideFit:side_≤E:=by
    have adjacent : Packed.bits (A).degree=2:=by rw [three];decide
    have width : Packed.bits (A).cap≤cap_:=(logfit (A).cap).trans realCap
    change 11*cap_+12≤M at raw
    unfold DescentSignedCableCodec.width;rw [adjacent];omega
  have basic : bits_≤E:=ptr.trans (up 3 e (by dsimp [e];omega))
  constructor
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact countFit.trans Kfit
    · exact stamp.trans basic
    · exact frozenFit
    · exact capfit
    · exact (logfit _).trans (countFit.trans Kfit)
    · exact (logfit _).trans Kfit
    · exact basic
    · exact sideFit
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl
    · exact realCap.trans capfit
    · exact countFit.trans Kfit
    · exact Kfit

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
