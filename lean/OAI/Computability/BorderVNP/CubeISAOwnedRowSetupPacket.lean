import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupSingle
import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupLiterals

/-! # Native setup of the strict symbol-pair packet loop -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedRowSetup

open Cube Cube.Physical.Owned Cube.Tally VPVNP.BurstRAM

/-- Convert the loaded endpoint count and grouping place into packet trial counts. -/
def packetRadices : Code := .block [.binary .mul 11 10 10,.binary .mul 12 12 12,
  .binary .mul 19 19 13,.binary .mul 19 19 2]

/-- Native packet setup. The static gadget parameters use the fixed literal table;
all layout-dependent operands are loaded from the primary frame and its two arrays. -/
def packet (n b h K s : ℕ) : Code := .seq single (.seq packetRadices (parameters n b h K s))

/-- The initializer never branches on a guessed bit or invokes a private routine. -/
theorem packet_deterministic (n b h K s : ℕ) : (packet n b h K s).deterministic = true := by
  simp only [packet,Code.deterministic,single_swap_deterministic.1,
    show packetRadices.deterministic = true by decide,parameters_deterministic,Bool.and_true]

/-- Neither packet setup nor its fixed scalar construction emits signed events or private choices. -/
theorem packet_unsigned (n b h K s : ℕ) : (packet n b h K s).unsigned = true := by
  simp only [packet,Code.unsigned,show single.unsigned = true by decide,
    show packetRadices.unsigned = true by decide,parameters_unsigned,Bool.and_true]

private theorem held_ne {j : Reg} (hj : Held j) : j ≠ 11 ∧ j ≠ 12 ∧ j ≠ 19 ∧ j ≠ 8 ∧ j ≠ 9 ∧
    j ≠ 16 ∧ j ≠ 57 ∧ j ≠ 58 := by
  simp only [Held,List.mem_cons,List.mem_nil_iff,or_false] at hj
  rcases hj with h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> decide

/-- An addressed frame, the selected grouping coordinate and the endpoint registers supply
every input of the packet iterator and its vertex/selector callback. -/
theorem packet_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w)
    (m : Memory w) (l : Layout) (i : Fin (n+1)) (pair : Symbols l.d) (b h K s : ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (trials : packetTrials n l.d l.blocks < 2^w) (widthFit : selectorWidth n K h < 2^w)
    (countFit : Fintype.card (Selector n K h) < 2^w) (strideFit : bankWidth n b h K s < 2^w)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (ha : readings r 14 = pair.val.1.val) (hb : readings r 15 = pair.val.2.val) :
    BoundedRun pub mac (packet n b h K s) r m (packet n b h K s).slots (fun z =>
      Owned.packetReady (blocks := l.blocks) i pair (bankWidth n b h K s) l.bank 0 z ∧
      z.reg 5 = n ∧ z.reg 8 = selectorWidth n K h ∧ z.reg 9 = Fintype.card (Selector n K h) ∧
      (∀ j, Held j → z.reg j = readings r j) ∧ z.mem = readings m) := by
  apply (prepare_run pub mac r m l i loaded fit h0 h1 axis).seq
  rintro t mt ⟨p,keep,mem⟩
  have hi : l.d^i.val ≤ l.d^n := Nat.pow_le_pow_right (Nat.zero_lt_of_lt pair.val.1.isLt) (by omega)
  have place : l.d^i.val*l.d^i.val < 2^w := (Nat.mul_le_mul hi hi).trans_lt fit.endpoints
  have bound : singlePairTrials n l.d*l.blocks*2 = packetTrials n l.d l.blocks := by
    simp only [singlePairTrials,packetTrials,mul_pow]; ac_rfl
  have count : singlePairTrials n l.d*l.blocks*2 < 2^w := bound ▸ trials
  have h10 : readings t 10 = l.d := p.radix
  have h12 : readings t 12 = l.d^i.val := p.place
  have h13 : readings t 13 = l.blocks := p.blocks
  have h19 : readings t 19 = singlePairTrials n l.d := p.trials
  have h2 : readings t 2 = 2 := p.two
  have safe : packetRadices.fixedSafe w (readings pub) (.ofWords t mt) := by
    simp (config := {decide := true}) [packetRadices,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,
      Code.safeReadOnly,addressOp,addressOpFits,NatState.ofWords,h10,h12,h13,h19,h2,place,fit.square,count]
    omega
  apply (Code.runFixed packetRadices pub mac t mt safe).seq
  rintro u mu eu
  have ur := congrArg NatState.reg eu
  have um : readings mu = readings mt := congrArg NatState.mem eu
  have ku (j : Reg) (j11 : j ≠ 11) (j12 : j ≠ 12) (j19 : j ≠ 19) : readings u j = readings t j := by
    change (NatState.ofWords u mu).reg j = _
    rw [eu]
    simp [packetRadices,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,j11,j12,j19]
  have u11 : readings u 11 = l.d*l.d := by
    simpa (config := {decide := true}) [packetRadices,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,NatState.ofWords,h10] using congrFun ur 11
  have u12 : readings u 12 = (l.d*l.d)^i.val := by
    simpa (config := {decide := true}) [packetRadices,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,NatState.ofWords,h12,mul_pow] using congrFun ur 12
  have u19 : readings u 19 = packetTrials n l.d l.blocks := by
    simpa (config := {decide := true}) [packetRadices,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,NatState.ofWords,h19,h13,h2,bound] using congrFun ur 19
  have hw : 1 < 2^w := by have h := fit.primary; omega
  apply (parameters_run pub mac u mu n b h K s widthFit countFit strideFit hw).mono le_rfl
  rintro z ⟨w8,c9,stride,kz,zm⟩
  have fixed (j : Reg) (hj : Held j) : z.reg j = readings r j := by
    obtain ⟨j11,j12,j19,j8,j9,j16,j57,j58⟩ := held_ne hj
    exact (kz _ j8 j9 j16 j57 j58).trans ((ku _ j11 j12 j19).trans (keep _ hj))
  have preserved (j : Reg) (j8 : j ≠ 8) (j9 : j ≠ 9) (j16 : j ≠ 16) (j57 : j ≠ 57) (j58 : j ≠ 58)
      (j11 : j ≠ 11) (j12 : j ≠ 12) (j19 : j ≠ 19) : z.reg j = readings t j :=
    (kz _ j8 j9 j16 j57 j58).trans (ku _ j11 j12 j19)
  refine ⟨⟨(fixed _ (by decide)).trans h0,(fixed _ (by decide)).trans h1,?_,?_,?_,?_,?_,
    (fixed _ (by decide)).trans ha,(fixed _ (by decide)).trans hb,stride,?_,?_,?_⟩,?_,w8,c9,fixed,zm.trans (um.trans mem)⟩
  · exact (preserved 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.two
  · exact (preserved 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.radix
  · exact (kz 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans u11
  · exact (kz 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans u12
  · exact (preserved 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.blocks
  · exact (preserved 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.bank
  · exact (preserved 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.cursor
  · exact (kz 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans u19
  · exact (preserved 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.dim

end RoutingISA.OwnedRowSetup

end BorderVNP
end Computability
end OAI
