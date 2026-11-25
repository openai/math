import OAI.Computability.BorderVNP.CubeISALocalRowCode

/-! # Installing both scalar and packet trial parameters for a local declaration row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Physical.Owned
open OwnedRowSetup

/-- Native setup keeps both radix systems, their common endpoints, the
caller vertex cursor and the selector metadata used in the eight-word header. -/
structure Primed (l : Layout) (n b h K s i lo hi vertex : ℕ) (r : Reg → ℕ) : Prop where
  zero : r 0 = 0
  one : r 1 = 1
  two : r 2 = 2
  dim : r 5 = n
  tail : r 6 = l.d^n
  place : r 7 = l.d^i
  width : r 8 = selectorWidth n K h
  count : r 9 = Fintype.card (Selector n K h)
  radix : r 10 = l.d
  square : r 11 = l.d*l.d
  squarePlace : r 12 = (l.d*l.d)^i
  blocks : r 13 = l.blocks
  left : r 14 = lo
  right : r 15 = hi
  stride : r 16 = bankWidth n b h K s
  bank : r 17 = l.bank
  cursor : r 18 = 0
  trials : r 19 = packetTrials n l.d l.blocks
  bits : r 21 = l.blocks*l.bc
  literalOne : r 57 = 1
  saved : r 61 = vertex

private theorem parametersOne {w n b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {v y : Bank w} {mv my : Memory w} {es : List (TeamRAM.Event w)}
    (run : Runs pub mac (parameters n b h K s) v mv es y my) (hw : 1 < 2^w) : readings y 57 = 1 := by
  let tail := Code.block [Constants.literal (Constants.digits (selectorWidth n K h)),.copy 8 58,
    Constants.literal (Constants.digits (Fintype.card (Selector n K h))),.copy 9 58,
    Constants.literal (Constants.digits (bankWidth n b h K s)),.copy 16 58]
  have keep (ds : List Bool) : (Constants.literal ds).keeps 57 = true := by
    induction ds with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [Constants.literal,Code.keeps,ih]
  have kt : tail.keeps 57 = true := by simp (config := {decide := true}) [tail,Code.block,Code.keeps,keep]
  change Runs pub mac (.seq (.constant 57 1) tail) _ _ _ _ _ at run
  cases run with
  | atom ha _ _ => cases ha
  | seq f t =>
    have fixed := ((Code.constant 57 1).runFixed pub mac v mv hw).asTest (by decide)
    have e := (fixed.sound f).2
    exact (congrArg Fin.val (t.keepsReg kt)).trans (by simpa [Code.fixedEval,Code.evalNat,NatState.ofWords,readings] using
      (congrArg (fun z : NatState => z.reg 57) e))

/-- Native execution of the common prefix for strict and diagonal rows. -/
theorem prime_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (i : Fin (n+1)) (lo hi : Fin l.d) (b h K s : ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (trials : packetTrials n l.d l.blocks < 2^w) (widthFit : selectorWidth n K h < 2^w)
    (countFit : Fintype.card (Selector n K h) < 2^w) (strideFit : bankWidth n b h K s < 2^w)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (left : readings r 14 = lo.val) (right : readings r 15 = hi.val) :
    BoundedRun pub mac (prime n b h K s) r m (prime n b h K s).slots
      (fun z => Primed l n b h K s i.val lo.val hi.val (readings r 7) z.reg ∧ z.mem = readings m) := by
  apply (prepare_run pub mac r m l i loaded fit h0 h1 axis).seq
  rintro t mt ⟨hp,hold,hm⟩
  apply (snapshot.runFixed pub mac t mt (by simp [snapshot,Code.block,Code.fixedSafe,Code.safeReadOnly])).seq
  rintro u mu hu
  have moved : readings u = (snapshot.fixedEval (readings pub) (.ofWords t mt)).reg := congrArg NatState.reg hu
  have mm : readings mu = readings mt := congrArg NatState.mem hu
  have keep (j : Reg) (h61 : j ≠ 61) (h6 : j ≠ 6) (h7 : j ≠ 7) : readings u j = readings t j := by
    simp [moved,snapshot,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,h61,h6,h7]
  have u6 : readings u 6 = l.d^n := by simpa (config := {decide := true})
    [moved,snapshot,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords] using hp.labels
  have u7 : readings u 7 = l.d^i.val := by simpa (config := {decide := true})
    [moved,snapshot,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords] using hp.place
  have u61 : readings u 61 = readings r 7 := by simpa (config := {decide := true})
    [moved,snapshot,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords] using hold 7 (by decide)
  have hiPow := Nat.pow_le_pow_right (Nat.zero_lt_of_lt lo.isLt) (by omega : i.val ≤ n)
  have place : l.d^i.val*l.d^i.val < 2^w := (Nat.mul_le_mul hiPow hiPow).trans_lt fit.endpoints
  have bound : singlePairTrials n l.d*l.blocks*2 = packetTrials n l.d l.blocks := by
    simp only [singlePairTrials,packetTrials,mul_pow]; ac_rfl
  have cnt : singlePairTrials n l.d*l.blocks*2 < 2^w := bound ▸ trials
  have h10 := (keep 10 (by decide) (by decide) (by decide)).trans hp.radix
  have h12 := (keep 12 (by decide) (by decide) (by decide)).trans hp.place
  have h13 := (keep 13 (by decide) (by decide) (by decide)).trans hp.blocks
  have h19 := (keep 19 (by decide) (by decide) (by decide)).trans hp.trials
  have h2 := (keep 2 (by decide) (by decide) (by decide)).trans hp.two
  have safe : packetRadices.fixedSafe w (readings pub) (.ofWords u mu) := by
    simp (config := {decide := true}) [packetRadices,Code.block,Code.fixedSafe,Code.fixedEval,Code.evalNat,
      Code.safeReadOnly,addressOp,addressOpFits,NatState.ofWords,h10,h12,h13,h19,h2,place,fit.square,cnt]
    omega
  apply (packetRadices.runFixed pub mac u mu safe).seq
  rintro v mv hv
  have regs : readings v = (packetRadices.fixedEval (readings pub) (.ofWords u mu)).reg :=
    congrArg NatState.reg hv
  have vm : readings mv = readings mu := congrArg NatState.mem hv
  have kv (j : Reg) (j11 : j ≠ 11) (j12 : j ≠ 12) (j19 : j ≠ 19) : readings v j = readings u j := by
    simp [regs,packetRadices,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,j11,j12,j19]
  have v11 : readings v 11 = l.d*l.d := by
    simp (config := {decide := true}) [regs,packetRadices,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,h10]
  have v12 : readings v 12 = (l.d*l.d)^i.val := by
    simp (config := {decide := true}) [regs,packetRadices,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,h12,mul_pow]
  have v19 : readings v 19 = packetTrials n l.d l.blocks := by
    simp (config := {decide := true}) [regs,packetRadices,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,h19,h13,h2,bound]
  have hw : 1 < 2^w := by have := fit.primary; omega
  obtain ⟨es,y,my,run,cap,res⟩ := parameters_run pub mac v mv n b h K s widthFit countFit strideFit hw
  obtain ⟨width,count,stride,ky,ym⟩ := res
  have litOne : readings y 57 = 1 := by
    exact parametersOne run hw
  refine ⟨es,y,my,run,cap,?_,ym.trans (vm.trans (mm.trans hm))⟩
  constructor
  all_goals first | exact width | exact count | exact stride | exact litOne | skip
  all_goals rw [ky _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  all_goals first | exact v11 | exact v12 | exact v19 | skip
  all_goals rw [kv _ (by decide) (by decide) (by decide)]
  all_goals first | exact u6 | exact u7 | exact u61 | skip
  all_goals rw [keep _ (by decide) (by decide) (by decide)]
  all_goals first
    | exact hp.two | exact hp.dim | exact hp.radix | exact hp.blocks | exact hp.bank
    | exact hp.cursor | exact hp.bits | exact (hold _ (by decide)).trans h0 | exact (hold _ (by decide)).trans h1
    | exact (hold _ (by decide)).trans left | exact (hold _ (by decide)).trans right

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
