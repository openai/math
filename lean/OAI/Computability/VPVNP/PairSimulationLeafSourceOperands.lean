import OAI.Computability.VPVNP.PairSimulationLeafSourceLoad

/-! # The 38 private leaf-cache values at the paper's public parameters -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM CursorRouting CursorNetwork RAMTape LiveProgram
open LeafRegisterBank LeafStartup
open scoped Fin.CommRing

variable (c : Constants) {p : UniversalMachine.Program} {B n H : ℕ}
  {i : Fin (2^(n^c.chainPower-1))}
  (Q : PrimedInputRAM.Layout ((CounterPublic.spec p c).lengths n i) n (addressWidth B n) H
    (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5)))

private theorem bucket_eval (g : Geometry) :
    (.pow2 (.divConst (.add (.clog2 .n) (.lit 3)) 4) : PublicExpr).eval g = 2^roundedUp 1 4 g.n := by
  change 2^((Nat.clog 2 g.n+3)/4) = _
  rw [roundedUp,pow_one,Nat.clog_pow_left]

/-- The length-only operands and the two own-prefix slots agree with the
actual coefficient counter on every pair, exterior cut and nomination. -/
theorem paper_operands (hB : 1 ≤ B) (hn : 2 ≤ n) (hp : Q.program = p)
    (hbase : Q.scratchBase = 2^CursorBounds.virtualBits B n) (hf : D.Fits) (hroot : D.root.val = 0)
    (hw : 2 ≤ CursorBounds.wordBits B n)
    (hc : 2^CursorBounds.virtualBits B n*2^roundedUp 1 4 n < 2^CursorBounds.wordBits B n)
    (v : Position (CursorBounds.virtualBits B n))
    (buf : Buffers (CursorBounds.virtualBits B n) (2^roundedUp 1 4 n) (CursorBounds.wordBits B n))
    (j : Static 34) :
    let g := AssemblerPublic.geometry B n H
    let lit := CounterPublic.actualPrefix p
    let x := auxiliary D hw hc v buf
    Pieces.word g lit (expr c j) = sourceWord x D.pub j.dest ∧
      match expr c j with
      | .geometry e => e.Fits g (2^g.w)
      | a => a.eval g lit < 2^g.w := by
  let g := AssemblerPublic.geometry B n H
  let d := CursorBounds.virtualBits B n
  let e := roundedUp 1 4 n
  let w := CursorBounds.wordBits B n
  have he := Nat.two_pow_pos e
  have hd := Nat.two_pow_pos d
  have hdFit : 2^d < 2^w := (Nat.le_mul_of_pos_right _ he).trans_lt hc
  have heFit : 2^e < 2^w := (Nat.le_mul_of_pos_left _ hd).trans_lt hc
  have virtualFit := virtualSites_fits (H := H) hB hn hdFit
  have hsite : virtualSites.eval g = 2^d := virtualSites_eval g hn
  have hnine : 9 ≤ w := by
    change 9 ≤ (addressWidth B n+10)^4
    exact (by omega : 9 ≤ addressWidth B n+10).trans (Nat.le_self_pow (by decide) _)
  have hwidth : w < 2^w := Nat.lt_two_pow_self
  cases j with
  | operand j => exact CounterPublic.operands_correct c Q D hB hn hp hbase hf hroot j
  | width => exact ⟨rfl, hwidth,trivial⟩
  | fuel =>
    have hfuel := D.fuel_eq_virtualFuel g rfl
    constructor
    · change Fin.ofNat _ (PrimedCounter.virtualFuel.eval g) = (D.fuel : Word w)
      exact congrArg (Fin.ofNat (2^w)) hfuel.symm
    · exact PrimedCounter.virtualFuel_fits g hnine
  | bucket =>
    have hval := bucket_eval g
    constructor
    · change Fin.ofNat _ _ = ((2^e : ℕ) : Word w)
      exact congrArg (Fin.ofNat (2^w)) hval
    · exact ⟨hval ▸ heFit,virtualFit.2.2.2⟩
  | d =>
    have hval : (.clog2 virtualSites : PublicExpr).eval g = d := by
      change Nat.clog 2 (virtualSites.eval g) = d
      rw [hsite,Nat.clog_pow 2 _ Nat.one_lt_two]
    constructor
    · change Fin.ofNat _ _ = (d : Word w)
      exact congrArg (Fin.ofNat (2^w)) hval
    · exact ⟨hval ▸ (Nat.lt_two_pow_self (n := d)).trans hdFit,virtualFit⟩

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
