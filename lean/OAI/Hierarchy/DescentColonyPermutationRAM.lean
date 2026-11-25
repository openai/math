import OAI.Hierarchy.DescentUniformColony
import OAI.Hierarchy.DescentGLScoreRAM
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native pullback of the actual prior load bank by a multiplier -/

namespace Hierarchy.DescentColonies.PermutationRAM
open DescentGL DescentGLScoreRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

/-- Only the public modulus and candidate enter these two literals. They do
not contain any load data or depend on the expansion history. -/
def present {k : ℕ} (a μ : Bits k) (x : Block k) : ℕ :=
  (((inverseAddresses a μ).get x).1.isSome).toNat

def origin {k : ℕ} (a μ : Bits k) (x : Block k) : ℕ :=
  (((inverseAddresses a μ).get x).1.map Fin.val).getD 0

def expr {k : ℕ} (base : ℕ) (a μ : Bits k) : Expr :=
  .branch .eq (lookupRow (2^k) (present a μ)) (.lit 0) (.lit 0)
    (.lookup ⟨base,k⟩ (lookupRow (2^k) (origin a μ)))

theorem fits {w k out base : ℕ} (a μ : Bits k) (input : (Bank.mk base k).Fits w out) :
    (expr base a μ).Fits w out :=
  ⟨lookupRow_fits ..,trivial,trivial,input,lookupRow_fits ..⟩

theorem work {k : ℕ} (base : ℕ) (a μ : Bits k) : (expr base a μ).work=10*(2^k)+10 := by
  simp only [expr,Expr.work,lookupRow_work];omega

theorem eval {w k base : ℕ} (m : Memory w) (a μ : Bits k) (weight : Block k→ℕ)
    (fits : 2^k<2^w) (loads : ∀i : Block k,m (base+i.val)=(weight i:Word w)) (d : Block k) :
    (expr base a μ).eval m (d.val:Word w) =
      (bufferedLoad (fun _ : Unit=>weight) (inverseAddresses a μ) () d:Word w) := by
  simp only [expr,Expr.eval,lookupRow_eval m _ fits.le d,DescriptorExpr.Comparison.test]
  cases old : ((inverseAddresses a μ).get d).1 with
  | none => simp [present,bufferedLoad,old]
  | some x =>
    have nz : (1:Word w)≠0 := by
      have two : 1 < 2^w := (Nat.succ_le_of_lt (Nat.two_pow_pos k)).trans_lt fits
      have val : (1 : Word w).val = 1 := by
        change 1 % (2^w) = 1
        exact Nat.mod_eq_of_lt two
      intro eqn
      exact Nat.one_ne_zero (val.symm.trans ((congrArg Fin.val eqn).trans (by simp)))
    simp [present,origin,bufferedLoad,old,nz,Bank.read,Bank.size,
      Fin.val_cast_of_lt (x.isLt.trans fits),Nat.mod_eq_of_lt x.isLt,loads x]

theorem run {w k base out : ℕ} (m : Memory w) (a μ : Bits k) (weight : Block k→ℕ)
    (input : (Bank.mk base k).Fits w out) (room : out+2^k<2^w)
    (loads : ∀i : Block k,m (base+i.val)=(weight i:Word w)) :
    let e := expr base a μ
    let after := ProtocolRAM.image out (2^k) e m
    (scan w out (2^k) e).Exec m after (4+2^k*(2*e.work+4)) ∧
      CheapCode (scan w out (2^k) e) ∧
      (∀ d : Block k,after (out+d.val)=
        (multiplierLoad (fun _ : Unit=>weight) a μ () d:Word w)) ∧
      ∀i<out,after i=m i := by
  refine ⟨scan_exec _ _ _ _ (fits a μ input) room,@scan_cheap _ _ _ _,?_,?_⟩
  · intro d
    rw [←bufferedLoad_eq]
    simpa [ProtocolRAM.image,fillSegment,Nat.add_lt_add_left d.isLt,Nat.cast_add] using
      eval m a μ weight input.2.1 loads d
  · intro i lo
    simp [ProtocolRAM.image,fillSegment,lo.not_ge]

end Hierarchy.DescentColonies.PermutationRAM

end OAI
