import OAI.Hierarchy.DescentSeedEpochRoom
import OAI.Hierarchy.DescentSeedTokenAlphabet
import OAI.Hierarchy.DescentPrimitivePalettePrintedBits

namespace OAI
/-! # Uniform short digit widths of the two genuine original primitive alphabets -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentPackedSeed DescentSeedRoot DescentPrimitivePalette
open DescentSixParty DescentResetGates DescentSIMDLookup Filter
variable {F : Type} [Field F] (G : DescentSixParty.PoweredGadget F) (op : RotorSpec)

theorem primitive_bits (s Z : ℕ) (cap : Z ≤ s) :
    printedBits G s Z op ≤ Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)+8*digitsNeeded s :=by
  let C:=6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))
  have size:=paletteSize G Z s op cap
  have hi:=Nat.pow_le_pow_left (Nat.lt_log2_self (n:=s) : s+1 ≤ 2^digitsNeeded s) 8
  have rows : (s+1)^8 ≤ 2^(8*digitsNeeded s) :=by
    rw [Nat.mul_comm 8 (digitsNeeded s),pow_mul]
    exact hi
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  have con : C+1 ≤ 2^Nat.clog 2 (C+1):=Nat.le_pow_clog (by decide) _
  have stage:=Nat.mul_le_mul_left C rows
  have one:=Nat.two_pow_pos (8*digitsNeeded s)
  apply le_trans _ (Nat.mul_le_mul_right _ con)
  change colors G s Z op+1 ≤ (C+1)*_
  change colors G s Z op ≤ C*(s+1)^8 at size
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem primitive_rate (B : ℕ) (positive : 0 < B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀s Z : ℕ,Z ≤ s → s ≤ h → printedBits G s Z op ≤ scale J 3 ∧
        DescentPackedSeed.Primitive.roleBits s ≤ scale J 3 ∧ digitsNeeded s ≤ scale J 2 :=by
  let C:=Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)
  filter_upwards [eventually_late (C+2*B+16) B positive] with h old
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro s Z cap hs
  have one : J ≤ scale J 1 :=(Nat.le_succ _).trans (by
    simpa only [scale,one_mul] using (Nat.lt_two_pow_self (n:=J+1)).le)
  have late :=old.trans one
  have input :=(Nat.succ_le_succ (Nat.log_mono_right (b:=2) hs)).trans (log_epoch h B positive)
  have digits : digitsNeeded s ≤ scale J 2 :=by
    unfold digitsNeeded;rw [Nat.log2_eq_log_two]
    exact input.trans ((Nat.mul_le_mul_right _ (by omega : 2*B ≤ scale J 1)).trans_eq (scale_mul J 1 1))
  have actual:=primitive_bits G op s Z cap
  have localCode:=DescentPackedSeed.Primitive.role_bound_short s
  have lower : 1 ≤ scale J 2 := Nat.two_pow_pos _
  have package : C+8*digitsNeeded s ≤ (C+8)*scale J 2 :=by nlinarith only [digits,lower,Nat.mul_le_mul_left C lower]
  have budget : (C+8)*scale J 2 ≤ scale J 3 :=
    (Nat.mul_le_mul_right _ (by omega : C+8 ≤ scale J 1)).trans_eq (scale_mul J 1 2)
  have shorter : 8*digitsNeeded s+3 ≤ 11*scale J 2 :=by omega
  exact ⟨actual.trans (package.trans budget),localCode.trans (shorter.trans ((Nat.mul_le_mul_right _
    (by omega : 11 ≤ scale J 1)).trans_eq (scale_mul J 1 2))),digits⟩

end Hierarchy.DescentDatedSeedStartup

end OAI
