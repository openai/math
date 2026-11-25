import OAI.Hierarchy.DescentAtomSchedule

namespace OAI
/-! # Ordinary group addresses before and after a full-width reset -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)

def groupWidth (k tail age : ℕ) := tail+k*(S.length-age)

theorem group_power {k tail : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (i : ℕ) :
    2^S.groupWidth k tail i=S.groupCount i := by
  simp only [groupWidth,groupCount,base,radix,pow_add,pow_mul]

/-- All surviving group digits and the old local row appear as coordinates of one
power-of-two reset layout. Division by the row radix recovers exactly the next
group ordinal in the original order. -/
def resetInputDigits {k tail : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (i : ℕ) :
    Fin (2^(S.groupWidth k tail i+k)) ≃ Fin (S.groupCount i) × Fin (2^k) :=
  (finCongr (by rw [pow_add,S.group_power base radix])).trans finProdFinEquiv.symm

theorem group_cut {k tail i : ℕ} (age : i<S.length) :
    S.groupWidth k tail i=S.groupWidth k tail (i+1)+k := by
  have d : S.length-i=(S.length-(i+1))+1 := by omega
  rw [groupWidth, d, Nat.mul_add]
  simp [groupWidth,Nat.add_assoc]

/-- The post-reset address uses the very same public radix as an ordinary
step. In particular its high digits count the actual population at age i+1. -/
def resetOutputDigits {k tail i depth : ℕ} (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (age : i<S.length) (actual : depth=S.groupWidth k tail i) :
    Fin (2^depth) ≃ Fin (S.groupCount (i+1)) × Fin (2^k) :=
  (finCongr (congrArg (fun n=>2^n) (actual.trans (S.group_cut age)))).trans
    (S.resetInputDigits base radix (i+1))

end Hierarchy.DescentCompiler.AtomSchedule

end OAI
