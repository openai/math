import OAI.Hierarchy.DescentRotorAlphabet
import OAI.Hierarchy.DescentPrimitiveRolePrice
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # Exact number and bit length of all possible primitive rotor labels -/

namespace Hierarchy.DescentCompiler.AtomSchedule
variable (S : AtomSchedule)
theorem first_width_payload (hj : 0<S.height) {b : ℕ} (base : b≤2^S.capGain) (p : ℕ) :
    S.firstWidth b p≤p*S.epochPower^S.localGrainExponent := by
  unfold firstWidth
  rw [S.grain_initial,Nat.mul_assoc,←pow_succ]
  refine Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left base _).trans ?_)
  unfold epochPower localGrainExponent
  rw [←pow_mul,←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have one : 1≤S.height := hj
  have v := Nat.mul_le_mul_left S.capGain (Nat.add_le_add_left one (S.rounds*S.height))
  simpa only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using v

end Hierarchy.DescentCompiler.AtomSchedule

namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentCompiler DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
abbrev censusCount (s : ℕ) := (∑m : Fin 4,(s+1)^(2^m.val))+1
abbrev gadgetCount (G : PoweredGadget F) (z : ℕ) := (z+1)*((G.C+2)^8*6)
def colors (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec) :=
  censusCount s + (gadgetCount G Z+(1+Fintype.card (CanonicalTag (2^op.n))))

variable (G : PoweredGadget F) (S : AtomSchedule) {p : ℕ}
variable (branch : G.b≤2^S.capGain)

theorem paletteSize (z seed : ℕ) (op : RotorSpec) (small : z≤ seed) :
    colors G seed z op≤(6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n)))*(seed+1)^8 := by
  have mass : (∑ j : Fin 4,(seed+1)^(2^j.val))≤4*(seed+1)^8 := by
    have bound (j : Fin 4) : (seed+1)^(2^j.val)≤(seed+1)^8 := by
      apply Nat.pow_le_pow_right (by omega)
      fin_cases j <;> decide
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _=>bound j)
  have base : 1≤(seed+1)^8 := Nat.one_le_pow _ _ (by omega)
  have next : z+1≤(seed+1)^8 :=
    (Nat.succ_le_succ small).trans (by simpa only [pow_one] using Nat.pow_le_pow_right (show 0<seed+1 by omega) (show 1≤8 by decide))
  have cost:=Nat.mul_le_mul_right ((G.C+2)^8*6) next
  have rest:=Nat.mul_le_mul_left (Fintype.card (CanonicalTag (2^op.n))) base
  unfold colors censusCount gadgetCount
  nlinarith

include branch in
theorem paletteBits (op : RotorSpec) {h B : ℕ} (hb : 0<B) (chosen : S.height=Nat.log 2 h/(2*B))
    (age : 0<S.height) (word : p≤h) :
    Nat.clog 2 (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op+1) ≤
      Nat.clog 2 (6+6*(G.C+2)^8+Fintype.card (CanonicalTag (2^op.n))+1)+
        8*(2*B*(S.height+1)+S.height*(S.capGain*(S.rounds+1))+1) := by
  apply DescentPrimitiveRolePrice.tagBits hb chosen word (S.first_width_payload age branch p)
  exact paletteSize G (S.grainAt G.b p 0) (S.firstWidth G.b p) op (Nat.le_mul_of_pos_right _ G.base_pos)

end
end Hierarchy.DescentPrimitivePalette

end OAI
