import OAI.Hierarchy.DescentPackedMatchSourceChart
import OAI.Hierarchy.DescentMatchedRosterCount

namespace OAI
/-! # Rank every input profile by its actual pre-profile key, host, group and local unit -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentStageEdgeReceipt
open DescentKernelHistory.BitDescription Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k H groups : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {price ε : ℝ}
variable (he : 0≤ε) (A : GroupStage W G price ε J V k) (gid : J↪Fin groups) (host : V↪Fin H)
set_option quotPrecheck false
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "rank" => (sourceChart he A gid host).trans Fin.valEmbedding

/-- The physical incoming coordinate is fixed before the new choices. -/
def inputNumber : ScanNumbers he A.stage :=
  PairRAM.globalNumberBy W.graph W.core home color A.cap rank

def countIn (c : ScanColonies he A.stage) :=
  Fintype.card (Matched T A.cap (thinList home color c) (thickList home color c))

def beforeSource (c : ScanColonies he A.stage) :=
  MatchedStageRAM.countAt rank (countIn he A) (rank c)

theorem rank_address (c : ScanColonies he A.stage) (e : Matched T A.cap (thinList home color c) (thickList home color c)) :
    (inputNumber he A gid host ⟨c,e⟩).val=beforeSource he A gid host c+
      (pairNumber (amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val := rfl

/-- Expanding the two public pitches with zero-count physical rows or lanes
preserves the strictly ordered live source offsets. -/
private theorem mul_pitch {x y a b p : ℕ} (aSmall : a < p) (bSmall : b < p) :
    x*p+a < y*p+b ↔ x < y ∨ x=y ∧ a < b := by
  have lower {i j : ℕ} (lt : i < j) (t : ℕ) (room : t < p) : i*p+t < j*p := by
    calc
      _ < i*p+p:=Nat.add_lt_add_left room _
      _ = (i+1)*p:=by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ j*p:=Nat.mul_le_mul_right p lt
  rcases lt_trichotomy x y with left|eqn|right
  · exact iff_of_true (by have :=lower left a aSmall;omega) (Or.inl left)
  · subst y;simp
  · exact iff_of_false (by have :=lower right b bSmall;omega) (by omega)

theorem padded_order {G H G' H' : ℕ} (a b host₁ host₂ group₁ group₂ : ℕ)
    (ag : group₁ < G) (bg : group₂ < G) (ah : host₁ < H) (bh : host₂ < H) (gg : G ≤ G') (hh : H ≤ H') :
    ((a*H+host₁)*G+group₁ < (b*H+host₂)*G+group₂) ↔
      ((a*H'+host₁)*G'+group₁ < (b*H'+host₂)*G'+group₂) := by
  have mid : a*H+host₁=b*H+host₂ ↔ a=b ∧ host₁=host₂ := by
    constructor
    · intro eqn
      have l:=mul_pitch ah bh (x:=a) (y:=b)
      have r:=mul_pitch bh ah (x:=b) (y:=a)
      by_cases same : a=b
      · subst b;exact ⟨rfl,Nat.add_left_cancel eqn⟩
      · rcases lt_or_gt_of_ne same with lt|lt
        · exact False.elim ((ne_of_lt (l.mpr (Or.inl lt))) eqn)
        · exact False.elim ((ne_of_lt (r.mpr (Or.inl lt))) eqn.symm)
    · rintro ⟨rfl,rfl⟩;rfl
  have hand {q : ℕ} (aH : host₁ < q) (bH : host₂ < q) :
      a*q+host₁=b*q+host₂ ↔ a=b ∧ host₁=host₂ := by
    have f:=mul_pitch aH bH (x:=a) (y:=b)
    have g:=mul_pitch bH aH (x:=b) (y:=a)
    omega
  rw [mul_pitch ag bg,mul_pitch (ag.trans_le gg) (bg.trans_le gg),mid,hand (ah.trans_le hh) (bh.trans_le hh),
    mul_pitch ah bh,mul_pitch (ah.trans_le hh) (bh.trans_le hh)]

theorem before_padded {Q : Type} [Fintype Q] (short wide : Q↪ℕ) (mass : Q→ℕ)
    (order : ∀a b,short a < short b ↔ wide a < wide b) (c : Q) :
    MatchedStageRAM.countAt short mass (short c)=MatchedStageRAM.countAt wide mass (wide c) := by
  unfold MatchedStageRAM.countAt
  congr 1
  ext a
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using order a c


end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
