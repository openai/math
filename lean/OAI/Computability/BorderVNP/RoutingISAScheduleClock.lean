import OAI.Computability.BorderVNP.RoutingISASignedAssembly
import OAI.Computability.BorderVNP.RoutingISAEvalClock
import OAI.Computability.BorderVNP.CubeLabelProducerClock
import OAI.Computability.BorderVNP.CubeGroupWeightClock

/-! # Physical clock of the public grouping passes of Section 8

All cable and delivery rows are charged, including the vacant rows in the
producer's rectangle. Only the compact declaration reader and its installer
depend on the binary word widths. The threshold for the entire grouping
stage is independent of the number of processors and of the stored words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open BorderVNP.Cube Filter TeamScales

/-- Charges for the descriptor scans in `scheduleGroups`, in native execution
order, excluding the two compact binary header passes. -/
def descriptorTicks (l : LabelIndex.Layout) (m : ℕ → ℕ) (z axes : ℕ)
    (g : GroupWeights.Layout) (t : TeamNative.Layout) :=
  LabelIndex.directoryTicks l z m +
    (NativeIntervals.setup.slots+(4*l.labels^2+2)+(2+l.cableCount*(NativeIntervals.cableStep.slots+1))) +
    (16+5*axes) +
    (CubeLengths.minSetup.slots+CubeLengths.pivot.slots+axes*(CubeLengths.minBody.slots+1)+2) +
    GroupWeights.checkedTicks g t + (CellBanks.setup.slots+l.cells*15+1) +
    (30+(l.labels*l.labels)*(24+27*axes)) +
    (Transmission.DataWriter.setup.slots+l.deliveryCount*(Transmission.DataWriter.step.slots+1)+5) +
    SharedRows.budget g.groups

/-- The native scalar header installer, compact field decoder and dense column
totals use these two binary widths of the physical header. -/
def declarationTicks (p : HeaderDecode.Layout) (dimension selectorBits : ℕ) :=
  (95+dimension+selectorBits+4*p.cw+4*p.rw) +
    (HeaderDecode.cost p+HeaderTotals.cost p.a (p.d*p.d))

/-- The entire descriptor charge is bounded at the original grid size. The
argument only needs the total number of reserved source rows, even when many
final cells are empty. -/
theorem descriptorTicks_le_envelope (l : LabelIndex.Layout) (m : ℕ → ℕ) (z a B V M : ℕ)
    (g : GroupWeights.Layout) (t : TeamNative.Layout) (hz : l.labels=z+1)
    (cells : g.cells=l.cells) (groups : t.groups=g.groups) (teams : t.r+1 ≤ g.groups)
    (alphabet : g.groups ≤ l.labels) (rows : 1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1)) :
    descriptorTicks l m z a g t ≤ MeanChoice.scanEnvelope (2048*(a+1)*B) V M l.labels := by
  let N := 1+l.cells+l.cableCount+l.deliveryCount
  let P := (l.labels+1)^6
  let H := (a+1)*N*P
  have np : 1 ≤ N := by dsimp [N]; omega
  have pp : 1 ≤ P := pow_pos (Nat.zero_lt_succ _) _
  have base : N*P ≤ H := by dsimp [H]; rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)
  have nH : N ≤ H := (Nat.le_mul_of_pos_right _ pp).trans base
  have pH : P ≤ H := (Nat.le_mul_of_pos_left _ np).trans base
  have sq : (l.labels+1)^2 ≤ P := Nat.pow_le_pow_right (Nat.zero_lt_succ _) (by decide)
  have cube : (l.labels+1)^3 ≤ P := Nat.pow_le_pow_right (Nat.zero_lt_succ _) (by decide)
  have lsq : l.labels*l.labels ≤ P := (Nat.mul_self_le_mul_self (Nat.le_succ _)).trans (by simpa only [pow_two] using sq)
  have gsq : g.groups*g.groups ≤ H := (Nat.mul_self_le_mul_self alphabet).trans (lsq.trans pH)
  have gteam : g.groups*(t.r+1) ≤ H := (Nat.mul_le_mul_left _ teams).trans gsq
  have gd : g.groups ≤ H := (Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)).trans gteam
  have td := teams.trans gd
  have one := np.trans nH
  have ap : (a+1)*P ≤ H := by
    dsimp only [H]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ np)
  have aH : a ≤ H := (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ pp).trans ap)
  have pA : l.labels*l.labels*a ≤ H := by
    rw [Nat.mul_comm _ a]
    exact (Nat.mul_le_mul (Nat.le_succ _) lsq).trans ap
  have label := (LabelIndex.directoryTicks_le l m z hz).trans
    ((Nat.mul_le_mul_right _ (Nat.le_refl (600*N))).trans (Nat.mul_le_mul_left (600*N) cube))
  have labH : LabelIndex.directoryTicks l z m ≤ 600*H := by
    rw [Nat.mul_assoc] at label
    exact label.trans (Nat.mul_le_mul_left 600 base)
  have sh := SharedRows.budget_le g.groups
  change SharedRows.budget g.groups ≤ 91*(g.groups+1)^2 at sh
  have shH := sh.trans (Nat.mul_le_mul_left 91 ((Nat.pow_le_pow_left (Nat.succ_le_succ alphabet) 2).trans (sq.trans pH)))
  have lc : l.cells ≤ H := (show _ ≤ N by dsimp [N]; omega).trans nH
  have le : l.cableCount ≤ H := (show _ ≤ N by dsimp [N]; omega).trans nH
  have ld : l.deliveryCount ≤ H := (show _ ≤ N by dsimp [N]; omega).trans nH
  have ls := lsq.trans pH
  unfold descriptorTicks
  rw [GroupWeights.checkedTicks_eq _ _ groups,cells,pow_two]
  change LabelIndex.directoryTicks l z m + (28+(4*(l.labels*l.labels)+2)+(2+l.cableCount*23)) +
    (16+5*a)+(24+2+a*11+2)+
    (124+13*g.groups+21*(g.groups*g.groups)+13*l.cells+13*(t.r+1)+12*(g.groups*(t.r+1)))+
    (52+l.cells*15+1)+(30+(l.labels*l.labels)*(24+27*a))+(41+l.deliveryCount*43+5)+
    SharedRows.budget g.groups ≤ _
  have expand : (l.labels*l.labels)*(24+27*a) = 24*(l.labels*l.labels)+27*(l.labels*l.labels*a) := by ring
  rw [expand]
  calc
    _ ≤ 2048*H := by omega
    _ ≤ MeanChoice.scanEnvelope (2048*(a+1)*B) V M l.labels := by
      unfold H MeanChoice.scanEnvelope
      have h := Nat.mul_le_mul_left (2048*(a+1)) (Nat.mul_le_mul_right P rows)
      dsimp only [N,P]
      simpa only [Nat.mul_assoc] using h

/-- Binary work is linear in the installed field width and quadratic in the
symbol alphabet, including every lower-triangle padding cell. -/
theorem declarationTicks_le (p : HeaderDecode.Layout) (n bits w : ℕ) (hn : n ≤ p.a)
    (cw : p.cw ≤ w) (rw : p.rw ≤ w) :
    declarationTicks p n bits ≤ 256*(p.a+bits+1)*(p.d+1)^2*(w+1) := by
  change 95+n+bits+4*p.cw+4*p.rw+
    (77+(4+p.cw*12+1+3+(4+((p.d*p.d*p.a)*(3+(4+p.rw*12+1+3+1+1)+3+1)+1)))+
      (3+p.a*(7*(p.d*p.d)+7))) ≤ _
  calc
    _ ≤ 95+p.a+bits+4*w+4*w+
      (77+(4+w*12+1+3+(4+((p.d*p.d*p.a)*(3+(4+w*12+1+3+1+1)+3+1)+1)))+
        (3+p.a*(7*(p.d*p.d)+7))) := by gcongr
    _ ≤ _ := by
      simp only [pow_two]
      ring_nf
      omega

/-- Simultaneous public and word-dependent bounds. Each term is the sum of
actual native pass allowances. The public part uses the original tile and
reserved-row counts and the local part uses the width of the machine word. -/
theorem eventually_scheduleTicks {α ξ : ℝ} (hα : 0 < α) (a bits B C D : ℕ) (small : α*a < 1/10^6) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R V M z w : ℕ) (l : LabelIndex.Layout) (m : ℕ → ℕ)
      (g : GroupWeights.Layout) (t : TeamNative.Layout) (p : HeaderDecode.Layout),
      1 ≤ r → 1 ≤ R → (V:ℝ) ≤ C*r*(n:ℝ)^(9/10:ℝ) → (M:ℝ) ≤ (n:ℝ)^(1/100:ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(V+1)*(M+1) →
      l.labels=Routing.labelCount a α n → l.labels=z+1 → g.cells=l.cells → t.groups=g.groups →
      t.r+1 ≤ g.groups → g.groups ≤ l.labels → p.d=g.groups → p.a=a →
      p.cw ≤ w → p.rw ≤ w → w ≤ logWidth r n ^ D →
      (descriptorTicks l m z a g t:ℝ) ≤ publicWork a α r n R ∧
      (declarationTicks p (a-1) bits:ℝ) ≤ (512*(a+bits+1):ℕ)*localWork a D α ξ r n R := by
  filter_upwards [MeanChoice.eventually_scanEnvelope hα a small (2048*(a+1)*B) C,eventually_ge_atTop 1] with n bound hn
  intro r R V M z w l m g t p hr hR Vcap Mcap rows Z hz cells groups teams alph d axes cw rw width
  constructor
  · have h := descriptorTicks_le_envelope l m z a B V M g t hz cells groups teams alph rows
    rw [Z] at h
    have cap := (Nat.cast_le (α:=ℝ)).mpr h |>.trans (bound r V M hr Vcap Mcap).le
    unfold publicWork
    norm_num1 at cap ⊢
    linarith [show 0 ≤ ((Routing.labelCount a α n:ℝ)+R)^10 by positivity]
  · have cap := declarationTicks_le p (a-1) bits w (by omega) cw rw
    let L := logWidth r n^D
    have lp : 1 ≤ L := Nat.one_le_pow _ _ (GeometryAdviceRate.indexWidths hr hn).1
    have wp : w+1 ≤ 2*L := by change w ≤ L at width; omega
    have dz : p.d+1 ≤ Routing.labelCount a α n+R := by omega
    have pos : 1 ≤ Routing.labelCount a α n+R := by omega
    have top := (Nat.pow_le_pow_left dz 2).trans (Nat.pow_le_pow_right pos (by decide : 2≤10))
    have b := cap.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ top) wp)
    rw [axes] at b
    have cast := (Nat.cast_le (α:=ℝ)).mpr b
    push_cast at cast ⊢
    unfold localWork
    dsimp only [L] at cast
    push_cast at cast
    nlinarith only [cast,show 0 ≤ ((512:ℝ)*(a+bits+1))*(exterior ξ r n:ℝ)*(logWidth r n:ℝ)^D by positivity]

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
