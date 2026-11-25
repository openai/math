import OAI.Hierarchy.GridReceiverTickDirectory
import OAI.Hierarchy.GridSimulationPadding
import OAI.Hierarchy.TickResourceBounds

namespace OAI
/-! # The receiving tick's common startup fuel -/

namespace Hierarchy.GridReceiverClock
open ThreeFlat Diagonal RAM PhysicalStage NavigationPass NavigationDirectory
open GridScale Computability.VPVNP.BurstRAM Filter

/-- The common per-tick work includes both copies of the chronological scan
budget, the funded-node publication, the class counter initialization and
the full class-major candidate traversal. -/
def startupTime (w pins cut N dim : ℕ) (a : Archive) (ss : List Stage) (edges : ℕ) : ℕ :=
  (28+16*pins)+(cut+(cut+Archive.terminalTime (a.terminal ss edges (64*w))))+
    2*cut+(GridSimulation.assignTime w N dim+
      GridReceiverTickDirectory.clock (64*w) (((20*(w+1)+2)^dim)*N))

def coefficient (dim : ℕ) := 10000+FactorBucketRAM.budgetConstant dim+34*22^dim

theorem prefix_bound {w pin cut N dim edges : ℕ} (a : Archive) (ss : List Stage)
    (live : 0<pin) (rootCount : N≤cut) (edgeCount : edges≤cut) (bits : a.pairCapacity≤pin) :
    startupTime w pin cut N dim a ss edges ≤ coefficient dim*(w+1)^(dim+2)*(cut+pin) := by
  let z:=(w+1)^(dim+2)
  let n:=cut+pin
  have grow {i : ℕ} (hi : i≤dim+2) : (w+1)^i≤z :=
    Nat.pow_le_pow_right (by omega) hi
  have wz : w+1≤z := by simpa using (grow (i:=1) (by omega))
  have pos : 0<z := by omega
  have nz : 1≤n := by dsimp only [n];omega
  have zn : z≤z*n := Nat.le_mul_of_pos_right _ nz
  have nn : n≤z*n := Nat.le_mul_of_pos_left _ pos
  have loop := FactorBucketRAM.clock_bound w N dim
  have count : N+1≤n := by dsimp only [n];omega
  have t₁ : FactorBucketRAM.ticks w N dim≤FactorBucketRAM.budgetConstant dim*(z*n) :=
    calc
      _ ≤ _ := loop
      _ ≤ FactorBucketRAM.budgetConstant dim*z*n :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (grow (i:=dim+1) (by omega))) count
      _ = _ := Nat.mul_assoc ..
  have header : GridReceiverHeader.count w*(5*(64*w)+6)+6≤7000*(z*n) := calc
    _ ≤ 7000*(w+1)^2 := by unfold GridReceiverHeader.count; nlinarith
    _ ≤ _ := Nat.mul_le_mul_left _ ((grow (by omega)).trans zn)
  have term:=GridSelector.terminal_price a ss edges (64*w)
  have classes : (20*(w+1)+2)^dim ≤ 22^dim*z := calc
    _ ≤ (22*(w+1))^dim := Nat.pow_le_pow_left (by omega) _
    _ ≤ _ := by rw [Nat.mul_pow];exact Nat.mul_le_mul_left _ (grow (by omega))
  have scan : ((20*(w+1)+2)^dim)*N≤22^dim*(z*n) :=
    (Nat.mul_le_mul classes (by dsimp only [n];omega : N≤n)).trans_eq (Nat.mul_assoc ..)
  have wn : w≤z*n := by omega
  have clockOverhead :
      (28+16*pin)+4*cut+500*(edges+a.pairCapacity+2)+
        (4+5*6+(1*(5*(64*w)+6)+6)+3) ≤ 3000*(z*n) := by
    have paid : cut+pin ≤ z*n := nn
    have paidOne : 1 ≤ z*n := nz.trans nn
    omega
  change _≤coefficient dim*z*n
  rw [Nat.mul_assoc]
  unfold startupTime GridSimulation.assignTime GridReceiverTickDirectory.clock coefficient
  nlinarith only [clockOverhead,term,t₁,header,Nat.mul_le_mul_left 34 scan]

/-- These budgets also pay an arbitrary polynomial number of genuine template
words or masks. The multiplier is fixed before the controller and can reserve
any fixed fraction for the later selected replay and weighted-field machine. -/
theorem eventual_with_scans {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss)
    (k A dim templateCoeff templateDegree margin : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ q,0<q → q≤Q w →
      let pin:=pins w (overhead Q loss w)
      let cut:=2^(3*w/5)
      ∀ (a : Archive) (ss : List Stage) (N edges template : ℕ), N≤cut → edges≤cut →
        a.pairCapacity≤pin → template≤templateCoeff*(w+1)^templateDegree*(cut+pin) →
        margin*(startupTime w pin cut N dim a ss edges+template)≤UniversalTick.clock w UniversalTick.saving := by
  let streamDegree:=max (dim+2) templateDegree
  let total:=margin*(coefficient dim+templateCoeff)
  filter_upwards [receiver_setup_room env k A total streamDegree UniversalTick.saving] with w bound
  intro q live within pin cut a ss N edges table count edgeCount bitCount tableBound
  have pos : 0<pin := Nat.two_pow_pos _
  have z : 1≤cut+pin := by omega
  have clock:=prefix_bound (w:=w) (dim:=dim) a ss pos count edgeCount bitCount
  have g {j : ℕ} (hj : j≤ streamDegree) : (w+1)^j≤(w+1)^streamDegree :=
    Nat.pow_le_pow_right (by omega) hj
  have c₁ := clock.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (g (le_max_left ..))))
  have c₃ := tableBound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (g (le_max_right ..))))
  have n : margin*(startupTime w pin cut N dim a ss edges+table) ≤ total*(w+1)^streamDegree*(cut+pin) := by
    apply (Nat.mul_le_mul_left margin (Nat.add_le_add c₁ c₃)).trans_eq
    dsimp only [total];ring
  have cutBound : (cut:ℝ)≤((2:ℝ)^w)^(4/5:ℝ) := by
    change ((2^(3*w/5):ℕ):ℝ)≤_
    push_cast
    rw [←Real.rpow_natCast (2:ℝ) (3*w/5),←Real.rpow_natCast (2:ℝ) w,←Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have small : ((3*w/5:ℕ):ℝ)*5≤3*(w:ℝ) := by exact_mod_cast Nat.div_mul_le_self (3*w) 5
    linarith [Nat.cast_nonneg w (α:=ℝ)]
  have result : ((total*(w+1)^streamDegree*(cut+pin):ℕ):ℝ)≤
      (UniversalTick.clock w UniversalTick.saving:ℕ) := by
    calc
      _ = ((total*(w+1)^streamDegree:ℕ):ℝ)*((cut:ℝ)+(pin:ℝ)) := by
        rw [Nat.cast_mul,Nat.cast_add]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add cutBound (le_refl (pin:ℝ)))
        (Nat.cast_nonneg (total*(w+1)^streamDegree))).trans (bound q live within)
  exact n.trans (by exact_mod_cast result)

/-- A fixed public prototype and its masks are a special case of the
same estimate. -/
theorem eventual {Q : ℕ→ℕ} {loss : ℕ→ℝ} (env : Envelopes Q loss)
    (k A dim templateCoeff templateDegree margin : ℕ) :
    ∀ᶠ w : ℕ in atTop,∀ q,0<q → q≤Q w →
      let pin:=pins w (overhead Q loss w)
      let cut:=2^(3*w/5)
      ∀ (a : Archive) (ss : List Stage) (N edges template : ℕ), N≤cut → edges≤cut →
        a.pairCapacity≤pin → template≤templateCoeff*(w+1)^templateDegree →
        margin*(startupTime w pin cut N dim a ss edges+template)≤UniversalTick.clock w UniversalTick.saving := by
  filter_upwards [eventual_with_scans env k A dim templateCoeff templateDegree margin] with w common
  intro q live within pin cut a ss N edges table roots wires bits material
  exact common q live within a ss N edges table roots wires bits
    (material.trans (Nat.le_mul_of_pos_right _ (by
      have h : 0<pin := Nat.two_pow_pos _
      omega)))

end Hierarchy.GridReceiverClock

end OAI
