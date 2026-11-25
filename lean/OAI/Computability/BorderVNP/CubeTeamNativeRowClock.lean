import OAI.Computability.BorderVNP.CubeTeamScatterRowClock
import OAI.Computability.BorderVNP.CubeISADeclaredRowTally
import OAI.Computability.BorderVNP.CubeISAOwnedVertexRow
import OAI.Computability.BorderVNP.CubeTeamRowDispatch

/-! # Whole-team clock for scatter, declared-row tally and vertex emission

All three phases traverse the same physical row. The fixed-format packet
callbacks and the singleton bit tally have bounded costs per scatter trial.
The per-coordinate initialization and equality scan are charged separately.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical Physical.Owned Finset RoutingISA

variable {n d : ℕ}

/-- The allowance of a native packet candidate loop with the indicated callback. -/
def packetScan (n d blocks callback : ℕ) :=
  (∑ t : Fin (packetTrials n d blocks), (6*n+22 + if packetTrialValid t then callback else 1))+1

private theorem scale_scan {N : ℕ} (a b : Fin N → ℕ) (K : ℕ) (hk : 1 ≤ K)
    (bound : ∀ t, a t ≤ K*b t) : (∑ t, a t)+1 ≤ K*((∑ t, b t)+1) := by
  rw [Nat.mul_add,Finset.mul_sum,Nat.mul_one]
  exact Nat.add_le_add (sum_le_sum fun t _ => bound t) hk

private theorem packetScan_le (n d blocks b h K s callback : ℕ) :
    packetScan n d blocks callback ≤ (callback+1)*packetTicks n d blocks b h K s := by
  apply scale_scan _ _ _ (Nat.le_add_left 1 callback)
  intro t
  split_ifs with hv
  · have pos : 1 ≤ 6*n+22+Scatter.ownedPacketCost n b h K s := by omega
    have le := Nat.mul_le_mul_left callback pos
    rw [Nat.mul_one] at le
    rw [Nat.add_mul callback 1, Nat.one_mul]
    omega
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

private theorem singleTally_le (blocks width : ℕ) (i : Fin (n+1)) (u v : Fin d) :
    SingleTally.rowCost i u v (blocks*width) ≤ (13*(n+1)+8)*singleTicks blocks width i u v := by
  let k := 13*(n+1)+7
  change _ ≤ (k+1)*_
  apply scale_scan _ _ _ (Nat.le_add_left 1 k)
  intro t
  split_ifs with hv
  · let x := 6*n+20+(Scatter.startSingle.slots+5*(blocks*width)+2)
    have st : 3 ≤ Scatter.startSingle.slots := by decide
    have len : blocks*width ≤ x := by dsimp only [x]; omega
    have base : 6*n+20+5 ≤ x := by dsimp only [x]; omega
    have le := Nat.mul_le_mul_right k len
    rw [Nat.mul_comm x k] at le
    change 6*n+20+(5+blocks*width*k) ≤ (k+1)*x
    rw [Nat.add_mul k 1,Nat.one_mul]
    omega
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- Actual local declaration tally. A strict tally has one packet and two ordered
singleton passes, with their initializations and intervening register swap. -/
def tallyTicks (blocks b h K : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  if u = v then 4+SingleTally.rowCost i u v (blocks*(h*b)) else
    packetScan n d blocks (PacketTally.cost n K h) + ((4+SingleTally.rowCost i u v (blocks*(h*b)))+
      (3+(4+SingleTally.rowCost i v u (blocks*(h*b)))))

/-- The numerical allowance agrees with the strict tally in either local role. -/
theorem tallyTicks_strict (blocks b h K : ℕ) (i : Fin (n+1)) (sym : Symbols d) :
    tallyTicks blocks b h K i sym.val.1 sym.val.2 = DeclaredRow.strictCost i sym blocks b K h ∧
    tallyTicks blocks b h K i sym.val.2 sym.val.1 = DeclaredRow.strictCost i sym blocks b K h := by
  constructor <;> simp only [tallyTicks,sym.property.ne,sym.property.ne',ite_false,DeclaredRow.strictCost,packetScan]
  all_goals omega

/-- The directory emitter runs only at strict rows and charges its true selector width. -/
def vertexTicks (n d blocks K h : ℕ) (u v : Fin d) :=
  if u = v then 0 else packetScan n d blocks (2+OwnedVertex.emitPacketCost n (Tally.selectorWidth n K h))

/-- Constant relating a packet or singleton declaration tally to its scatter trial. -/
def tallyFactor (n K h : ℕ) := max (PacketTally.cost n K h+1) (13*(n+1)+8)

/-- Fixed-format factor for the half-cube directory writer. -/
def vertexFactor (n K h : ℕ) := 2+OwnedVertex.emitPacketCost n (Tally.selectorWidth n K h)+1

private theorem tallyTicks_le (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) :
    tallyTicks blocks b h K i u v ≤ tallyFactor n K h*scatterRoleTicks blocks b h K s i u v+11 := by
  let C := tallyFactor n K h
  have hp := (packetScan_le n d blocks b h K s (PacketTally.cost n K h)).trans
    (Nat.mul_le_mul_right _ (show PacketTally.cost n K h+1 ≤ C from le_max_left ..))
  have single (x y : Fin d) := (singleTally_le blocks (h*b) i x y).trans
    (Nat.mul_le_mul_right _ (show 13*(n+1)+8 ≤ C from le_max_right ..))
  have huv := single u v
  have hvu := single v u
  by_cases diag : u = v
  · simp only [tallyTicks,scatterRoleTicks,diag,ite_true] at huv ⊢
    dsimp only [C] at huv
    omega
  · simp only [tallyTicks,scatterRoleTicks,diag,ite_false,Nat.mul_add]
    dsimp only [C] at hp huv hvu
    omega

private theorem vertexTicks_le (blocks b h K s : ℕ) (i : Fin (n+1)) (u v : Fin d) :
    vertexTicks n d blocks K h u v ≤ vertexFactor n K h*scatterRoleTicks blocks b h K s i u v := by
  by_cases diag : u = v
  · simp [vertexTicks,diag]
  · simp only [vertexTicks,scatterRoleTicks,diag,ite_false]
    exact (packetScan_le n d blocks b h K s _).trans (Nat.mul_le_mul_left _ (by omega))

/-- Cost of one local group role, including fixed setup and a clear and comparison
at each coordinate, followed by the three actual selected-row phases. -/
def nativeRoleTicks (blocks b h K s fixed each : ℕ) (i : Fin (n+1)) (u v : Fin d) :=
  fixed + (n+1)*each + scatterRoleTicks blocks b h K s i u v +
    tallyTicks blocks b h K i u v + vertexTicks n d blocks K h u v

/-- Combined coefficient for the three fixed-format phases. -/
def phaseFactor (n K h : ℕ) := 1+tallyFactor n K h+vertexFactor n K h

/-- Coefficient on candidate scans and per-coordinate initialization. -/
def nativeProbe (n K h fixed each : ℕ) := fixed+(n+1)*each+11+phaseFactor n K h*scatterProbe n

/-- Coefficient on physical raw wires. -/
def nativeBit (n b h K s : ℕ) := phaseFactor n K h*scatterBit n b h K s

/-- The full checked row has a fixed preparation budget and a charge for exactly its raw inventory. -/
theorem nativeRoleTicks_le_trials (blocks b h K s fixed each : ℕ) (i : Fin (n+1)) (u v : Fin d)
    (positive : 0 < h*b) :
    nativeRoleTicks blocks b h K s fixed each i u v ≤
      nativeProbe n K h fixed each*(d^n)^2 + nativeBit n b h K s*rowRaw blocks (h*b) i u v := by
  let Z := (d^n)^2
  have hz : 0 < Z := pow_pos (pow_pos (Nat.zero_lt_of_lt u.isLt) _) _
  have hs := scatterRoleTicks_le_trials blocks b h K s i u v positive
  have ht := tallyTicks_le blocks b h K s i u v
  have hv := vertexTicks_le blocks b h K s i u v
  let k := fixed+(n+1)*each+11
  calc
    _ ≤ k+phaseFactor n K h*scatterRoleTicks blocks b h K s i u v := by
      simp only [nativeRoleTicks,k,phaseFactor,Nat.add_mul,Nat.one_mul]
      omega
    _ ≤ k*Z+phaseFactor n K h*(scatterProbe n*Z+scatterBit n b h K s*rowRaw blocks (h*b) i u v) :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ hz) (Nat.mul_le_mul_left _ hs)
    _ = _ := by dsimp only [nativeProbe,nativeBit,k,Z]; ring

/-- A full-label squared allowance also bounds each checked role. -/
theorem nativeRoleTicks_le (blocks b h K s fixed each : ℕ) (i : Fin (n+1)) (u v : Fin d)
    (positive : 0 < h*b) :
    nativeRoleTicks blocks b h K s fixed each i u v ≤
      nativeProbe n K h fixed each*(d^(n+1))^2 + nativeBit n b h K s*rowRaw blocks (h*b) i u v := by
  have hd : d^n ≤ d^(n+1) := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt u.isLt)
  exact (nativeRoleTicks_le_trials blocks b h K s fixed each i u v positive).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2)) _)

/-- The numeric quotient and remainder in the native outer counter are exactly
the two coordinates of the finite product used to charge the ordered roles. -/
theorem linear_teamClock (d : ℕ) (owner cost : ℕ → ℕ) (team overhead : ℕ) :
    (∑ q ∈ range (d*d), (overhead + if owner (q/d) = team then cost q else 0)) =
      teamClock (fun u : Fin d => owner u.val) team overhead (fun u v => cost (finProdFinEquiv (u,v)).val) := by
  let f (p : Fin d × Fin d) := overhead + if owner p.1.val = team then cost (finProdFinEquiv p).val else 0
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p, f p := Fintype.sum_equiv finProdFinEquiv.symm _ f fun q => by
      dsimp only [f]; rw [Equiv.apply_symm_apply]; rfl
    _ = _ := Fintype.sum_prod_type f

/-- Clock for the native linear dispatcher with its actual setup, classifications,
advances and final guard, using the weight cap of the team chosen by the schedule. -/
theorem nativeTeamTicks_le {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (dispatch : TeamRowPrepare.Layout) (hd : dispatch.d = l.groups)
    (ht : dispatch.teamID = team.val) (X s fixed each : ℕ) (cost : ℕ → ℕ) (positive : 0 < h*b)
    (role : ∀ u v : Fin l.groups, cost (finProdFinEquiv (u,v)).val ≤
      nativeRoleTicks blocks b h K s fixed each D.1 u v)
    (cap : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    TeamRows.ticks dispatch (fun u => mem (teams.owners+u)) cost ≤
      TeamRowPrepare.setup.slots + ((TeamRowPrepare.prepare.slots+5+nativeProbe n K h fixed each)*
      (l.groups^(n+1))^4 + nativeBit n b h K s*(1000000*X/256)) + 1 := by
  rw [TeamRows.ticks,hd,ht,linear_teamClock l.groups (fun u => mem (teams.owners+u)) cost team.val
    (TeamRowPrepare.prepare.slots+5)]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact teamClock_le_exterior result image team X _ _ _ _ (fun u v =>
    (role u v).trans (nativeRoleTicks_le blocks b h K s fixed each D.1 u v positive)) cap

/-- Read a physical role allowance at the corresponding linear counter position. -/
def roleAt {d : ℕ} (role : Fin d → Fin d → ℕ) (q : ℕ) :=
  if hq : q < d*d then
    let p := finProdFinEquiv.symm (⟨q,hq⟩ : Fin (d*d))
    role p.1 p.2
  else 0

/-- The actual ordered row key retrieves its role in either orientation. -/
theorem roleAt_pair {d : ℕ} (role : Fin d → Fin d → ℕ) (u v : Fin d) :
    roleAt role (finProdFinEquiv (u,v)).val = role u v := by
  simp only [roleAt,dite_eq_left (finProdFinEquiv (u,v)).isLt,Fin.eta,Equiv.symm_apply_apply]

/-- At the actual role allowance, the only length-dependent terms in the team clock
are the fourth power of the number of labels and the scaled team cap. -/
theorem nativeTeamTicks_at_roles {l : GroupWeights.Layout} {teams : TeamNative.Layout} {orig mem : ℕ → ℕ}
    {n blocks b K h : ℕ} {D : LengthDeclaration n l.groups} {A : Type*} [Fintype A]
    {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
    (result : GroupWeights.ScheduleResult l teams orig mem)
    (image : GroupWeights.PhysicalImage l orig blocks b K h D label recv w)
    (team : Fin (teams.r+1)) (dispatch : TeamRowPrepare.Layout) (hd : dispatch.d = l.groups)
    (ht : dispatch.teamID = team.val) (X s fixed each : ℕ) (positive : 0 < h*b)
    (cap : TeamNative.unscale (mem (teams.totals+team.val)) ≤ (X : ℚ)/256) :
    TeamRows.ticks dispatch (fun u => mem (teams.owners+u))
      (roleAt (nativeRoleTicks blocks b h K s fixed each D.1 : Fin l.groups → Fin l.groups → ℕ)) ≤
      TeamRowPrepare.setup.slots + ((TeamRowPrepare.prepare.slots+5+nativeProbe n K h fixed each)*
      (l.groups^(n+1))^4 + nativeBit n b h K s*(1000000*X/256)) + 1 :=
  nativeTeamTicks_le result image team dispatch hd ht X s fixed each _ positive
    (fun u v => (roleAt_pair _ u v).le) cap

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
