import OAI.Hierarchy.DescentIssuedReset
import OAI.Hierarchy.DescentOrderedReentry
import OAI.Hierarchy.DescentResetAtomBudget

namespace OAI
/-! # Paying the first actual group stage following a rotor reset -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentColonies DescentHostDegree DescentMixedRouter DescentRotor DescentResetTrunks
open scoped Classical BigOperators
noncomputable section

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {q ε : ℝ} {G : PoweredGadget F}
  (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
variable {h C Ht f g cut : ℕ}
  (Z : ResetInput (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht)
  (T : Z.Terminals)
local notation "hg" => ResetInput.resetHostGain h (2^Z.n) Ht
local notation "J₁" => Fin (S.groupCount (i+1))

/-- A reset keeps the old common grain. Its new bank sites are new retained
atoms and its hub scale is exactly the actor budget of that same reset. -/
theorem reset_successor {L : ℕ}
    (key : (W.granular A.grainCount grain (A.grainCount_fit S ready)).graph.Edge ↪ Fin L)
    (digits : Block T.commonDepth ≃ J₁×Block k)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<S.height) (age : i<S.length) (radix : S.radix=2^k)
    (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (pos : Fintype.card Z.V=Fintype.card V)
    (unit : Z.unit=grain) (atHub : ∀u,Z.hub u=A.hub (A.pos u).2)
    (bill : Z.ActorBudget T A.records A.wire A.hist f g full)
    (rotor : 3*(2+rotorRate h C)*((2:ℝ)^f*full)+A.hist≤(2:ℝ)^g*full)
    (rows : 9*((2:ℝ)^f*full)+A.hist≤(2:ℝ)^g*full)
    (room : 3*((2:ℝ)^g*full)/256+A.hist≤(2:ℝ)^g*full)
    (range : Z.k-T.commonDepth≤k)
    (gain : hg≤S.hostGain) (rate : g≤S.capGain) (fineRate : g≤S.capGain-(G.b+3)) (cut₀ : packExponent 20 3≤cut) :
    ∃N : GroupStage (Z.orderedOrdinary T key) G q ε J₁ ↥(Z.commonNames T) k,
      N.StateBounds S (i+1) ∧ N.z=A.z ∧ N.wire=A.wire ∧ N.hist=A.hist ∧ N.degree=3 ∧ N.cap=2^g*A.cap ∧
        N.pos=Z.groupPosition T digits ∧ N.block=Z.groupBlock T digits ∧ N.hub=Z.commonTag T := by
  let newCap := 2^g*A.cap
  have hc : 0<newCap := Nat.mul_pos (Nat.two_pow_pos _) A.capPos
  have kept : ∀u,Z.hub u=true→A.records u=[] := fun u eq=>A.noHubAtoms u ((atHub u).symm.trans eq)
  have positions : Fintype.card Z.V≤S.hostSize i := pos.le.trans ready.host
  have groups := Z.reset_digit_population T S digits (by simp : Fintype.card J₁≤S.groupCount (i+1)) radix.ge
  obtain ⟨pay,history⟩ := Z.reset_atom_ledger T S A.records positive ready.atom age positions range gain radix.ge groups ready.history
  rw [←ready.valuation,←budget] at pay
  have actual : Fintype.card Z.V*(2^hg*2^k)≤S.hostSize (i+1) :=
    S.host_step positions (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) gain) radix.ge))
  have nextHost := (Z.placed_growth T range).trans actual
  have cap : newCap≤2^(8+S.capGain*(i+1)) := calc
    _ ≤ 2^S.capGain*2^(8+S.capGain*i) := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) rate) ready.capacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have fineCap : newCap≤2^(8+(S.capGain-(G.b+3))*(i+1)) := calc
    _ ≤ 2^(S.capGain-(G.b+3))*2^(8+(S.capGain-(G.b+3))*i) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) fineRate) ready.bundleCapacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have charged : q*((2^g*full:ℕ):ℝ)≤(2:ℝ)^(8+S.capGain*(i+1)) := calc
    _ = (q*((A.wire*grain:ℕ):ℝ))*(newCap:ℝ) := by dsimp [newCap];push_cast;ring
    _ ≤ newCap := by simpa using mul_le_mul_of_nonneg_right ready.paidUnit (Nat.cast_nonneg newCap)
    _ ≤ _ := by exact_mod_cast cap
  have counted : Fintype.card Z.V*(2^hg*2^k) ≤ S.initialSites *
      (2^S.hostGain*2^groupBits S.rounds S.height S.hostGain S.capGain cut)^(i+1) := by
    simpa only [AtomSchedule.hostSize,radix,fixed] using actual
  have roots := point_root_real (R:=S.baseGroups) (Nat.succ_le_of_lt age) counted cut₀ charged
  have scale : A.wire*grain*newCap=2^g*full := by dsimp [newCap];ring
  let raw := Z.physical_group_stage T A.records digits A.wire A.hist f g full bill
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using rotor)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using rows)
    (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using room) G q ε A.z newCap
    A.fieldBits A.pricePos A.wirePos A.unitPos hc unit scale kept pay range
    (by
      refine le_trans ?_ budget.ge
      simpa only [Fintype.card_fin,AtomSchedule.copies,AtomSchedule.groupCount,AtomSchedule.epochPower,
        AtomSchedule.length,radix,fixed,DescentCompiler.residual,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using roots)
  let N := Z.orderedStage T key raw
  have recorded := (congrArg (S.Within (i+1)) (Z.measured_count T A.records)).mpr history
  refine ⟨N,⟨Z.group_coordinates T digits,nextHost,cap,fineCap,recorded,ready.atom,ready.valuation,ready.paidUnit,?_⟩,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  intro e
  change grain∣(Z.orderedOrdinary T key).graph.width e
  apply (congrArg (fun u : ℕ => u ∣ (Z.orderedOrdinary T key).graph.width e) unit).mp
  rcases e with old|part
  · exact Z.reentry_divides T old.val
  · exact dvd_refl _

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
