import OAI.Hierarchy.DescentIssuedNativeReset
import OAI.Hierarchy.DescentCanonicalTrajectory

namespace OAI
/-! # One native vertex order, measured depth array and first-index basis for each issued reset -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open DescentLinearLayouts Computability.VPVNP.BurstRAM PrivateRAM DescentBaseVariance DescentIntegerScale DescentGL.PhysicalTrajectory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ}

variable {n h C bitsR f g cut K m : ℕ} (board : Graph n h)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
local notation "positions" => (fun u=>(A.pos u).2)
local notation "ht" => 2*max (terminalDepth A.degree (2^n) f g false) (terminalDepth A.degree (2^n) f g true)

/-- The reached parent already numbers every live vertex in a dense bank. -/
def numberedHeader (digits : Block m ≃ J × Block k) (vertex : V ↪ Fin (Fintype.card V)) :
    A.MixerHeader digits :=
  A.mixerHeader digits (Equiv.ofBijective vertex ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨vertex.injective, by simp⟩))

def MixerHeader.integerWeights {digits : Block m ≃ J × Block k} (H : A.MixerHeader digits)
    (f K : ℕ) : Fin (m+1) → Bits m → ℕ :=
  mixingWeightNumerator (inputLevels (k:=m) (H.depth A f)) (inputDepth (H.depth A f))
    (pairDepth A.mutual (H.depth A f))
    (fun v z => A.resetLoad digits v (DescentColonies.address m z))
    (fun c z => A.resetFlow digits c.1 c.2.val (DescentColonies.address m z)) f full K

def MixerHeader.chosenBasis {digits : Block m ≃ J × Block k} (H : A.MixerHeader digits)
    (f K : ℕ) : Layout m :=
  canonicalTrajectory (H.integerWeights A f K) (2^f*full) m

theorem issued_reset_canonical_rosters (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        frame.basis=H.chosenBasis A f K ∧ (∀v,Z.placement.b (frame.host v)=H.depth A f v) ∧ ResetInput.SourceFrame.Roster Z T positions (filled W.graph A.pos A.block digits) A.hub g frame (H.vertex A) A.mutual n f full A.wire K (fun v w j=>(A.resetFlow digits v w j:ℝ)) A.degree (A.resetLoad digits) ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  apply issued_reset_from_roster_mixer A S board order ready realAge digits remaining radix fixed
    budget fcut fg gk km quota ports hK positiveRotor rows menu tail H (·=H.chosenBasis A f K)
  intro geom limit incidence ep hB hh
  have sym (v z) : z∈A.mutual v ↔ v∈A.mutual z := by simp [«mutual»,and_comm]
  refine ⟨H.chosenBasis A f K,rfl,?_⟩
  exact paid_of_subaverage A.mutual (A.resetLoad digits) (A.resetFlow digits) (H.depth A f) _
    sym A.degreeMin (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v)) hB hK limit
    incidence (ε/q) ep hh tail geom (H.chosenBasis A f K)
    (canonicalTrajectory_bound (H.integerWeights A f K) (2^f*full))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
