import OAI.Hierarchy.DescentIssuedNativeReset
import OAI.Hierarchy.DescentMeasuredSparseMixer

namespace OAI
/-! # From original branch measurements through the programmed optimizer to its installed geometry -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open DescentLinearLayouts Computability.VPVNP.BurstRAM PrivateRAM DescentBaseVariance DescentIntegerScale DescentGL.PhysicalTrajectory
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentMeasuredMixer DescentMeasuredWeights
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ}

variable {n h C bitsR f g cut K m : ℕ} (board : Graph n h)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
local notation "positions" => (fun u => Prod.snd (A.pos u))
local notation "ht" => 2*max (terminalDepth A.degree (2^n) f g false) (terminalDepth A.degree (2^n) f g true)

def measuredSiteRow (digits : Block m≃J×Block k) (v : V) (z : Bits m) :=
  A.resetLoad digits v (DescentColonies.address m z)

def measuredContactRow (digits : Block m≃J×Block k) (c : Contacts A.mutual) (z : Bits m) :=
  A.resetFlow digits c.1 c.2.val (DescentColonies.address m z)

section BankShape
variable {digits : Block m≃J×Block k} (H : A.MixerHeader digits) {N w base payloadBits gainBits : ℕ}
local notation "b" => H.depth A f
local notation "levels" => inputLevels (k:=m) b
local notation "lv" => inputDepth (k:=m) b
local notation "pair" => pairDepth A.mutual b
local notation "X" => A.measuredSiteRow digits
local notation "Y" => A.measuredContactRow digits
local notation "locType" => Item levels (Contacts A.mutual) ↪ Fin N

/-- The sparse measured mixer reads the actual branch load at each block,
each directed pair traffic, and the numerical levels and gains of those
rows. The larger joint numerator is computed by the program itself. -/
structure ResetMeasurements (loc : locType) (tab : Fin N→Header) (mem : Memory w) where
  room : PhysicalTrajectory.Room w m (mixerBase m base N) (DescentNativeColumns.address m (keyBase m base N))
  widths : payloadBits≤w ∧ gainBits≤w
  segments : ∀i,(Bank.mk (tab i).payload m).Fits w base ∧ (tab i).depth<base ∧ (tab i).gain<base
  heads : ∀i,mem (tab i).depth=((padded loc (level levels lv pair) 0 i : ℕ) : Word w) ∧
    mem (tab i).gain=((padded loc (gain levels f full K) 0 i : ℕ) : Word w)
  values : ∀i (z : Fin (2^m)),mem ((tab i).payload+z.val)=
    (padded loc (load levels X Y) (fun _=>0) i (DescentGLScoreRAM.vec z):Word w)
  inputWidth : ∀i,padded loc (level levels lv pair) 0 i<2^w ∧
    padded loc (gain levels f full K) 0 i<2^gainBits ∧
    ∀z,padded loc (load levels X Y) (fun _=>0) i z<2^payloadBits

end BankShape

def MeasuredRun {w N : ℕ} (m base payloadBits gainBits : ℕ) (tab : Fin N→Header) (mem : Memory w) (μ : Layout m) : Prop :=
  ∃ out : Memory w,
    (stages w m base payloadBits gainBits tab).Exec mem out (measuredTime w m base payloadBits gainBits tab) ∧
    (∀j : Fin m,out (pointer m (mixerBase m base N) j.val)=((rowIndex m (rowFunctional μ j)).val:Word w)) ∧
    (∀z : Fin (2^m),out (outputBase m (mixerBase m base N)+z.val)=
      ((finFunctionFinEquiv (μ (DescentGLScoreRAM.vec z))).val:Word w)) ∧ ∀a<base,out a=mem a

theorem issued_reset_measured_rosters (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) {N w base payloadBits gainBits : ℕ}
    (loc : (Item (inputLevels (k:=m) (H.depth A f)) (Contacts A.mutual) ↪ Fin N)) (tab : Fin N→Header) (mem : Memory w) (initial : Layout m)
    (physical : A.ResetMeasurements (K:=K) (base:=base) (payloadBits:=payloadBits) (gainBits:=gainBits) H loc tab mem)
    (scaleBits countBits rateBits massBits : ℕ)
    (scale : 2^f*full≤2^scaleBits)
    (members : (∑v,(inputLevels (k:=m) (H.depth A f)) v)+Fintype.card (Contacts A.mutual)≤2^countBits)
    (rateLevel : ∀v (t : Fin ((inputLevels (k:=m) (H.depth A f)) v)),4*2^((t.val+7)/8)≤2^rateBits)
    (ratePair : K^2≤2^rateBits) (mass : ∀v,(∑i,A.measuredSiteRow digits v i)≤2^massBits)
    (thin : ∀c,(∑i,A.measuredContactRow digits c i)≤2^massBits)
    (available : 3*m+(scaleBits+countBits+rateBits+2*massBits)+2≤w) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        MeasuredRun m base payloadBits gainBits tab mem frame.basis ∧
        (∀v,Z.placement.b (frame.host v)=H.depth A f v) ∧
        ResetInput.SourceFrame.Roster Z T positions (filled W.graph A.pos A.block digits) A.hub g frame
          (H.vertex A) A.mutual n f full A.wire K (fun v w j=>(A.resetFlow digits v w j:ℝ)) A.degree (A.resetLoad digits) ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  apply issued_reset_from_roster_mixer A S board order ready realAge digits remaining radix fixed budget fcut fg gk km
    quota ports hK positiveRotor rows menu tail H (MeasuredRun m base payloadBits gainBits tab mem)
  intro geom limit incidence ep hB hh
  let lev := inputLevels (k:=m) (H.depth A f)
  let depth := inputDepth (k:=m) (H.depth A f)
  let peer := pairDepth A.mutual (H.depth A f)
  obtain ⟨out,μ,run,price,ptr,remix,keep⟩ :=
    sparse_result (inputLevels (k:=m) (H.depth A f)) loc (inputDepth (k:=m) (H.depth A f)) (pairDepth A.mutual (H.depth A f)) (A.measuredSiteRow digits) (A.measuredContactRow digits) f full K mem tab initial physical.room available hB
      physical.widths physical.segments physical.heads physical.values physical.inputWidth
      (fun l d=>mixingWeightNumerator_bound lev depth peer (A.measuredSiteRow digits) (A.measuredContactRow digits) f full K l d
        scaleBits countBits rateBits massBits scale members rateLevel ratePair mass thin)
  have sym (v z) : z∈A.mutual v ↔ v∈A.mutual z := by simp [«mutual»,and_comm]
  refine ⟨μ,⟨out,run,ptr,remix,keep⟩,?_⟩
  exact paid_of_subaverage A.mutual (A.resetLoad digits) (A.resetFlow digits) (H.depth A f) _ sym A.degreeMin
    (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v)) hB hK limit incidence (ε/q) ep hh tail geom μ price

theorem issued_reset_measured (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) {N w base payloadBits gainBits : ℕ}
    (loc : (Item (inputLevels (k:=m) (H.depth A f)) (Contacts A.mutual) ↪ Fin N)) (tab : Fin N→Header) (mem : Memory w) (initial : Layout m)
    (physical : A.ResetMeasurements (K:=K) (base:=base) (payloadBits:=payloadBits) (gainBits:=gainBits) H loc tab mem)
    (scaleBits countBits rateBits massBits : ℕ)
    (scale : 2^f*full≤2^scaleBits)
    (members : (∑v,(inputLevels (k:=m) (H.depth A f)) v)+Fintype.card (Contacts A.mutual)≤2^countBits)
    (rateLevel : ∀v (t : Fin ((inputLevels (k:=m) (H.depth A f)) v)),4*2^((t.val+7)/8)≤2^rateBits)
    (ratePair : K^2≤2^rateBits) (mass : ∀v,(∑i,A.measuredSiteRow digits v i)≤2^massBits)
    (thin : ∀c,(∑i,A.measuredContactRow digits c i)≤2^massBits)
    (available : 3*m+(scaleBits+countBits+rateBits+2*massBits)+2≤w) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        MeasuredRun m base payloadBits gainBits tab mem frame.basis ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  obtain ⟨Z,T,cost,zk,group,zn,card,unit,_,_,frame,cpu,_,_,ticket⟩ :=
    issued_reset_measured_rosters A S board order ready realAge digits remaining radix fixed budget fcut
      fg gk km quota ports hK positiveRotor rows menu tail H loc tab mem initial physical
      scaleBits countBits rateBits massBits scale members rateLevel ratePair mass thin available
  exact ⟨Z,T,cost,zk,group,zn,card,unit,frame,cpu,ticket⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
