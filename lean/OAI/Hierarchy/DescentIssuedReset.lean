import OAI.Hierarchy.DescentGrainSizes
import OAI.Hierarchy.DescentCollectedPhase
import OAI.Hierarchy.DescentFixedMenu
import OAI.Hierarchy.DescentFlattenGroups
import OAI.Hierarchy.DescentPhysicalGrainInput

namespace OAI
/-! # Building the configured reset on a genuine final ordinary graph -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ}

def «mutual» (v : V) := (A.near v).filter (fun w=>v∈A.near w)
private theorem mutual_symmetric (v w : V) : w∈A.mutual v ↔ v∈A.mutual w := by simp [«mutual»,and_comm]

variable {n h C bitsR f g cut K m : ℕ} (board : Graph n h)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
local notation "positions" => (fun u => Prod.snd (A.pos u))
local notation "ht" => 2*max (terminalDepth A.degree (2^n) f g false) (terminalDepth A.degree (2^n) f g true)

/-- Native vector views of this specific completed ordinary branch. -/
def resetLoad (digits : Block m≃J×Block k) : V→Block m→ℕ :=
  let raw := W.countWorld A.grainCount
  blockMass raw.graph positions (filled W.graph A.pos A.block digits)
    (raw.siteUnits (A.hub ∘ positions) A.records (A.wire*grain) 256 A.hist)

theorem issued_reset_with_rosters (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ)) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),
      Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
        Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
        (∃frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
          ResetInput.SourceFrame.Roster Z T positions (filled W.graph A.pos A.block digits) A.hub g frame
            vertex A.mutual n f full A.wire K (fun v w j=>
            (pairLoad (W.countWorld A.grainCount) positions (filled W.graph A.pos A.block digits) (A.wire*grain) v w j:ℝ)) A.degree (A.resetLoad digits)) ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  let ix := filled W.graph A.pos A.block digits
  let load := W.siteUnits (fun u=>A.hub (A.pos u).2) A.records A.wire 256 A.hist
  have reindex (v : V) (t : Block m) := filled_mass W.graph A.pos A.block digits load v t
  have bound (v : V) (t : Block m) : blockMass W.graph positions ix load v t≤full :=
    (reindex v t).le.trans (A.small _ _)
  have hubs (v : V) (hu : A.hub v=true) (t : Block m) : blockMass W.graph positions ix load v t=full :=
    (reindex v t).trans (A.saturated _ hu _)
  have edges (e : W.graph.Edge) :=
    filled_edges W.graph A.pos A.block digits A.near (fun e=>(A.peers e).1) A.same e
  have peer (e : W.graph.Edge) : positions (W.graph.dst e)∈A.mutual (positions (W.graph.src e)) := by
    have forward := (edges e).2
    exact Finset.mem_filter.mpr ⟨forward,(A.symmetric _ _).mp forward⟩
  have cap : q*(full:ℝ)≤(2:ℝ)^(8+S.capGain*i) := calc
    _ = (q*((A.wire*grain:ℕ):ℝ))*A.cap := by push_cast;ring
    _ ≤ (1:ℝ)*A.cap := mul_le_mul_of_nonneg_right ready.paidUnit (by positivity)
    _ ≤ _ := by simpa only [one_mul,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le.mpr ready.capacity : (A.cap:ℝ)≤((2^(8+S.capGain*i):ℕ):ℝ))
  have counted : Fintype.card V ≤ S.initialSites *
      (2^S.hostGain * 2^groupBits S.rounds S.height S.hostGain S.capGain cut)^i := by
    simpa only [AtomSchedule.hostSize,radix,fixed] using ready.host
  have actual := point_root_real (R:=S.baseGroups) realAge counted fcut cap
  have root : (Fintype.card V:ℝ)*(2:ℝ)^(m-k)*((2:ℝ)^f*full)≤ε/q := by
    apply (le_div_iff₀ A.pricePos).mpr
    have block : (2:ℝ)^(m-k)=(S.groupCount i:ℝ) := by exact_mod_cast remaining
    rw [block]
    refine le_trans ?_ budget.ge
    simpa only [AtomSchedule.groupCount,AtomSchedule.epochPower,AtomSchedule.length,AtomSchedule.copies,
      DescentCompiler.residual,radix,fixed,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_assoc,mul_left_comm,mul_comm] using actual
  have history : (A.hist:ℝ)*(∑v,((A.records v).length:ℝ))≤ε/q := by
    apply (le_div_iff₀ A.pricePos).mpr
    simpa only [Nat.cast_sum,mul_assoc,mul_comm,mul_left_comm] using A.retained
  have cancel : q*(ε/q)=ε := by field_simp [A.pricePos.ne']
  have physical := physical_grain_budgets_with_order_rosters W A.grainCount grain (A.grainCount_fit S ready)
    positions ix A.hub A.records A.wire A.hist board order vertex A.mutual (mutual_symmetric A) A.degreeMin
    (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v)) quota ports hK (fg.trans gk) km fg
    (gk.trans km) A.wirePos (Nat.mul_pos A.unitPos G.base_pos)
    (Nat.le_mul_of_pos_right _ A.capPos) positiveRotor rows menu bound hubs peer
    (fun e=>(edges e).1) A.incidence.inside A.incidence.outside q (ε/q) A.pricePos
    (by simpa only [Nat.cast_mul] using root) history tail
  rw [cancel] at physical
  obtain ⟨Z,T,cost,zk,depth,zn,card,unit,width,boardEq,⟨frame,roster⟩,tickets⟩ := physical
  refine ⟨Z,T,cost,zk,?_,zn,card,unit,width,boardEq,⟨frame,?_⟩,tickets⟩
  · simpa only [max_eq_left gk] using depth
  · unfold resetLoad
    dsimp only [ix] at roster
    with_unfolding_all exact roster

theorem issued_reset_ordered (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ)) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),
      Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
        Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧
        Nonempty (Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g) ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  obtain ⟨Z,T,cost,zk,group,zn,sz,unit,_,_,⟨frame,_⟩,tickets⟩:=issued_reset_with_rosters A S board order vertex
    ready realAge digits remaining radix fixed budget fcut fg gk km quota ports hK positiveRotor rows menu tail
  exact ⟨Z,T,cost,zk,group,zn,sz,unit,⟨frame⟩,tickets⟩

theorem issued_reset (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ)) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),
      Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
        Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧
        Nonempty (Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g) := by
  obtain ⟨Z,T,cost,zk,group,zn,sz,unit,frame,_⟩ :=
    issued_reset_ordered A S board (Fintype.equivFin _).toEmbedding ((Fintype.equivFin V).toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩) ready realAge digits remaining radix
      fixed budget fcut fg gk km quota ports hK positiveRotor rows menu tail
  exact ⟨Z,T,cost,zk,group,zn,sz,unit,frame⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
