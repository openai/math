import OAI.Hierarchy.DescentIssuedReset
import OAI.Hierarchy.DescentNativeResetGeometry

namespace OAI
/-! # Installing a reset from the same genuinely executed GL matrix -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open DescentLinearLayouts Computability.VPVNP.BurstRAM PrivateRAM DescentBaseVariance DescentIntegerScale DescentGL.PhysicalTrajectory
open ThreeFlat.RAM PhysicalProcedure
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

def resetFlow (digits : Block m≃J×Block k) : V→V→Block m→ℕ :=
  pairLoad (W.countWorld A.grainCount) positions (filled W.graph A.pos A.block digits) (A.wire*grain)

structure MixerHeader (digits : Block m≃J×Block k) where
  sites : ℕ
  site : V≃Fin sites
  neighbors : Native.Neighbors sites
  loads : Native.Rows sites (2^m)
  topology : ∀v,(A.mutual v).map site.toEmbedding=measuredNear neighbors (site v)
  payload : ∀v j,measuredLoad loads (site v) j=A.resetLoad digits v j
  degree : ∀v : Fin sites,(neighbors[v.val]).length≤A.degree

/-- Host IDs uniquely fix the address order. Each list enumerates only the
actual neighbors at that address, and each row contains its original mass. -/
def mixerHeader (digits : Block m≃J×Block k) {N : ℕ} (idx : V≃Fin N) : A.MixerHeader digits where
  sites := N
  site := idx
  neighbors := Vector.ofFn (fun t=>((A.mutual (idx.symm t)).map idx.toEmbedding).sort (·≤·))
  loads := Vector.ofFn (fun t=>Vector.ofFn (fun j=>A.resetLoad digits (idx.symm t) j))
  topology v := by simp [measuredNear,Finset.sort_toFinset]
  payload v j := by simp [measuredLoad]
  degree v := by
    simp only [Vector.getElem_ofFn,Finset.length_sort,Finset.card_map]
    exact (Finset.card_filter_le ..).trans (A.degreeBound (idx.symm v))

def MixerHeader.depth {digits : Block m≃J×Block k} (H : A.MixerHeader digits) (f : ℕ) (v : V) :=
  measuredDepth H.neighbors H.loads A.degree k f full (H.site v)

def MixerHeader.vertex {digits : Block m≃J×Block k} (H : A.MixerHeader digits) : V↪ℕ :=
  H.site.toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩

theorem issued_reset_from_roster_mixer (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) (R : Layout m→Prop)
    (get : ∀(geom : BaseGeometry A.mutual A.degree k f full K (ε/q) (A.resetLoad digits)
      (fun v w j=>(A.resetFlow digits v w j:ℝ)) (H.depth A f))
      (_limit : ∀v j,A.resetLoad digits v j≤full)
      (_inc : ∀v j,∑w∈A.mutual v,A.resetFlow digits v w j≤A.resetLoad digits v j)
      (_ep : 0≤ε/q) (_hB : 0<full) (_hh : 0<nonhubHops A.degree (2^n)),
      ∃μ : Layout m,R μ ∧ PaidResetLayout A.mutual A.degree k f full K (nonhubHops A.degree (2^n)) (ε/q)
        (A.resetLoad digits) (fun v w j=>(A.resetFlow digits v w j:ℝ)) (H.depth A f)
        (fun v=>(geom.bounds v).2.trans (Nat.sub_le m f)) μ) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        R frame.basis ∧ (∀v,Z.placement.b (frame.host v)=H.depth A f v) ∧ ResetInput.SourceFrame.Roster Z T positions (filled W.graph A.pos A.block digits) A.hub g frame (H.vertex A) A.mutual n f full A.wire K (fun v w j=>(A.resetFlow digits v w j:ℝ)) A.degree (A.resetLoad digits) ∧
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
  let raw := W.countWorld A.grainCount
  have inc (v j) : ∑z∈A.mutual v,A.resetFlow digits v z j≤A.resetLoad digits v j :=
    pairLoad_le raw positions ix (A.wire*grain) (A.hub ∘ positions) A.records 256 A.hist (by decide) A.mutual v j
  have limits (v j) : A.resetLoad digits v j≤full := by
    exact (W.mass_of_counts A.grainCount grain (A.grainCount_fit S ready) positions ix (A.hub ∘ positions)
      A.records A.wire 256 A.hist v j).le.trans (bound v j)
  have sy (v w) : w∈A.mutual v ↔ v∈A.mutual w := by simp [«mutual»,and_comm]
  have hB : 0<full := Nat.mul_pos (Nat.mul_pos A.wirePos (Nat.mul_pos A.unitPos G.base_pos)) A.capPos
  have geom : BaseGeometry A.mutual A.degree k f full K (ε/q) (A.resetLoad digits)
        (fun v w j=>(A.resetFlow digits v w j:ℝ)) (H.depth A f) :=
    measured_bases_at H.site H.neighbors H.loads A.degree k f full K (ε/q)
      A.mutual (A.resetLoad digits) _ H.topology H.payload sy H.degree quota hK (fg.trans gk) km hB limits
      (fun v j=>by exact_mod_cast inc v j) (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using root)
  have ep : 0≤ε/q := (by positivity : 0≤(Fintype.card V:ℝ)*(2:ℝ)^(m-k)*((2:ℝ)^f*full)).trans root
  obtain ⟨μ,cpu,score⟩ := get geom limits inc ep hB (by unfold nonhubHops;omega)
  have built :=
    physical_grain_budgets_for_ordered_rosters W A.grainCount grain (A.grainCount_fit S ready)
      positions ix A.hub A.records A.wire A.hist board order (H.vertex A) A.mutual sy A.degreeMin
      (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v)) quota ports hK (fg.trans gk) km fg
      (gk.trans km) A.wirePos (Nat.mul_pos A.unitPos G.base_pos)
      (Nat.le_mul_of_pos_right _ A.capPos) positiveRotor rows menu bound hubs peer
      (fun e=>(edges e).1) A.incidence.inside A.incidence.outside q (ε/q) A.pricePos
      (by simpa only [Nat.cast_mul] using root) history tail
      (H.depth A f) (fun v=>(geom.bounds v).2.trans (Nat.sub_le m f)) μ (by with_unfolding_all exact score)
  rw [cancel] at built
  obtain ⟨Z,T,cost,zk,group,zn,card,unit,width,boardEq,frame,basis,depthRead,roster,ticket⟩ := built
  refine ⟨Z,T,cost,zk,?_,zn,card,unit,width,boardEq,frame,?_,depthRead,?_,ticket⟩
  · simpa only [max_eq_left gk] using group
  · exact basis.symm ▸ cpu
  · unfold resetLoad resetFlow
    dsimp only [ix] at roster
    with_unfolding_all exact roster

theorem issued_reset_from_mixer (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) (R : Layout m→Prop)
    (get : ∀(geom : BaseGeometry A.mutual A.degree k f full K (ε/q) (A.resetLoad digits)
      (fun v w j=>(A.resetFlow digits v w j:ℝ)) (H.depth A f))
      (_limit : ∀v j,A.resetLoad digits v j≤full)
      (_inc : ∀v j,∑w∈A.mutual v,A.resetFlow digits v w j≤A.resetLoad digits v j)
      (_ep : 0≤ε/q) (_hB : 0<full) (_hh : 0<nonhubHops A.degree (2^n)),
      ∃μ : Layout m,R μ ∧ PaidResetLayout A.mutual A.degree k f full K (nonhubHops A.degree (2^n)) (ε/q)
        (A.resetLoad digits) (fun v w j=>(A.resetFlow digits v w j:ℝ)) (H.depth A f)
        (fun v=>(geom.bounds v).2.trans (Nat.sub_le m f)) μ) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        R frame.basis ∧ Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  obtain ⟨Z,T,cost,zk,group,zn,card,unit,_,_,frame,cpu,_,_,ticket⟩ :=
    issued_reset_from_roster_mixer A S board order ready realAge digits remaining radix fixed budget
      fcut fg gk km quota ports hK positiveRotor rows menu tail H R get
  exact ⟨Z,T,cost,zk,group,zn,card,unit,frame,cpu,ticket⟩

def ExecutedBasis {w : ℕ} (m base : ℕ) (bank : ℕ→ℕ) (mem : Memory w) (μ : Layout m) : Prop :=
  let out := finalMemory m base bank mem
  (PhysicalTrajectory.program w m base bank).Exec mem out (time m base bank m+DescentGLPermutationRAM.clock m) ∧
  (∀j : Fin m,out (pointer m base j.val)=((rowIndex m (rowFunctional μ j)).val:Word w)) ∧
  (∀z : Fin (2^m),out (outputBase m base+z.val)=
    ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm z))).val:Word w)) ∧
  ∀a<base,out a=mem a

theorem issued_reset_native (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) {w base : ℕ} (bank : ℕ→ℕ) (initial : Layout m) (mem : Memory w)
    (space : Room w m base bank) (scaleBits countBits gainBits massBits : ℕ)
    (scale : 2^f*full≤2^scaleBits)
    (members : (∑v,inputLevels (k:=m) (H.depth A f) v)+Fintype.card (Contacts A.mutual)≤2^countBits)
    (gain : ∀v (s : Fin (inputLevels (k:=m) (H.depth A f) v)),4*2^((s.val+7)/8)≤2^gainBits)
    (rate : K^2≤2^gainBits) (loads : ∀v,(∑i : Bits m,A.resetLoad digits v (address m i))≤2^massBits)
    (flows : ∀c : Contacts A.mutual,(∑i : Bits m,A.resetFlow digits c.1 c.2.val (address m i))≤2^massBits)
    (word : 3*m+(scaleBits+countBits+gainBits+2*massBits)+2≤w)
    (physical : ∀l (z : Fin (2^m)),mem (bank l.val+z.val)=
      (mixingWeightNumerator (inputLevels (k:=m) (H.depth A f)) (inputDepth (H.depth A f))
        (pairDepth A.mutual (H.depth A f)) (fun v i=>A.resetLoad digits v (address m i))
        (fun c i=>A.resetFlow digits c.1 c.2.val (address m i)) f full K l (DescentGLScoreRAM.vec z):Word w)) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        ExecutedBasis m base bank mem frame.basis ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  apply issued_reset_from_mixer A S board order ready realAge digits remaining radix fixed budget fcut fg gk km quota ports hK positiveRotor rows menu tail H (ExecutedBasis m base bank mem)
  intro geom limit incidence ep hB hh
  have sym (v z) : z∈A.mutual v ↔ v∈A.mutual z := by simp [«mutual»,and_comm]
  obtain ⟨execute,μ,paid,ptr,image,keep⟩ := mixer_paid A.mutual (A.resetLoad digits) (A.resetFlow digits)
    (H.depth A f) _ sym A.degreeMin (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v)) hB hK
    limit incidence (ε/q) ep hh tail geom bank initial mem space scaleBits countBits gainBits massBits
    scale members gain rate loads flows word physical
  exact ⟨μ,⟨execute,ptr,image,keep⟩,paid⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
