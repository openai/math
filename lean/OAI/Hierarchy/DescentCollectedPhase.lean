import OAI.Hierarchy.DescentStateBounds
import OAI.Hierarchy.DescentNamedGeometry
import OAI.Hierarchy.DescentScannedAtomBudget
import OAI.Hierarchy.DescentStageNumbers

namespace OAI
/-! # Paying and advancing one actual scanned ordinary branch -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {price ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule) (i f : ℕ)
local notation "a" => packExponent 20 A.degree
local notation "g" => gainExponent 20 A.degree
local notation "slots" => (2^a+2)
local notation "nextDegree" => (((A.degree+1)*(gap A.degree+g+1+2^(gap A.degree+g))*slots)^10)
local notation "raw" => (Fintype.card V*2^(k+1)*slots)
local notation "load" => (A.wire*(A.z*G.b)*A.cap)

theorem next_state_particles {J₁ : Type} [Fintype J₁] [DecidableEq J₁] (input : StateBounds A S i)
    (hε : 0≤ε) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<S.height) (age : i<S.length) (radix : S.radix=2^k)
    (fixedWidth : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (pop : Fintype.card J≤S.groupCount i) (sub : Fintype.card J₁=S.groupCount (i+1))
    (digits : J≃J₁×Block k)
    (globalSites : 2*slots≤2^S.hostGain) (hub : 2^g*G.b≤2^S.capGain)
    (fineGrowth : 2^g*G.b≤2^(S.capGain-(G.b+3)))
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextID : J₁↪ℕ) (vertex : V↪ℕ)
    (cut : packExponent 20 nextDegree≤f) (localAge : g≤k) {newZ : ℕ}
    (grain : A.z=newZ*G.b) (histCost : 6*A.hist≤A.wire*(A.z*G.b))
    (c : (A.stage.result hε).Choice) :
    ∃n : Normalize ((A.stage.result hε).state c),
      ∃A' : GroupStage n.result G price ε J₁ (Host V k slots) k,
        (ParticleRows hε A.stage c _ n (fun v=>(A'.records v).length) (fun v=>A'.hub (A'.pos v).2) ∧
          HubRows A hε digits A' (Function.Embedding.subtype _) ∧
          VenueRows A hε A.stage c digits n A' (Function.Embedding.subtype _) ∧ (∀v,A'.hub v=publishedHub A.hub k g v.val) ∧
          A'.near=restrictedNear A.near (gap A.degree+g) k slots ∧ IntrinsicallySorted n.result ∧ n.nameCount=1) ∧
        (∃ tape : DescentStageEdgeReceipt.Tape n.result.graph.Edge, ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
          DescentStageEdgeReceipt.IssuedRows hε A.stage c order (DescentStageEdgeReceipt.groupRank groupID vertex) _ n tape pair ∧
          ∀x,DescentPacking.originalId n.result.graph.Edge x=(tape.selector x).val) ∧ Normalize.CutsEqual A.z n ∧
        A'.SiteNamed (DescentStageEdgeReceipt.groupRank nextID (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧ StateBounds A' S (i+1) ∧
        A'.z=newZ ∧ A'.cap=2^g*G.b*A.cap ∧ A'.wire=A.wire ∧ A'.hist=A.hist ∧ A'.degree=nextDegree := by
  have base := G.base_pos
  have newPos : 0<newZ := by
    by_contra! eq
    have z0 : newZ=0 := by omega
    have := A.unitPos
    simp [z0] at grain
    omega
  have capNext : 2^g*G.b*A.cap≤2^(8+S.capGain*(i+1)) := calc
    _ ≤ 2^S.capGain*2^(8+S.capGain*i) := Nat.mul_le_mul hub input.capacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have bundleNext : 2^g*G.b*A.cap≤2^(8+(S.capGain-(G.b+3))*(i+1)) := calc
    _ ≤ 2^(S.capGain-(G.b+3))*2^(8+(S.capGain-(G.b+3))*i) :=
      Nat.mul_le_mul fineGrowth input.bundleCapacity
    _ = _ := by rw [←pow_add];congr 1;ring
  have growth : raw≤Fintype.card V*(2^S.hostGain*S.radix) := by
    rw [radix,pow_succ]
    calc
      _ = Fintype.card V*((2*slots)*2^k) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ globalSites)
  have rawBound := S.host_step input.host growth
  have hostCount : Fintype.card (Host V k slots) ≤ raw := host_size
  have hostNext := hostCount.trans rawBound
  have charge : price*((2^g*load:ℕ):ℝ) ≤ (2:ℝ)^(8+S.capGain*(i+1)) := by
    have cap8 : 2^g*A.cap ≤ 2^(8+S.capGain*(i+1)) :=
      (Nat.mul_le_mul_right A.cap (by simpa using Nat.mul_le_mul_left (2^g) (show 1≤G.b from base))).trans capNext
    have h := mul_le_mul_of_nonneg_right input.paidUnit (show (0:ℝ)≤(2^g*A.cap:ℕ) by positivity)
    calc
      _ = (price*((A.wire*(A.z*G.b):ℕ):ℝ))*((2^g*A.cap:ℕ):ℝ) := by push_cast;ring
      _ ≤ ((2^g*A.cap:ℕ):ℝ) := by simpa using h
      _ ≤ _ := by exact_mod_cast cap8
  have counted : raw≤S.initialSites*(2^S.hostGain*2^groupBits S.rounds S.height S.hostGain S.capGain f)^(i+1) := by
    simpa [AtomSchedule.hostSize,radix,←fixedWidth] using rawBound
  have invoice := point_root_real (R:=S.baseGroups) (Nat.succ_le_of_lt age) counted cut charge
  have root : ((Fintype.card J₁*raw:ℕ):ℝ)*((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*load:ℕ):ℝ)))≤ε := by
    simpa only [budget,sub,AtomSchedule.copies,AtomSchedule.groupCount,AtomSchedule.epochPower,
      AtomSchedule.length,radix,fixedWidth,DescentCompiler.residual,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using invoice
  obtain ⟨old,advance⟩ := A.scanned_atom_ledger S positive input.atom age input.host pop radix.ge input.capacity input.history input.valuation budget
  obtain ⟨n,A',particles,tape,cuts,named,coords,z,cap,wire,hist,degree,divs,pairs,born,fits⟩ :=
    A.scanned_geometry_named_particles hε digits A.fieldBits
      (by dsimp [gainExponent];omega) localAge newZ newPos grain histCost old root order groupID nextID vertex c
  have save : newZ≤A.z := by rw [grain];simpa using Nat.mul_le_mul_left newZ base
  have nextCharge : price*((A'.wire*(A'.z*G.b):ℕ):ℝ)≤1 := by
    rw [wire,z]
    apply le_trans _ input.paidUnit
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ save))) A.pricePos.le
  refine ⟨n,A',particles,tape,cuts,named,⟨coords,hostNext,cap ▸ capNext,cap ▸ bundleNext,?_,hist ▸ input.atom,hist ▸ input.valuation,
    nextCharge,divs input.divides⟩,z,cap,wire,hist,degree⟩
  rw [born]
  exact advance pairs fits

theorem next_state_rows {J₁ : Type} [Fintype J₁] [DecidableEq J₁] (input : StateBounds A S i)
    (hε : 0≤ε) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<S.height) (age : i<S.length) (radix : S.radix=2^k)
    (fixedWidth : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (pop : Fintype.card J≤S.groupCount i) (sub : Fintype.card J₁=S.groupCount (i+1))
    (digits : J≃J₁×Block k)
    (globalSites : 2*slots≤2^S.hostGain) (hub : 2^g*G.b≤2^S.capGain)
    (fineGrowth : 2^g*G.b≤2^(S.capGain-(G.b+3)))
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextID : J₁↪ℕ) (vertex : V↪ℕ)
    (cut : packExponent 20 nextDegree≤f) (localAge : g≤k) {newZ : ℕ}
    (grain : A.z=newZ*G.b) (histCost : 6*A.hist≤A.wire*(A.z*G.b))
    (c : (A.stage.result hε).Choice) :
    ∃n : Normalize ((A.stage.result hε).state c),
      ∃A' : GroupStage n.result G price ε J₁ (Host V k slots) k,
        (∃ tape : DescentStageEdgeReceipt.Tape n.result.graph.Edge, ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
          DescentStageEdgeReceipt.IssuedRows hε A.stage c order (DescentStageEdgeReceipt.groupRank groupID vertex) _ n tape pair ∧
          ∀x,DescentPacking.originalId n.result.graph.Edge x=(tape.selector x).val) ∧ Normalize.CutsEqual A.z n ∧
        A'.SiteNamed (DescentStageEdgeReceipt.groupRank nextID (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧ StateBounds A' S (i+1) ∧
        A'.z=newZ ∧ A'.cap=2^g*G.b*A.cap ∧ A'.wire=A.wire ∧ A'.hist=A.hist ∧ A'.degree=nextDegree := by
  obtain ⟨n,b,_,rest⟩ := A.next_state_particles S i f input hε budget positive age radix fixedWidth pop sub
    digits globalSites hub fineGrowth order groupID nextID vertex cut localAge grain histCost c
  exact ⟨n,b,rest⟩

theorem next_state {J₁ : Type} [Fintype J₁] [DecidableEq J₁] (input : StateBounds A S i)
    (hε : 0≤ε) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (positive : 0<S.height) (age : i<S.length) (radix : S.radix=2^k)
    (fixedWidth : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (pop : Fintype.card J≤S.groupCount i) (sub : Fintype.card J₁=S.groupCount (i+1))
    (digits : J≃J₁×Block k)
    (globalSites : 2*slots≤2^S.hostGain) (hub : 2^g*G.b≤2^S.capGain)
    (fineGrowth : 2^g*G.b≤2^(S.capGain-(G.b+3)))
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextID : J₁↪ℕ) (vertex : V↪ℕ)
    (cut : packExponent 20 nextDegree≤f) (localAge : g≤k) {newZ : ℕ}
    (grain : A.z=newZ*G.b) (histCost : 6*A.hist≤A.wire*(A.z*G.b))
    (c : (A.stage.result hε).Choice) :
    ∃n : Normalize ((A.stage.result hε).state c),
      ∃A' : GroupStage n.result G price ε J₁ (Host V k slots) k,
        (∃ tape : DescentStageEdgeReceipt.Tape n.result.graph.Edge, DescentStageEdgeReceipt.Issued W G order
          (DescentStageEdgeReceipt.groupRank groupID vertex) _ n tape ∧
          ∀x,DescentPacking.originalId n.result.graph.Edge x=(tape.selector x).val) ∧ Normalize.CutsEqual A.z n ∧
        A'.SiteNamed (DescentStageEdgeReceipt.groupRank nextID (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧ StateBounds A' S (i+1) ∧
        A'.z=newZ ∧ A'.cap=2^g*G.b*A.cap ∧ A'.wire=A.wire ∧ A'.hist=A.hist ∧ A'.degree=nextDegree := by
  obtain ⟨n,A',⟨tape,pair,receipt,identifiers⟩,remaining⟩ :=
    A.next_state_rows S i f input hε budget positive age radix fixedWidth pop sub digits globalSites hub
      fineGrowth order groupID nextID vertex cut localAge grain histCost c
  exact ⟨n,A',⟨tape,receipt.toIssued,identifiers⟩,remaining⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
