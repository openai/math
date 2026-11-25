import OAI.Hierarchy.DescentDensePhysicalOrder
import OAI.Hierarchy.DescentScannedGeometry
import OAI.Hierarchy.DescentSourceSorted
import OAI.Hierarchy.DescentGroupStageNames

namespace OAI
/-! # Bind the next actual graph to its physical site and cable rows -/

namespace Hierarchy.DescentSixParty.GroupStage
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentGL DescentWalshTables
open StarKeys GadgetNetwork MarkedWorld DescentHostDegree DescentHostDirectory
open scoped Classical BigOperators
noncomputable section
variable {P : Type} {d k n : ℕ} {bits : P→ℕ} {F : Type} [Field F]
variable {G : PoweredGadget F} {W : MarkedWorld F d P bits} {ε price : ℝ}
variable {J J₁ V : Type} [Fintype J] [Fintype J₁] [Fintype V] [DecidableEq J] [DecidableEq J₁] [DecidableEq V]
variable (A : GroupStage W G price ε J V k)
local notation "a" => packExponent 20 A.degree
local notation "g" => gainExponent 20 A.degree
local notation "window" => gap A.degree+g
local notation "slots" => (2^a+2)
local notation "nextDegree" => (((A.degree+1)*(window+1+2^window)*slots)^10)
local notation "unit" => A.wire*(A.z*G.b)
local notation "U" => unit*A.cap


/-- An extended host name and the remaining original block ordinal together
identify each site. The block digit is the final radix field of the key. -/
def siteFrom (rank : J×V↪ℕ) (coord : Function.Injective (fun u=>(A.pos u,A.block u))) : W.graph.Site↪ℕ where
  toFun u := rank (A.pos u)*2^k+(A.block u).val
  inj' := by
    intro x y same
    have hp : 0<(2:ℕ)^k := by positivity
    change rank (A.pos x)*2^k+(A.block x).val=rank (A.pos y)*2^k+(A.block y).val at same
    have h := congrArg (·/2^k) same
    have b := congrArg (·%2^k) same
    simp only [Nat.mul_comm (rank (A.pos x)) (2^k), Nat.mul_comm (rank (A.pos y)) (2^k),
      Nat.mul_add_div hp, Nat.div_eq_of_lt (A.block x).isLt,
      Nat.div_eq_of_lt (A.block y).isLt, Nat.add_zero] at h
    simp only [Nat.mul_add_mod_of_lt (A.block x).isLt,
      Nat.mul_add_mod_of_lt (A.block y).isLt] at b
    exact coord (Prod.ext (rank.injective h) (Fin.ext b))

/-- Canonical semantic site names in this world have the precise numeric
order obtained by prefixing the occupied host/row directory. -/
def SiteNamed (rank : J×V↪ℕ) : Prop := ∀u : W.graph.Site,
  originalId W.graph.Site u=(Finset.univ.filter fun v=>
    rank (A.pos v)*2^k+(A.block v).val < rank (A.pos u)*2^k+(A.block u).val).card

theorem siteNamed_names (rank : J×V↪ℕ) (coord : Function.Injective (fun v=>(A.pos v,A.block v)))
    (edge : Equiv.Perm W.graph.Edge) :
    (A.names (DescentPhysicalOrder.rename (A.siteFrom rank coord)) edge).SiteNamed rank := by
  let r := A.siteFrom rank coord
  let s := DescentPhysicalOrder.rename r
  intro u
  obtain ⟨v,rfl⟩ := s.surjective u
  have numbered : originalId W.graph.Site (s v)=(Finset.univ.filter fun t=>r t<r v).card :=
    (congrArg Fin.val (DescentPhysicalOrder.code_rename r v)).trans (DescentPhysicalOrder.physical_val r v)
  apply numbered.trans
  apply Finset.card_bij (fun t _=>s t)
  · intro t ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change r (s.symm (s t)) < r (s.symm (s v))
    simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp ht).2
  · exact fun _ _ _ _ h=>s.injective h
  · intro t ht
    obtain ⟨j,rfl⟩ := s.surjective t
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    have smaller : r (s.symm (s j)) < r (s.symm (s v)) := (Finset.mem_filter.mp ht).2
    simpa only [Equiv.symm_apply_apply] using smaller

theorem cast_siteNamed {W' : MarkedWorld F d P bits} (rank : J×V↪ℕ)
    (coord : Function.Injective (fun v=>(A.pos v,A.block v))) (edge : Equiv.Perm W.graph.Edge)
    (h : W'=PhysicalRename.world W (DescentPhysicalOrder.rename (A.siteFrom rank coord)) edge) :
    let N : GroupStage W' G price ε J V k := h.symm ▸ A.names (DescentPhysicalOrder.rename (A.siteFrom rank coord)) edge
    N.SiteNamed rank := by cases h; exact A.siteNamed_names rank coord edge

omit [Field F] in
theorem edgeNamed_after {W S : MarkedWorld F d P bits} (t : DescentStageEdgeReceipt.Tape W.graph.Edge)
    (s : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge) (eqn : S=PhysicalRename.world W s e) :
    let paper : DescentStageEdgeReceipt.Tape S.graph.Edge := eqn.symm ▸
      (show DescentStageEdgeReceipt.Tape (PhysicalRename.world W s e).graph.Edge from t.names e)
    ∀x,originalId S.graph.Edge x=(paper.selector x).val := by
  subst S
  intro paper x
  rfl

/-- Field and incidence measures after casting the new physical names.
The numbered tapes retain all scalar, width and history charges. -/
theorem renamed_fields {W' : MarkedWorld F d P bits} (v : Equiv.Perm W.graph.Site)
    (e : Equiv.Perm W.graph.Edge) (eqn : W'=PhysicalRename.world W v e) :
    let N : GroupStage W' G price ε J V k := eqn.symm ▸ A.names v e
    N.z=A.z ∧ N.cap=A.cap ∧ N.wire=A.wire ∧ N.hist=A.hist ∧ N.degree=A.degree ∧
    (Function.Injective (fun x=>(A.pos x,A.block x))→Function.Injective (fun x=>(N.pos x,N.block x))) ∧
    (∀q,(∀i,q∣W.graph.width i)→∀i,q∣W'.graph.width i) ∧
    (∑u,(N.records u).length)=∑u,(A.records u).length := by
  subst W'
  refine ⟨rfl,rfl,rfl,rfl,rfl,A.names_coordinates v e,fun q old x=>old (e.symm x),?_⟩
  exact eqa v
where
  eqa (v : Equiv.Perm W.graph.Site) :
      (∑x,(A.records (v.symm x)).length)=∑x,(A.records x).length :=
    v.symm.sum_comp (fun x=>(A.records x).length)

theorem renamed_particle_fields {K : Type} [Fintype K] [DecidableEq K] {Y : Type} [Fintype Y] [DecidableEq Y]
    {X X' : MarkedWorld F d P bits} {r : ℕ} (b : GroupStage X G price ε K Y r)
    (s : Equiv.Perm X.graph.Site) (e : Equiv.Perm X.graph.Edge) (eqn : X'=PhysicalRename.world X s e) :
    let b' : GroupStage X' G price ε K Y r := eqn.symm ▸ b.names s e
    (fun v=>(b'.records v).length)=transferRow eqn ((fun v=>(b.records v).length)∘s.symm) ∧
    (fun v=>b'.hub (b'.pos v).2)=transferRow eqn ((fun v=>b.hub (b.pos v).2)∘s.symm) ∧ b'.hub=b.hub := by
  subst X'
  exact ⟨rfl,rfl,rfl⟩

theorem scanned_geometry_named_particles (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextGroup : J₁↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (ParticleRows hε A.stage c _ norm (fun v=>(next.records v).length) (fun v=>next.hub (next.pos v).2) ∧
          HubRows A hε digits next (Function.Embedding.subtype _) ∧
          VenueRows A hε A.stage c digits norm next (Function.Embedding.subtype _) ∧ (∀v,next.hub v=publishedHub A.hub k g v.val) ∧
          next.near=restrictedNear A.near window k slots ∧ IntrinsicallySorted norm.result ∧ norm.nameCount=1) ∧
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
            DescentStageEdgeReceipt.IssuedRows hε A.stage c oldOrder (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape pair ∧
          ∀x,originalId norm.result.graph.Edge x=(tape.selector x).val) ∧
        Normalize.CutsEqual A.z norm ∧
        next.SiteNamed (DescentStageEdgeReceipt.groupRank nextGroup (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  obtain ⟨norm,t,⟨atoms,hubRows,venueRows,hubFlags,nearRows,rawCount⟩,⟨tape,pair,issued⟩,cut,coord,hz,hc,hw,hh,hd,divs,nb,record,bound⟩ :=
    A.scanned_geometry_issued_particles hε digits hn ag gk newZ hz₁ grain histCost oldLedger rootLedger oldOrder groupID vertex c
  let nextHost := DescentStageEdgeReceipt.hostRank vertex k slots
  let id := t.siteFrom (DescentStageEdgeReceipt.groupRank nextGroup nextHost) coord
  let s := DescentPhysicalOrder.rename id
  let e := DescentPhysicalOrder.rename (tape.sourceKey norm.result.graph.src id norm.result.graph.width)
  let t' := afterNames norm t s e
  obtain ⟨z₁,c₁,w₁,h₁,d₁,coordinates,whole,sameCount⟩ :=
    renamed_fields t s e (norm.appendNames_result s e)
  have tags := renamed_particle_fields t s e (norm.appendNames_result s e)
  have retainedNear {Y : MarkedWorld F d P bits} (same : Y=PhysicalRename.world norm.result s e) :
      (show GroupStage Y G price ε J₁ (Host V k slots) n from same.symm ▸ t.names s e).near=t.near := by
    cases same
    rfl
  have fresh : ParticleRows hε A.stage c _ (norm.appendNames s e) (fun v=>(t'.records v).length) (fun v=>t'.hub (t'.pos v).2) := by
    rw [show (fun v=>(t'.records v).length)=_ from tags.1,show (fun v=>t'.hub (t'.pos v).2)=_ from tags.2.1]
    exact ParticleRows.named norm atoms s e
  refine ⟨norm.appendNames s e,t',⟨fresh,HubRows.cast_names A hε digits t (Function.Embedding.subtype _) hubRows s e (norm.appendNames_result s e),VenueRows.named A hε A.stage c digits t (Function.Embedding.subtype _) s e venueRows,fun v=>(congrFun tags.2.2 v).trans (hubFlags v),
    (retainedNear (norm.appendNames_result s e)).trans nearRows,(norm.appendNames_result s e).symm ▸ physically_sorted norm.result tape id,by rw [Normalize.nameCount_append,rawCount]⟩,⟨_,pair,DescentStageEdgeReceipt.IssuedRows.named norm tape issued id,
      edgeNamed_after tape s e (norm.appendNames_result s e)⟩,
    (Normalize.cutsEqual_appendNames A.z norm s e).2 cut,
    t.cast_siteNamed (DescentStageEdgeReceipt.groupRank nextGroup nextHost) coord e (norm.appendNames_result s e),
    coordinates coord,
    z₁.trans hz,c₁.trans hc,w₁.trans hw,h₁.trans hh,d₁.trans hd,?_,nb,sameCount.trans record,bound⟩
  intro smaller
  rw [show t'.z=t.z from z₁]
  exact whole _ (divs smaller)

theorem scanned_geometry_named_rows (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextGroup : J₁↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          ∃ pair : DescentStageEdgeReceipt.ScanNumbers hε A.stage,
            DescentStageEdgeReceipt.IssuedRows hε A.stage c oldOrder (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape pair ∧
          ∀x,originalId norm.result.graph.Edge x=(tape.selector x).val) ∧
        Normalize.CutsEqual A.z norm ∧
        next.SiteNamed (DescentStageEdgeReceipt.groupRank nextGroup (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  obtain ⟨norm,t,_,rest⟩ := A.scanned_geometry_named_particles hε digits hn ag gk newZ hz₁ grain histCost oldLedger
    rootLedger oldOrder groupID nextGroup vertex c
  exact ⟨norm,t,rest⟩

theorem scanned_geometry_named (hε : 0≤ε) (digits : J≃J₁×Block n)
    (hn : 0<n) (ag : a≤g) (gk : g≤k)
    (newZ : ℕ) (hz₁ : 0<newZ) (grain : A.z=newZ*G.b)
    (histCost : 6*A.hist≤unit)
    (oldLedger : price*A.hist*((∑u,(A.records u).length)+6*(W.liveWidth/(2*(A.z*G.b))):ℕ)≤ε)
    (rootLedger : ((Fintype.card J₁*(Fintype.card V*2^(k+1)*slots):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 nextDegree*(price*((2^g*U:ℕ):ℝ)))≤ε)
    (oldOrder : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (groupID : J↪ℕ) (nextGroup : J₁↪ℕ) (vertex : V↪ℕ)
    (c : (A.stage.result hε).Choice) :
    ∃ norm : Normalize ((A.stage.result hε).state c),
      ∃ next : GroupStage norm.result G price ε J₁ (Host V k slots) n,
        (∃ tape : DescentStageEdgeReceipt.Tape norm.result.graph.Edge,
          DescentStageEdgeReceipt.Issued W G oldOrder (DescentStageEdgeReceipt.groupRank groupID vertex) _ norm tape ∧
          ∀x,originalId norm.result.graph.Edge x=(tape.selector x).val) ∧
        Normalize.CutsEqual A.z norm ∧
        next.SiteNamed (DescentStageEdgeReceipt.groupRank nextGroup (DescentStageEdgeReceipt.hostRank vertex k slots)) ∧
        Function.Injective (fun v=>(next.pos v,next.block v)) ∧
          next.z=newZ ∧ next.cap=2^g*G.b*A.cap ∧
          next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=nextDegree ∧
          ((∀e,A.z*G.b∣W.graph.width e)→∀e,next.z*G.b∣norm.result.graph.width e) ∧
          ∃ pairs : ℕ, (∑v,(next.records v).length)=(∑u,(A.records u).length)+6*pairs ∧
            2*pairs*(A.z*G.b)≤W.liveWidth := by
  obtain ⟨norm,next,⟨tape,pair,receipt,identifiers⟩,remaining⟩ :=
    A.scanned_geometry_named_rows hε digits hn ag gk newZ hz₁ grain histCost oldLedger rootLedger
      oldOrder groupID nextGroup vertex c
  exact ⟨norm,next,⟨tape,receipt.toIssued,identifiers⟩,remaining⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
