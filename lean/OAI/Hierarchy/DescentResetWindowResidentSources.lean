import OAI.Hierarchy.DescentResetHeaderOrder

namespace OAI
/-! # At most four source classes at a post-reset receiver -/

noncomputable section
set_option quotPrecheck false

namespace Hierarchy.DescentResetWindowResidentSources
open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentCableDonorNames
open scoped Classical
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  [Fintype E] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
  (C : Blocks (Stage.source A native) E)
local notation "Host" => Stage.Host J V k

def sources (h : Host) := insert h (Stage.near A h)

theorem sources_room (h : Host) : (sources A h).card≤A.degree+1 :=
  (Finset.card_insert_le h (Stage.near A h)).trans (Nat.add_le_add_right (Stage.near_room A h) 1)

/-- Changing a host at one receiver preserves both its group and its block. -/
def hostAt (h : Host) : V↪Host := (DescentHostDirectory.liftSite h.1.1).trans (Stage.putAt h.2)

theorem sources_as_map (h : Host) :
    sources A h=(insert h.1.2 (A.near h.1.2)).map (hostAt h) := by
  obtain ⟨⟨g,v⟩,q⟩:=h
  simp only [sources,Stage.near,DescentHostDirectory.groupedNear,hostAt,Finset.map_map,Finset.map_insert]
  rfl

omit [Fintype E] in
theorem source_mem (h : Host) (x : Local C h) : C.src x.val∈sources A h := by
  rcases x.property.2 with source|target
  · exact Finset.mem_insert.mpr (.inl source)
  · let j : Fin (C.count x.val):=⟨0,x.property.1⟩
    have connected:=(Stage.connected A native (C.order ⟨x.val,j⟩)).2
    rw [C.atSource,C.atTarget,target] at connected
    exact Finset.mem_insert.mpr (.inr connected)

omit [Fintype E] in
theorem source_at (h : Host) (x : Local C h) : hostAt h (C.src x.val).1.2=C.src x.val := by
  have member:=source_mem A native C h x
  rw [sources_as_map A] at member
  obtain ⟨u,_,eqn⟩:=Finset.mem_map.mp member
  rw [←eqn]
  rfl

/-- The prior source number restricted to the receiver's true neighbor list
with the receiver itself included. Multiple signed wires can share a source. -/
def number (prior : Host→ℕ) (h : Host) (x : Local C h) : Fin (A.degree+1) :=
  let small:=(sources A h).filter (fun v=>prior v<prior (C.src x.val))
  ⟨small.card,by
    apply lt_of_lt_of_le _ (sources_room A h)
    apply Finset.card_lt_card
    have subset : small⊆sources A h:=Finset.filter_subset _ _
    exact (Finset.ssubset_iff_of_subset subset).2 ⟨C.src x.val,source_mem A native C h x,by simp [small]⟩⟩

omit [Fintype E] in
theorem number_lt (prior : Host→ℕ) (h : Host) (x y : Local C h) :
    number A native C prior h x<number A native C prior h y ↔ prior (C.src x.val)<prior (C.src y.val) := by
  let before:=(fun j=>(sources A h).filter (fun v=>prior v<j))
  have strict {a b : Local C h} (ltKey : prior (C.src a.val)<prior (C.src b.val)) :
      (before (prior (C.src a.val))).card<(before (prior (C.src b.val))).card := by
    apply Finset.card_lt_card
    have subset : before (prior (C.src a.val)) ⊆ before (prior (C.src b.val)) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.trans ltKey⟩
    apply (Finset.ssubset_iff_of_subset subset).2
    exact ⟨C.src a.val,Finset.mem_filter.mpr ⟨source_mem A native C h a,ltKey⟩,by simp [before]⟩
  change (before (prior (C.src x.val))).card<(before (prior (C.src y.val))).card ↔ _
  refine ⟨?_,strict⟩
  intro earlier
  rcases lt_trichotomy (prior (C.src x.val)) (prior (C.src y.val)) with lt|eqn|gt
  · exact lt
  · rw [eqn] at earlier
    exact (lt_irrefl _ earlier).elim
  · exact False.elim ((strict gt).not_gt earlier)

omit [Fintype E] in
theorem number_read (prior : Host→ℕ) (h : Host) (x : Local C h) :
    (number A native C prior h x).val=((sources A h).filter (fun v=>prior v<prior (C.src x.val))).card := rfl

omit [Fintype E] in
theorem number_eq (prior : Host→ℕ) (h : Host) (x y : Local C h) :
    number A native C prior h x=number A native C prior h y ↔ prior (C.src x.val)=prior (C.src y.val) := by
  have left:=number_lt A native C prior h x y
  have right:=number_lt A native C prior h y x
  constructor
  · intro eqn
    exact le_antisymm (le_of_not_gt (fun gt=>((right.mpr gt).ne eqn.symm)))
      (le_of_not_gt (fun lt=>((left.mpr lt).ne eqn)))
  · intro eqn
    exact le_antisymm (le_of_not_gt (fun gt=>(right.mp gt).ne eqn.symm))
      (le_of_not_gt (fun lt=>(left.mp lt).ne eqn))

end Hierarchy.DescentResetWindowResidentSources

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentResetWindowResidentSources
open DescentParallelBase
open scoped Classical
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "rank" => ((Z).rawHostRank T vertex).trans Fin.valEmbedding
local notation "grp" => S.groupCount (i+1)
local notation "groups" => groupRank (Fin.valEmbedding (n:=grp)) rank
local notation "rawSite" => B.raw.siteFrom groups B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin grp) B.next.V k

/-- The source ordinal extends the group/host code with the final block.
It agrees with the actual naming program on every installed source. -/
def hostKey (v : Host) := groups v.1*2^k+v.2.val
local notation "key" => hostKey B

theorem sourceKey (e : (coarse).graph.Edge) : key ((C₀).src e)=rawSite ((coarse).graph.src e) := by
  let v:=(coarse).graph.src e
  change groups (B.raw.pos ((hop).symm (hop v)))*2^k+(B.raw.block ((hop).symm (hop v))).val=
    groups (B.raw.pos v)*2^k+(B.raw.block v).val
  exact congrArg (fun t => groups (B.raw.pos t)*2^k+(B.raw.block t).val) ((hop).symm_apply_apply v)

def sourceClass (v : Host) (x : Local C₀ v) : Fin ((A).degree+1) := number A ord C₀ key v x

theorem sourceClass_lt (v : Host) (x y : Local C₀ v) :
    sourceClass B v x<sourceClass B v y ↔
      rawSite ((coarse).graph.src x.val)<rawSite ((coarse).graph.src y.val) := by
  simpa only [sourceClass,sourceKey B] using number_lt A ord C₀ key v x y

theorem sourceClass_eq (v : Host) (x y : Local C₀ v) :
    sourceClass B v x=sourceClass B v y ↔
      rawSite ((coarse).graph.src x.val)=rawSite ((coarse).graph.src y.val) := by
  simpa only [sourceClass,sourceKey B] using number_eq A ord C₀ key v x y

/-- At most four comparisons of the source header with the actual receiver
and its neighbors compute the whole source digit. -/
theorem sourceClass_read (v : Host) (x : Local C₀ v) :
    (sourceClass B v x).val =
      ((insert v (Stage.near A v)).filter (fun t=>key t<rawSite ((coarse).graph.src x.val))).card := by
  simpa only [sourceClass,sourceKey B,sources] using number_read A ord C₀ key v x

private theorem filter_eq_of_iff {α : Type} (s : Finset α) {p q : α → Prop}
    {dp : DecidablePred p} {dq : DecidablePred q} (same : ∀ u,p u ↔ q u) :
    @Finset.filter α p dp s = @Finset.filter α q dq s := by
  let _ := dp
  let _ := dq
  ext a
  exact Finset.mem_filter.trans ((and_congr Iff.rfl (same a)).trans Finset.mem_filter.symm)

/-- A receiver uses just one host table for every group and low block.
Each candidate has those same two digits, so raw host ordinal alone orders
the receiver and its neighbors. -/
theorem sourceClass_host (v : Host) (x : Local C₀ v) :
    (sourceClass B v x).val =
      ((insert v.1.2 ((A).near v.1.2)).filter (fun u=>rank u<rank ((C₀).src x.val).1.2)).card := by
  let src:=(C₀).src x.val
  have atSrc : hostAt v src.1.2=src:=source_at A ord C₀ v x
  have same (u : B.next.V) : key (hostAt v u)<key src ↔ rank u<rank src.1.2 := by
    calc
      key (hostAt v u)<key src ↔ key (hostAt v u)<key (hostAt v src.1.2) := by rw [atSrc]
      _ ↔ _ := by
        change (v.1.1.val*pitch rank+rank u)*2^k+v.2.val <
          (v.1.1.val*pitch rank+rank src.1.2)*2^k+v.2.val ↔ _
        rw [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos _),Nat.add_lt_add_iff_left]
  change ((sources A v).filter (fun t=>key t<key src)).card=_
  rw [sources_as_map A,Finset.filter_map,Finset.card_map]
  apply congrArg Finset.card
  exact filter_eq_of_iff _ same

theorem sourceClass_four (v : Host) (x : Local C₀ v) : (sourceClass B v x).val<4 := by
  have limit := (sourceClass B v x).isLt
  exact limit.trans_le (Nat.succ_le_succ B.next.branch.le)

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
