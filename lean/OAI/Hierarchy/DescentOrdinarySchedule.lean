import OAI.Hierarchy.DescentOrdinaryRateData
import OAI.Hierarchy.DescentCollectedPhase
import OAI.Hierarchy.DescentFullHostOrdinal
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentFixedMenu
import OAI.Hierarchy.DescentSiteNameRead
import OAI.Hierarchy.DescentScheduleGrains

namespace OAI
/-! # Iterating the actual paid ordinary branches within one epoch -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {k f : ℕ}

variable (G : PoweredGadget F) (S : AtomSchedule) {phase start : ℕ}

variable (ctl : OrdinaryRates G S k f) (he : 0≤ε)
  (priceEq : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)

include ctl priceEq

/-- Construct the real subround data, including the normalization specific
to every chosen assignment of the six-party terms. -/
theorem ordinary_level_joint (H : Histories F d P bits) {age j : ℕ} (hj : j<S.rounds) (hi : age<S.length)
    {z z' wire hist : ℕ} (grain : z=z'*G.b) (histFits : 6*hist≤wire*(z*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k age z (atRound j) wire hist) :
    ∃a : SubroundInput H G (u:=q*wire) he, ∃order inputOrder : DescentTerminalEpochDecoder.OrdersAt G he a, SubroundInput.Grain z a ∧ ∀c : (H.extend he a).Choice,
      ∃next : Reached ((H.extend he a).state c) G q ε S k (age+1) z' (atRound (j+1)) wire hist,
        ∃ticket : Chronology.OrdinaryLink (source c.1) he (a.placement c.1) c.2 (a.reblock c.1 c.2) next,
          ticket.pair=order c.1 ∧ ticket.inputPair=inputOrder c.1 := by
  let W (c : H.Choice) := H.state c
  let Next (c : H.Choice) (o : MarkedWorld F d P bits) :=
    Reached o G q ε S k (age+1) z' (atRound (j+1)) wire hist
  let Step (c : H.Choice) (u : ℝ) :=
    Σ st : StageInput (W c) G u ε,PLift (st.z=z) ×
      (Σorders : DescentStageEdgeReceipt.ScanNumbers he st × DescentStageEdgeReceipt.ScanNumbers he st, ∀p : (st.result he).Choice,Σn : Normalize ((st.result he).state p),Σv : Next c n.result,
        PLift (Normalize.CutsEqual z n) × {ticket : Chronology.OrdinaryLink (source c) he st p n v //ticket.pair=orders.1 ∧ ticket.inputPair=orders.2})
  have issue (c : H.Choice) : Nonempty (Step c (q*wire)) := by
    let cap:=source c
    let A:=cap.placement
    have old := cap.valid
    have wireEq : A.wire=wire := cap.edges
    rw [←wireEq]
    let J₁:=Fin (S.groupCount (age+1))
    let digits := S.groupDigits hi ctl.radix
    have next (p : (A.stage.result he).Choice) :=
      A.next_state_particles S age f old he priceEq ctl.height hi ctl.radix ctl.adr
        (Fintype.card_fin (S.groupCount age)).le (show Fintype.card J₁=S.groupCount (age+1) from Fintype.card_fin _) digits
        (by simpa [A,cap.branch] using ctl.host j hj)
        (by simpa [A,cap.branch] using ctl.gain j hj)
        (by simpa [A,cap.branch] using ctl.fineGain j hj) cap.order Fin.valEmbedding Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding)
        (by simpa [A,cap.branch,atRound,ordinaryDegree] using ctl.cut j hj)
        (by simpa [A,cap.branch] using ctl.room j hj) (cap.grain.trans grain)
        (by simpa [A,cap.edges,cap.atoms,cap.grain] using histFits) p
    let rank := DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount age)) (cap.vertex.trans Fin.valEmbedding)
    refine ⟨⟨A.stage,⟨cap.grain⟩,⟨DescentStageEdgeReceipt.nativeNumbers he A.stage rank,Chronology.inputNumbers he cap⟩,fun p=>?_⟩⟩
    apply Classical.choice
    obtain ⟨n,A',⟨particles,hubRows,venueRows,hubFlags,nearRows,sourceSorted,oneName⟩,⟨tape,pair,issued,edgeName⟩,cuts,named,validated,zEq,capEq,words,atoms,degree⟩ := next p
    constructor
    refine ⟨n,⟨_,A',validated,zEq,words.trans cap.edges,atoms.trans cap.atoms,?_,tape.selector,DescentRosterOrder.compact ((DescentHostDirectory.packedEmbedding cap.vertex
          (Function.Embedding.subtype _) (fun v=>v.2)).trans Fin.valEmbedding),fun _=>edgeName,
        fun _=>A'.siteNamed_read _ validated.coordinates named⟩,⟨by simpa only [←cap.grain] using cuts⟩,⟨⟨rfl,HEq.rfl,rfl,(fun _=>rfl),(fun _=>HEq.rfl),rfl,grain,tape,pair,Chronology.inputNumbers he cap,HEq.rfl,issued,particles,rfl,cuts,(by simpa only [A,cap.branch] using capEq),⟨hi,ctl.radix,Function.Embedding.subtype _,hubRows⟩,
          ⟨hi,ctl.radix,Function.Embedding.subtype _,hubRows,(fun v=>DescentHostDirectory.compact_fullHost cap.vertex v),(fun v=>v.property),hubFlags⟩,
          ⟨hi,ctl.radix,Function.Embedding.subtype _,venueRows,(fun v=>DescentHostDirectory.compact_fullHost cap.vertex v)⟩,sourceSorted.expose tape.selector edgeName,DescentHostDirectory.card_fullHost cap.vertex,⟨j,hj,rfl⟩,oneName,
          ⟨Equiv.refl _,(fun v=>DescentHostDirectory.compact_fullHost cap.vertex v),fun u v=>by
            simp only [nearRows,Equiv.refl_apply]
            exact Iff.rfl⟩,rfl⟩,issued.numbers_eq rank HEq.rfl,rfl⟩⟩
    simpa [A,cap.branch,atRound,ordinaryDegree] using degree
  let step (c : H.Choice) : Step c (q*wire) := (issue c).some
  refine ⟨⟨fun c=>(step c).1,fun c p=>((step c).2.2.2 p).1⟩,fun c=>(step c).2.2.1.1,fun c=>(step c).2.2.1.2,
    ⟨fun c=>(step c).2.1.down,fun c p=>((step c).2.2.2 p).2.2.1.down⟩,?_⟩
  intro c
  let row:=((step c.1).2.2.2 c.2)
  exact ⟨row.2.1,row.2.2.2.val,row.2.2.2.property⟩

theorem ordinary_level_orders (H : Histories F d P bits) {age j : ℕ} (hj : j<S.rounds) (hi : age<S.length)
    {z z' wire hist : ℕ} (grain : z=z'*G.b) (histFits : 6*hist≤wire*(z*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k age z (atRound j) wire hist) :
    ∃a : SubroundInput H G (u:=q*wire) he, ∃order : DescentTerminalEpochDecoder.OrdersAt G he a, SubroundInput.Grain z a ∧ ∀c : (H.extend he a).Choice,
      ∃next : Reached ((H.extend he a).state c) G q ε S k (age+1) z' (atRound (j+1)) wire hist,
        ∃ticket : Chronology.OrdinaryLink (source c.1) he (a.placement c.1) c.2 (a.reblock c.1 c.2) next,
          ticket.pair=order c.1 := by
  obtain ⟨a,order,inputOrder,cuts,run⟩:=ordinary_level_joint G S ctl he priceEq H hj hi grain histFits source
  refine ⟨a,order,cuts,fun c=>?_⟩
  obtain ⟨target,ticket,structural,_⟩:=run c
  exact ⟨target,ticket,structural⟩

theorem ordinary_level_links (H : Histories F d P bits) {age j : ℕ} (hj : j<S.rounds) (hi : age<S.length)
    {z z' wire hist : ℕ} (grain : z=z'*G.b) (histFits : 6*hist≤wire*(z*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k age z (atRound j) wire hist) :
    ∃a : SubroundInput H G (u:=q*wire) he, SubroundInput.Grain z a ∧ ∀c : (H.extend he a).Choice,
      ∃next : Reached ((H.extend he a).state c) G q ε S k (age+1) z' (atRound (j+1)) wire hist,
        Nonempty (Chronology.OrdinaryLink (source c.1) he (a.placement c.1) c.2 (a.reblock c.1 c.2) next) := by
  obtain ⟨a,order,cuts,run⟩ := ordinary_level_orders G S ctl he priceEq H hj hi grain histFits source
  refine ⟨a,cuts,fun c=>?_⟩
  obtain ⟨target,ticket,_⟩ := run c
  exact ⟨target,⟨ticket⟩⟩

theorem ordinary_level (H : Histories F d P bits) {age j : ℕ} (hj : j<S.rounds) (hi : age<S.length)
    {z z' wire hist : ℕ} (grain : z=z'*G.b) (histFits : 6*hist≤wire*(z*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k age z (atRound j) wire hist) :
    ∃a : SubroundInput H G (u:=q*wire) he, SubroundInput.Grain z a ∧ ∀c,Nonempty
      (Reached ((H.extend he a).state c) G q ε S k (age+1) z' (atRound (j+1)) wire hist) := by
  obtain ⟨a,cuts,links⟩ := ordinary_level_links G S ctl he priceEq H hj hi grain histFits source
  exact ⟨a,cuts,fun c=>⟨(links c).choose⟩⟩

/-- The control data for each subround consists only of fixed numeric
bounds. The proof builds and retains the concrete successor on every limb. -/
theorem ordinary_block_joint (H : Histories F d P bits) {start j count : ℕ}
    (limit : j+count≤S.rounds) (age : start+count≤S.length)
    (z : ℕ→ℕ) (wire hist : ℕ)
    (grain : ∀u<count,z u=z (u+1)*G.b)
    (historyFit : ∀u<count,6*hist≤wire*(z u*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k start (z 0) (atRound j) wire hist) :
    ∃v : Schedule G he (u:=q*wire) count H, ∃order inputOrder : DescentTerminalEpochDecoder.ScheduleOrders G he v, Schedule.Grains z v ∧ ∀c,
      ∃target : Reached ((Schedule.finish G he v).state c) G q ε S k (start+count) (z count) (atRound (j+count)) wire hist,
        ∃path : Chronology.Path (source (Chronology.sourceChoice he v c)) target,
          path.ranked=Chronology.rankedSchedule he v order c ∧ path.inputRanked=Chronology.rankedSchedule he v inputOrder c ∧ path.capFactors=ordinaryCapFactors G.b j count ∧ path.selections=Chronology.scheduled he v c ∧ path.ordinaryOnly ∧ (∀p,path.whole p) ∧
            ∀p R,(∀i<count,p∣z i)→path.aligned p R := by
  induction count generalizing H start j z with
  | zero=>
    exact ⟨PUnit.unit,PUnit.unit,PUnit.unit,trivial,fun c=>⟨source c,.here,rfl,rfl,rfl,rfl,trivial,(fun _=>trivial),fun _ _ _=>trivial⟩⟩
  | succ n ih=>
    obtain ⟨stage,order,inputOrder,cuts,link⟩ := ordinary_level_joint G S ctl he priceEq H (by omega : j<S.rounds)
      (by omega : start<S.length) (grain 0 (by omega)) (historyFit 0 (by omega)) source
    let mid (c : (H.extend he stage).Choice) := (link c).choose
    obtain ⟨rest,orders,inputOrders,aligned,done⟩ := ih (H.extend he stage) (start:=start+1) (j:=j+1)
      (by omega) (by omega) (fun i=>z (i+1))
      (fun i h=>grain _ (by omega)) (fun i h=>historyFit _ (by omega)) mid
    refine ⟨⟨stage,rest⟩,⟨order,orders⟩,⟨inputOrder,inputOrders⟩,⟨cuts,aligned⟩,?_⟩
    intro c
    let branch := Chronology.sourceChoice he rest c
    let ticket := (link branch).choose_spec.choose
    have shared : ticket.pair=order branch.1 := (link branch).choose_spec.choose_spec.1
    have inputShared : ticket.inputPair=inputOrder branch.1 := (link branch).choose_spec.choose_spec.2
    let prefixPath : Chronology.Path (source branch.1) (mid branch) := .ordinary .here ticket
    obtain ⟨target,trail,ranked,inputRanked,factors,records,only,whole,alignedTail⟩ := done c
    let claim (age round : ℕ) : Prop := ∃v : Reached ((Schedule.finish G he rest).state c) G q ε S k age
        (z (n+1)) (atRound round) wire hist,
        ∃path : Chronology.Path (source branch.1) v,
          path.ranked=⟨ticket.selection,order branch.1⟩::Chronology.rankedSchedule he rest orders c ∧
          path.inputRanked=⟨ticket.selection,inputOrder branch.1⟩::Chronology.rankedSchedule he rest inputOrders c ∧
          path.capFactors=ordinaryCapFactors G.b j (n+1) ∧
          path.selections=ticket.selection::Chronology.scheduled he rest c ∧ path.ordinaryOnly ∧ (∀p,path.whole p) ∧
            ∀p R,(∀i<n+1,p∣z i)→path.aligned p R
    have result : claim ((start+1)+n) ((j+1)+n) := by
      refine ⟨target,prefixPath.append trail,?_,?_,?_,?_,Chronology.Path.ordinaryOnly_append prefixPath trail trivial only,?_,?_⟩
      · rw [Chronology.Path.ranked_append,ranked]
        exact congrArg (fun pair : DescentStageEdgeReceipt.ScanNumbers he (stage.placement branch.1) =>
          (⟨ticket.selection,pair⟩ : Chronology.RankedSelection F P d bits G ε) ::
            Chronology.rankedSchedule he rest orders c) shared
      · rw [Chronology.Path.inputRanked_append,inputRanked]
        exact congrArg (fun pair : DescentStageEdgeReceipt.ScanNumbers he (stage.placement branch.1) =>
          (⟨ticket.selection,pair⟩ : Chronology.RankedSelection F P d bits G ε) ::
            Chronology.rankedSchedule he rest inputOrders c) inputShared
      · rw [Chronology.Path.capFactors_append,factors]
        rfl
      · rw [Chronology.Path.selections_append,records]
        rfl
      · exact fun p=>Chronology.Path.whole_append p prefixPath trail trivial (whole p)
      · intro p R all
        apply Chronology.Path.aligned_append p R
        · refine ⟨trivial,?_⟩
          change p∣(stage.placement branch.1).z
          rw [cuts.1 branch.1]
          exact all 0 (by omega)
        · exact alignedTail p R (fun i h=>all _ (by omega))
    have ageShift : (start+1)+n = start+(n+1) := by omega
    have roundShift : (j+1)+n = j+(n+1) := by omega
    exact (congrArg₂ claim ageShift roundShift).mp result

theorem ordinary_block_orders (H : Histories F d P bits) {start j count : ℕ}
    (limit : j+count≤S.rounds) (age : start+count≤S.length)
    (z : ℕ→ℕ) (wire hist : ℕ)
    (grain : ∀u<count,z u=z (u+1)*G.b)
    (historyFit : ∀u<count,6*hist≤wire*(z u*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k start (z 0) (atRound j) wire hist) :
    ∃v : Schedule G he (u:=q*wire) count H, ∃order : DescentTerminalEpochDecoder.ScheduleOrders G he v, Schedule.Grains z v ∧ ∀c,
      ∃target : Reached ((Schedule.finish G he v).state c) G q ε S k (start+count) (z count) (atRound (j+count)) wire hist,
        ∃path : Chronology.Path (source (Chronology.sourceChoice he v c)) target,
          path.ranked=Chronology.rankedSchedule he v order c ∧ path.selections=Chronology.scheduled he v c ∧ path.ordinaryOnly ∧ (∀p,path.whole p) ∧
            ∀p R,(∀i<count,p∣z i)→path.aligned p R := by
  obtain ⟨v,order,inputOrder,grains,run⟩:=ordinary_block_joint G S ctl he priceEq H limit age z wire hist grain historyFit source
  refine ⟨v,order,grains,fun c=>?_⟩
  obtain ⟨target,path,ranked,_,_,facts⟩:=run c
  exact ⟨target,path,ranked,facts⟩

theorem ordinary_block_links (H : Histories F d P bits) {start j count : ℕ}
    (limit : j+count≤S.rounds) (age : start+count≤S.length)
    (z : ℕ→ℕ) (wire hist : ℕ)
    (grain : ∀u<count,z u=z (u+1)*G.b)
    (historyFit : ∀u<count,6*hist≤wire*(z u*G.b))
    (source : ∀c,Reached (H.state c) G q ε S k start (z 0) (atRound j) wire hist) :
    ∃v : Schedule G he (u:=q*wire) count H, Schedule.Grains z v ∧ ∀c,
      ∃target : Reached ((Schedule.finish G he v).state c) G q ε S k (start+count) (z count) (atRound (j+count)) wire hist,
        ∃path : Chronology.Path (source (Chronology.sourceChoice he v c)) target,
          path.selections=Chronology.scheduled he v c ∧ path.ordinaryOnly ∧ (∀p,path.whole p) ∧
            ∀p R,(∀i<count,p∣z i)→path.aligned p R := by
  obtain ⟨v,order,aligned,run⟩ := ordinary_block_orders G S ctl he priceEq H limit age z wire hist grain historyFit source
  refine ⟨v,aligned,fun c=>?_⟩
  obtain ⟨target,path,_,facts⟩ := run c
  exact ⟨target,path,facts⟩

theorem ordinary_block (H : Histories F d P bits) {start j count : ℕ}
    (limit : j+count≤S.rounds) (age : start+count≤S.length)
    (z : ℕ→ℕ) (wire hist : ℕ)
    (grain : ∀u<count,z u=z (u+1)*G.b)
    (historyFit : ∀u<count,6*hist≤wire*(z u*G.b))
    (old : ∀c,Nonempty (Reached (H.state c) G q ε S k start (z 0) (atRound j) wire hist)) :
    ∃v : Schedule G he (u:=q*wire) count H,Schedule.Grains z v ∧ ∀c,Nonempty (Reached ((Schedule.finish G he v).state c)
      G q ε S k (start+count) (z count) (atRound (j+count)) wire hist) := by
  obtain ⟨v,aligned,run⟩ := ordinary_block_links G S ctl he priceEq H limit age z wire hist grain historyFit
    (fun c=>(old c).some)
  exact ⟨v,aligned,fun c=>⟨(run c).choose⟩⟩

end
end Hierarchy.DescentSixParty

end OAI
