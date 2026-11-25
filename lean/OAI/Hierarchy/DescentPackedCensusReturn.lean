import OAI.Hierarchy.DescentPackedCensusTables
import OAI.Hierarchy.DescentPackedPhaseIssued
import OAI.Hierarchy.DescentPackedCensusPhaseWidth
import OAI.Hierarchy.DescentPackedCensusInvoice

namespace OAI
/-! # From the packed predecessor cable records to native matching names and paint -/

namespace Hierarchy.DescentSixParty.GroupStage
open PackedCensus DescentCompiler DescentPackedColony DescentColonies DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C L k ℓ Δ d b w hBits quota age : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
local notation "fee" => A.wire*(A.z*G.b)
local notation "D" => DescentHostDegree.gap A.degree
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v : W.graph.Site => Finset.card (Finset.filter (fun edge => W.graph.src edge = v) W.core)
local notation "wt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev full g))
local notation "amt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev outgoing g))
local notation "grain" => Phase.recordWidth k b quota
local notation "M" => lanes hBits grain
local notation "used" => Phase.usedBits k b quota hBits

def plane (ev : V≃Fin L) (h : L≤2^ℓ) : V↪Fin (2^ℓ) := ev.toEmbedding.trans (Fin.castLEEmb h)

private theorem census_plane (t : Bool) (v : Fin (2^ℓ)) (g : Fin C) (x : Block k) :
    A.censusValue (plane ev h) ej t v g x=if t then amt g v x else wt g v x := by
  by_cases loc : v.val<L
  · let old:=ev.symm ⟨v.val,loc⟩
    have root : plane ev h old=v := Fin.ext (by simp [plane,old])
    have hit : ∃u,plane ev h u=v := ⟨old,root⟩
    have name : hit.choose=old := (plane ev h).injective (hit.choose_spec.trans root.symm)
    cases t <;> simp only [censusValue,dite_eq_left hit,name,Bool.false_eq_true,↓reduceIte,
      Padded.table,dite_eq_left loc,groupedCounts] <;> rfl
  · have miss : ¬∃u,plane ev h u=v := by
      rintro ⟨u,same⟩
      have id:=congrArg Fin.val same
      change (ev u).val=v.val at id
      exact loc (id ▸ (ev u).isLt)
    cases t <;> simp only [censusValue,dite_eq_right miss,Padded.table,dite_eq_right loc,Bool.false_eq_true,↓reduceIte]

theorem packed_census_return_at_unit (shared : ℕ) (covered : Phase.recordWidth k b quota ≤ shared) (sched : AtomSchedule) (ready : A.StateBounds sched age) (he : 0≤ε)
    (chart : Frame.Chart) (marked : Bank) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (layout : Phase.Arena.Room chart marked Δ k b (2*Phase.unit k b*lanes hBits shared) w (2^ℓ) C)
    (K : ℕ) (wide : 2*shared≤hBits) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (slots : A.PortOrder quota) (first second : Banks) (m : Memory w)
    (fit1 : DescentSIMDLookup.Fits first ((1+b+2*quota)*2^k) (b*2^k) (lanes hBits shared) (2^ℓ) C w chart.weights.base)
    (fit2 : DescentSIMDLookup.Fits second ((1+b+2*quota)*2^k) (b*2^k) (lanes hBits shared) (2^ℓ) C w chart.weights.base)
    (fit3 : DescentSIMDLookup.Fits second ((1+b+2*quota)*2^k) (b*2^k) (lanes hBits shared) (2^ℓ) C w marked.base)
    (apart : chart.weights.base+2^ℓ*chunks C (lanes hBits shared)≤ marked.base)
    (before : chart.roster.base+chart.roster.size≤chart.weights.base)
    (mounted : (Phase.Arena.image chart A.fieldBits Δ (2^ℓ) C b (2*Phase.unit k b*lanes hBits shared) D cap).Resident m)
    (topology : ∀v i,m (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (original : ∀fl : Bool,PinFrame («M» := lanes hBits shared) (if fl then second else first)
      (PackedCensus.lookup fl b quota k A.wire 256 (A.z*G.b) A.hist) (A.rawCensus (plane ev h) ej slots b) m) :
    let S:=Phase.Arena.shelves chart marked Δ k b (2*Phase.unit k b*lanes hBits shared)
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<(lanes hBits shared),
      ((PackedCensus.histograms first second chart.weights.base marked.base (2^ℓ) C (lanes hBits shared) w).seq (Phase.program S w (2^ℓ) C (lanes hBits shared))).Exec
        m out (PackedCensus.clocks first second (2^ℓ) C (lanes hBits shared)+Phase.cost S w (2^ℓ) C (lanes hBits shared)) ∧
      (PackedCensus.clocks first second (2^ℓ) C (lanes hBits shared)+Phase.cost S w (2^ℓ) C (lanes hBits shared))*w≤K*((96+Phase.factor k Δ)*(hBits+2^ℓ*hBits+4*2^ℓ*C*shared)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<chart.weights.base,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C (lanes hBits shared))≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs (lanes hBits shared) S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C (lanes hBits shared)) (A.block u)+(row (2^ℓ) C (lanes hBits shared) (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat := by
  let S:=Phase.Arena.shelves chart marked Δ k b (2*Phase.unit k b*lanes hBits shared)
  obtain ⟨mid,prepare,rows,low,high⟩:=A.packed_census_frames sched (plane ev h) ej slots ready first second
    chart.weights.base marked.base fit1 fit2 fit3 apart m original
  have matchLanes:=(show lanes (2*Phase.unit k b*lanes hBits shared) (Phase.unit k b)=lanes hBits shared from Nat.mul_div_cancel_left _ (by dsimp [Phase.unit];omega))
  have countSpan : marked.base+2^ℓ*chunks C (lanes hBits shared)≤chart.origin :=
    (Nat.add_le_add_left (matchLanes ▸ layout.rows) _).trans layout.counts.2.2
  have t (g : Bool) (p : Row (2^ℓ) C (lanes hBits shared)) := rows g p
  simp only [census_plane A ej ev h] at t
  have weights : Reads chart.weights (fun v g=>counts b (wt g v)) (lanes hBits shared) mid := by
    intro p
    simpa only [Bool.false_eq_true,↓reduceIte,counts] using t false p
  have raw : Reads marked (fun v g=>counts b (amt g v)) (lanes hBits shared) mid := by
    intro p
    simpa only [↓reduceIte,counts] using t true p
  have lifted := Phase.Arena.Image.Resident.afterEarlier _ mounted
    (marked.base + 2^ℓ * chunks C (lanes hBits shared)) countSpan high
  have top (v : Fin (2^ℓ)) (i : Fin Δ) : mid (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w) := by
    let n : Fin (2^k-1):=⟨0,by have:=Nat.one_lt_pow A.fieldBits.ne' (by decide : 1<2);omega⟩
    have fit : 2^ℓ*Δ≤chart.roster.size := (layout.charts n).topSize
    have ord:=Nat.mul_le_mul_right Δ v.isLt
    rw [Nat.succ_mul] at ord
    exact (low _ (by have:=i.isLt;omega)).trans (topology v i)
  have Wfit : w≤w*(2*Phase.unit k b*lanes hBits shared) := Nat.le_mul_of_pos_right _ ((show 0<2*Phase.unit k b by dsimp [Phase.unit];omega).trans_le layout.wide)
  have reached:=A.run_packed_chart ej ev h he chart marked rs members layout w Wfit short leaves budget mid lifted top
    (matchLanes.symm ▸ weights) (matchLanes.symm ▸ raw)
  dsimp only at reached
  rw [matchLanes] at reached
  obtain ⟨out,i,j,hm,run,_,auth,word1,word2,prev,future,muEq,paintEq,packedFields,cell⟩:=reached
  have firstBound : chart.origin ≤ S.first :=
    (show chart.origin ≤ Phase.Arena.menu chart Δ k from Nat.le_add_right ..).trans
      ((show Phase.Arena.menu chart Δ k ≤ Phase.Arena.names chart Δ k (2*Phase.unit k b*lanes hBits shared)
        from Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have lower : chart.weights.base ≤ S.first :=
    ((Nat.le_add_right ..).trans layout.weights).trans firstBound
  have upper : S.first ≤ S.output := by
    change Phase.Arena.first chart Δ k b (2*Phase.unit k b*lanes hBits shared) ≤
      Phase.Arena.endAt chart Δ k b (2*Phase.unit k b*lanes hBits shared)
    unfold Phase.Arena.endAt Phase.Arena.colorWork Phase.Arena.selected Phase.Arena.seedWork
    repeat first | exact Nat.le_refl _ | apply Nat.le_add_right_of_le
  refine ⟨out,i,j,hm,?_,Phase.census_phase_bill_at_unit k hBits w K Δ (2^ℓ) C shared S first second ((show 0<Phase.unit k b by dsimp [Phase.unit];omega).trans_le ((le_max_left ..).trans covered)) wide hardware,
    auth,word1,word2,fun z lz=>(prev z (lz.trans_le lower)).trans (low z lz),
    fun z hz => (future z hz).trans (high z
      (((countSpan.trans firstBound).trans upper).trans ((Nat.le_add_right ..).trans hz))),muEq,paintEq,packedFields,cell⟩
  exact @Procedure.Exec.then w
    (PackedCensus.histograms first second chart.weights.base marked.base (2^ℓ) C (lanes hBits shared) w)
    (Phase.program S w (2^ℓ) C (lanes hBits shared)) m mid out _ _ prepare run

theorem packed_resident_census_return_at_unit (shared : ℕ) (covered : Phase.recordWidth k b quota ≤ shared) (sched : AtomSchedule) (ready : A.StateBounds sched age) (he : 0≤ε)
    (chart : Frame.Chart) (marked : Bank) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (layout : Phase.Arena.Room chart marked Δ k b (2*Phase.unit k b*lanes hBits shared) w (2^ℓ) C)
    (K : ℕ) (wide : 2*shared≤hBits) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (slots : A.PortOrder quota) (source : Bank) (origin : ℕ) (m : Memory w)
    (original : Reads source (A.rawCensus (plane ev h) ej slots b) (lanes hBits shared) m)
    (sourceFit : source.Fits w chart.weights.base) (nsource : 2^ℓ*chunks C (lanes hBits shared) ≤ source.size)
    (rom : (Phase.CensusTables.image origin ((1+b+2*quota)*2^k) (b*2^k) (lanes hBits shared) (2^ℓ) C
      (fun fl=>PackedCensus.lookup fl b quota k A.wire 256 (A.z*G.b) A.hist)).Resident m)
    (early : Phase.CensusTables.finish origin ((1+b+2*quota)*2^k) (lanes hBits shared) (2^ℓ) C≤chart.weights.base)
    (addressable : marked.base+2^ℓ*chunks C (lanes hBits shared)<2^w) (fitsWidth : hBits≤w)
    (apart : chart.weights.base+2^ℓ*chunks C (lanes hBits shared)≤ marked.base)
    (before : chart.roster.base+chart.roster.size≤chart.weights.base)
    (mounted : (Phase.Arena.image chart A.fieldBits Δ (2^ℓ) C b (2*Phase.unit k b*lanes hBits shared) D cap).Resident m)
    (topology : ∀v i,m (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    :
    let first:=Phase.CensusTables.banks source origin ((1+b+2*quota)*2^k) (lanes hBits shared) (2^ℓ) C false
    let second:=Phase.CensusTables.banks source origin ((1+b+2*quota)*2^k) (lanes hBits shared) (2^ℓ) C true
    let S:=Phase.Arena.shelves chart marked Δ k b (2*Phase.unit k b*lanes hBits shared)
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<(lanes hBits shared),
      ((PackedCensus.histograms first second chart.weights.base marked.base (2^ℓ) C (lanes hBits shared) w).seq (Phase.program S w (2^ℓ) C (lanes hBits shared))).Exec
        m out (PackedCensus.clocks first second (2^ℓ) C (lanes hBits shared)+Phase.cost S w (2^ℓ) C (lanes hBits shared)) ∧
      (PackedCensus.clocks first second (2^ℓ) C (lanes hBits shared)+Phase.cost S w (2^ℓ) C (lanes hBits shared))*w≤K*((96+Phase.factor k Δ)*(hBits+2^ℓ*hBits+4*2^ℓ*C*shared)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<chart.weights.base,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C (lanes hBits shared))≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs (lanes hBits shared) S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C (lanes hBits shared)) (A.block u)+(row (2^ℓ) C (lanes hBits shared) (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat := by
  let width:=(1+b+2*quota)*2^k
  let f:=fun fl=>PackedCensus.lookup fl b quota k A.wire 256 (A.z*G.b) A.hist
  have live : 0<shared := (show 0<Phase.unit k b by dsimp [Phase.unit];omega).trans_le ((le_max_left ..).trans covered)
  have fitA : max width (b*2^k) ≤ shared :=
    (max_le (le_max_right ..) ((Nat.mul_le_mul_right (2^k) (show b≤1+b+2*quota by omega)).trans (le_max_right ..))).trans covered
  have capM : (lanes hBits shared)*max width (b*2^k)≤w/2 := by
    have floor : (lanes hBits shared)*(2*shared)≤hBits := Nat.div_mul_le_self _ _
    have room:=Nat.mul_le_mul_left (lanes hBits shared) fitA
    rw [Nat.mul_left_comm (lanes hBits shared) 2 shared] at floor
    omega
  have prior : chart.weights.base≤ marked.base := (Nat.le_add_right ..).trans apart
  have nfit : chart.weights.base+2^ℓ*chunks C (lanes hBits shared)<2^w := (Nat.add_le_add_right prior _).trans_lt addressable
  have laterFit : source.Fits w marked.base := ⟨sourceFit.1,sourceFit.2.1,sourceFit.2.2.trans prior⟩
  have hf:=Phase.CensusTables.fits source origin chart.weights.base false sourceFit nsource early nfit capM
  have hg:=Phase.CensusTables.fits source origin chart.weights.base true sourceFit nsource early nfit capM
  have hh:=Phase.CensusTables.fits source origin marked.base true laterFit nsource (early.trans prior) addressable capM
  exact A.packed_census_return_at_unit ej ev h shared covered sched ready he chart marked rs members layout K wide hardware short leaves budget slots _ _ m
    hf hg hh apart before mounted topology (by
      intro side
      cases side
      · exact Phase.CensusTables.frames source origin f _ m rom original false
      · exact Phase.CensusTables.frames source origin f _ m rom original true)

theorem packed_census_return (sched : AtomSchedule) (ready : A.StateBounds sched age) (he : 0≤ε)
    (chart : Frame.Chart) (marked : Bank) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (layout : Phase.Arena.Room chart marked Δ k b used w (2^ℓ) C)
    (K : ℕ) (wide : 2*grain≤hBits) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (slots : A.PortOrder quota) (first second : Banks) (m : Memory w)
    (fit1 : DescentSIMDLookup.Fits first ((1+b+2*quota)*2^k) (b*2^k) M (2^ℓ) C w chart.weights.base)
    (fit2 : DescentSIMDLookup.Fits second ((1+b+2*quota)*2^k) (b*2^k) M (2^ℓ) C w chart.weights.base)
    (fit3 : DescentSIMDLookup.Fits second ((1+b+2*quota)*2^k) (b*2^k) M (2^ℓ) C w marked.base)
    (apart : chart.weights.base+2^ℓ*chunks C M≤ marked.base)
    (before : chart.roster.base+chart.roster.size≤chart.weights.base)
    (mounted : (Phase.Arena.image chart A.fieldBits Δ (2^ℓ) C b used D cap).Resident m)
    (topology : ∀v i,m (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (original : ∀fl : Bool,PinFrame («M» := M) (if fl then second else first)
      (PackedCensus.lookup fl b quota k A.wire 256 (A.z*G.b) A.hist) (A.rawCensus (plane ev h) ej slots b) m) :
    let S:=Phase.Arena.shelves chart marked Δ k b used
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<M,
      ((PackedCensus.histograms first second chart.weights.base marked.base (2^ℓ) C M w).seq (Phase.program S w (2^ℓ) C M)).Exec
        m out (PackedCensus.clocks first second (2^ℓ) C M+Phase.cost S w (2^ℓ) C M) ∧
      (PackedCensus.clocks first second (2^ℓ) C M+Phase.cost S w (2^ℓ) C M)*w≤K*((96+Phase.factor k Δ)*(hBits+2^ℓ*hBits+4*2^ℓ*C*grain)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<chart.weights.base,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C M)≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs M S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C M) (A.block u)+(row (2^ℓ) C M (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat :=
  A.packed_census_return_at_unit ej ev h _ le_rfl sched ready he chart marked rs members layout K wide hardware short leaves budget
    slots first second m fit1 fit2 fit3 apart before mounted topology original

theorem packed_resident_census_return (sched : AtomSchedule) (ready : A.StateBounds sched age) (he : 0≤ε)
    (chart : Frame.Chart) (marked : Bank) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (layout : Phase.Arena.Room chart marked Δ k b used w (2^ℓ) C)
    (K : ℕ) (wide : 2*grain≤hBits) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (slots : A.PortOrder quota) (source : Bank) (origin : ℕ) (m : Memory w)
    (original : Reads source (A.rawCensus (plane ev h) ej slots b) M m)
    (sourceFit : source.Fits w chart.weights.base) (nsource : 2^ℓ*chunks C M ≤ source.size)
    (rom : (Phase.CensusTables.image origin ((1+b+2*quota)*2^k) (b*2^k) M (2^ℓ) C
      (fun fl=>PackedCensus.lookup fl b quota k A.wire 256 (A.z*G.b) A.hist)).Resident m)
    (early : Phase.CensusTables.finish origin ((1+b+2*quota)*2^k) M (2^ℓ) C≤chart.weights.base)
    (addressable : marked.base+2^ℓ*chunks C M<2^w) (fitsWidth : hBits≤w)
    (apart : chart.weights.base+2^ℓ*chunks C M≤ marked.base)
    (before : chart.roster.base+chart.roster.size≤chart.weights.base)
    (mounted : (Phase.Arena.image chart A.fieldBits Δ (2^ℓ) C b used D cap).Resident m)
    (topology : ∀v i,m (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    :
    let first:=Phase.CensusTables.banks source origin ((1+b+2*quota)*2^k) M (2^ℓ) C false
    let second:=Phase.CensusTables.banks source origin ((1+b+2*quota)*2^k) M (2^ℓ) C true
    let S:=Phase.Arena.shelves chart marked Δ k b used
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<M,
      ((PackedCensus.histograms first second chart.weights.base marked.base (2^ℓ) C M w).seq (Phase.program S w (2^ℓ) C M)).Exec
        m out (PackedCensus.clocks first second (2^ℓ) C M+Phase.cost S w (2^ℓ) C M) ∧
      (PackedCensus.clocks first second (2^ℓ) C M+Phase.cost S w (2^ℓ) C M)*w≤K*((96+Phase.factor k Δ)*(hBits+2^ℓ*hBits+4*2^ℓ*C*grain)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<chart.weights.base,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C M)≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs M S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C M) (A.block u)+(row (2^ℓ) C M (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat :=
  A.packed_resident_census_return_at_unit ej ev h _ le_rfl sched ready he chart marked rs members layout K wide hardware short leaves budget
    slots source origin m original sourceFit nsource rom early addressable fitsWidth apart before mounted topology


end
end Hierarchy.DescentSixParty.GroupStage

end OAI
