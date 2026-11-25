import OAI.Hierarchy.DescentPackedMatchPrepared
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # The chronological census, affine chooser, matching and profile read in one program -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.StarKeys
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
attribute [local irreducible] Gather.ROM.after Gather.ROM.machine Gather.ROM.ticks Prepare.ROM.after ProtocolRAM.result
  Chooser.Layout.program Chooser.Layout.ticks


variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S age)
  (he : 0≤ε) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ) (C : Chooser.Layout)
  (b quota payload unit ratio profile seats romBase : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "gid" => groups.toEmbedding
local notation "vid" => GroupStage.plane hosts hv
local notation "rank" => groupRank ((gid).trans Fin.valEmbedding) ((vid).trans Fin.valEmbedding)
local notation "rdx" => 2^k
local notation "cap2" => 2*A.cap
local notation "K" => 2^(k+1)
local notation "panelBits" => max (k+3) (Nat.clog 2 (A.degree+1))
local notation "s" => shape rdx A.degree cap2 profile
local notation "grain" => M*(s).pairs
variable (P₀ : Ports A.degree) (act : Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "vals" => C.winners A.degree k b H G M
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap (k+3) M H G
local notation "bits_" => Prepare.bits H G M
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "prep" => Prepare.ROM.chart romBase A.degree (k+3) M bits_ act vals wire
local notation "sort_" => Prepare.ROM.roster romBase k A.degree A.cap (k+3) M H G (Prepare.ROM.headBits H A.degree) P₀.roster
local notation "ps" => Prepare.passes prep sort_ base H G M A.degree
local notation "wins_" => Prepare.gatedBank (k:=k) base H G M A.degree bits_
local notation "marks_" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree bits_
local notation "field" => Gather.expr wins_ marks_ {P₀ with roster:=outB} H
local notation "donor" => Gather.ROM.donorExpr s panelBits rdx A.degree cap2 K H G M unit nextBase seats field
local notation "plan" => Gather.ROM.place s panelBits rdx A.degree cap2 K H G M unit nextBase seats
local notation "stamp" => Prepare.ROM.program w romBase k A.degree A.cap (k+3) panelBits M H G
local notation "matcher" => Gather.ROM.machine s panelBits rdx A.degree cap2 A.cap K H G M unit nextBase seats w field
local notation "warm" => (stamp).seq (ProtocolRAM.program w ps)
local notation "before" => C.program A.degree k b quota H G M w
local notation "time₀" => C.ticks A.degree k b quota H G M w
local notation "time₁" => ((4+10*Prepare.staticWords k A.degree A.cap (k+3) M H G)+ProtocolRAM.clock ps)+
  Gather.ROM.ticks s panelBits rdx A.degree cap2 K H G M unit nextBase seats field
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home

/-- Every native instruction and its clock depend only on the public address chart.
The two observed selectors and all matching fields are read after that program runs. -/
theorem ordinary_cpu_observed (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (start : Chooser.Ready A groups hosts hv C b quota payload unit ratio rs m)
    (named : A.SiteNamed rank)
    (prior : Accessible P₀ act H G M w C.chart.weights.base)
    (oldPort : ∀x j,(wire x j).Fits w C.chart.weights.base ∧ H*chunks G M≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (H*chunks G M+1))≤romBase)
    (signed : DescentSignedCableCodec.width A.degree A.cap≤unit)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j < (plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit grain stream j).val:Word w)) :
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : DescentAffineColors.Candidate k,∃hm : 0<M,
      let posted:=A.publishedTicket groups hosts rs i j
      let win:=fun h : J×V=>posted (vid h.2) (gid h.1)
      let terrain_:=terrain (short:=panelBits) A native S ready (cableNames k rank) win (rotor A rank)
      let keys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap (spread gid vid terrain_)))
      ((before).seq ((warm).seq matcher)).Exec m out (time₀+time₁) ∧
      DescentColonies.seedAt k i=(scannedRows he A.stage).μ ∧
      j=DescentAffineColors.code (scannedRows he A.stage).α (scannedRows he A.stage).β ∧
      out (C.shelves A.degree k b M).mu=(i.val:Word w) ∧ out (C.shelves A.degree k b M).paint=(j.val:Word w) ∧
      (∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (home u)).2+(color u).toNat) ∧
      Rails {P₀ with roster:=outB} wins_ marks_ (spread gid vid terrain_)
        (hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))) M nextBase out ∧
      Gather.ROM.DonorWord («M»:=M) donor (plan).source.base (spread gid vid terrain_) out ∧
      (∀q,out ((plan).layout.topology.base+q.val)=((keys q).val:Word w)) ∧
      ((∀i,(stream i).val=profileAt (inputNumber he A gid vid) ((scannedRows he A.stage).profile choice) i) → ∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let ordinal:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        let place:=slot he A gid vid hm c
        ∃v : Fin (s).pairs,v.val=ordinal ∧ digit (s).digit (finProdFinEquiv (place.2,v)).val
          (out ((plan).layout.out+place.1.val)).val=DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      ∀x,x < C.chart.weights.base ∨ (plan).endAddr ≤ x → out x=m x := by
  obtain ⟨mid,i,j,hm,choose,_,seed,paint,muWord,paintWord,words,actor,frame⟩:=Chooser.execute A groups hosts hv C b quota payload unit ratio S ready he rs m start
  let pub:=A.publishedTicket groups hosts rs i j
  let win (h : J×V):=pub (vid h.2) (gid h.1)
  have short_ (u : W.graph.Site) : (win (A.pos u) (A.block u)).val<2^panelBits :=
    (win (A.pos u) (A.block u)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left ..))
  have degree : A.degree<2^panelBits :=
    (Nat.lt_succ_self _).trans_le ((Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) (le_max_right ..)))
  have fit : unit*M≤w/2 := by
    have h:=(lanes_fit payload unit).trans (Nat.div_le_div_right (c:=2) start.embed)
    simpa only [Nat.mul_comm unit] using h
  have nextRaw : nextBase≤(plan).raw.base := by
    change nextBase≤((nextBase+_)+_)+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have allEnd : (plan).raw.base≤(plan).endAddr := by
    change (plan).raw.base≤(((((((plan).raw.base+_)+_)+_)+_)+_)+_)
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have rb : romBase≤base := by
    simp only [Prepare.ROM.sortBase,Nat.add_assoc]
    exact Nat.le_add_right ..
  have front : base≤nextBase := (Nat.le_add_right base (outB).size).trans (le_max_right ..)
  have top : romBase≤(plan).raw.base := rb.trans (front.trans nextRaw)
  have space' := (top.trans allEnd).trans_lt space
  have wires : Prepare.ROM.OldRoom act vals wire P₀.roster H G A.degree M w romBase :=
    ⟨⟨Chooser.bank_before prior.source low,prior.srcRoom⟩,Chooser.winners_before C k b A.degree H G M w romBase next space',
      fun x z=>⟨Chooser.bank_before (oldPort x z).1 low,(oldPort x z).2⟩,
      ⟨Chooser.bank_before prior.roster low,prior.rosterRoom⟩⟩
  have lower (x : ℕ) (early : x<C.chart.weights.base) := frame x (.inl early)
  have upper : C.last A.degree k b H G M≤romBase := (Nat.le_add_right ..).trans next
  obtain ⟨run_,rows,received,keep,_,rails,donorWord⟩:=Prepared.run_rails_observed A native S ready win he gid vid hm ready.coordinates named short_ actor degree profile
    P₀ romBase unit seats act vals wire choice stream mid rs start.neighbors
    (Chooser.accessible_before P₀ act prior low) wires signed
    (Chooser.reads_before act _ m mid raster lower prior.source prior.srcRoom) pub (fun _=>rfl) words
    (fun x z=>Chooser.reads_before (wire x z) _ m mid (cables x z) lower (oldPort x z).1 (oldPort x z).2)
    (Chooser.mounted_before P₀ act rs m mid mounted lower prior) large fit space cap
    (fun q good=>(frame _ (.inr (upper.trans (top.trans (Nat.le_add_right ..))))).trans (raw q good))
  have access:=(Phase.Arena.space C.chart C.marked A.fieldBits H G start.room).final
  have limit : (C.shelves A.degree k b M).output≤romBase :=
    (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans next)
  refine ⟨_,i,j,hm,?_,seed,paint,(keep _ (.inl (access.seed.trans_le limit))).trans muWord,
    (keep _ (.inl (access.paint.trans_le limit))).trans paintWord,actor,rails,donorWord,rows,received,?_⟩
  · apply Procedure.Exec.then choose
    exact run_
  · intro x hx
    rcases hx with earlier|later
    · exact (keep x (.inl (earlier.trans_le low))).trans (frame x (.inl earlier))
    · exact (keep x (.inr later)).trans (frame x (.inr (upper.trans (top.trans (allEnd.trans later)))))

theorem ordinary_cpu (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A gid vid) ((scannedRows he A.stage).profile choice) i)
    (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree) (m : Memory w)
    (start : Chooser.Ready A groups hosts hv C b quota payload unit ratio rs m)
    (named : A.SiteNamed rank)
    (prior : Accessible P₀ act H G M w C.chart.weights.base)
    (oldPort : ∀x j,(wire x j).Fits w C.chart.weights.base ∧ H*chunks G M≤(wire x j).size)
    (raster : Reads act (Prepare.actors A gid vid) M m)
    (cables : ∀x j,Reads (wire x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready gid vid x j h g)) M m)
    (mounted : Mounted P₀ rs m G M)
    (low : C.chart.weights.base≤romBase)
    (next : C.last A.degree k b H G M+2^(Nat.clog 2 (H*chunks G M+1))≤romBase)
    (signed : DescentSignedCableCodec.width A.degree A.cap≤unit)
    (large : Gather.matchUnit s panelBits rdx A.degree cap2≤unit) (space : (plan).endAddr<2^w)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : ∀j < (plan).raw.size,m ((plan).raw.base+j)=((DescentPackedProfileWindow.word (s).digit grain stream j).val:Word w)) :
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : DescentAffineColors.Candidate k,∃hm : 0<M,
      let posted:=A.publishedTicket groups hosts rs i j
      let win:=fun h : J×V=>posted (vid h.2) (gid h.1)
      let terrain_:=terrain (short:=panelBits) A native S ready (cableNames k rank) win (rotor A rank)
      let keys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap (spread gid vid terrain_)))
      ((before).seq ((warm).seq matcher)).Exec m out (time₀+time₁) ∧
      DescentColonies.seedAt k i=(scannedRows he A.stage).μ ∧
      j=DescentAffineColors.code (scannedRows he A.stage).α (scannedRows he A.stage).β ∧
      out (C.shelves A.degree k b M).mu=(i.val:Word w) ∧ out (C.shelves A.degree k b M).paint=(j.val:Word w) ∧
      (∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (home u)).2+(color u).toNat) ∧
      Rails {P₀ with roster:=outB} wins_ marks_ (spread gid vid terrain_)
        (hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))) M nextBase out ∧
      Gather.ROM.DonorWord («M»:=M) donor (plan).source.base (spread gid vid terrain_) out ∧
      (∀q,out ((plan).layout.topology.base+q.val)=((keys q).val:Word w)) ∧
      (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let ordinal:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        let place:=slot he A gid vid hm c
        ∃v : Fin (s).pairs,v.val=ordinal ∧ digit (s).digit (finProdFinEquiv (place.2,v)).val
          (out ((plan).layout.out+place.1.val)).val=DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      ∀x,x < C.chart.weights.base ∨ (plan).endAddr ≤ x → out x=m x := by
  obtain ⟨out,i,j,hm,cpu,seed,paint,muWord,paintWord,win,rails,donorRead,top,rows,frame_⟩:=ordinary_cpu_observed A native S ready he groups hosts hv C b quota payload unit ratio profile seats romBase P₀ act wire choice stream rs m start named prior oldPort raster cables mounted low next signed large space cap raw
  exact ⟨out,i,j,hm,cpu,seed,paint,muWord,paintWord,win,rails,donorRead,top,rows pins,frame_⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
