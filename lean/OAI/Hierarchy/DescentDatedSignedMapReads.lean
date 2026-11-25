import OAI.Hierarchy.DescentDatedSignedLocalRecords

namespace OAI
/-! Literal public row indices for normalization and transposition. A row
outside the actual prior or successor rectangle loads the zero word. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentParallelBase DescentParallelBase.ParentFilter DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {w : ℕ}

private theorem rect {N K:ℕ} (h:Fin N) (j:Fin K):h.val*K+j.val<N*K:=
  (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
private theorem divIdx {K:ℕ} (h:ℕ) (j:Fin K):(h*K+j.val)/K=h:=by
  rw [Nat.mul_comm h,Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
private theorem remIdx {K:ℕ} (h:ℕ) (j:Fin K):(h*K+j.val)%K=j.val:=by
  rw [Nat.mul_comm h,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt j.isLt]
private theorem rowId {H G M:ℕ} (h:Fin H) (j:Fin (chunks G M)):
    (DescentSIMDLookup.row H G M (h,j)).val=h.val*chunks G M+j.val:=by simp [DescentSIMDLookup.row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

variable (s:SignedExtent) (I:s.Input) (base:ℕ) (m:Memory w)
local notation "N"=>chunks s.groups s.lanes
local notation "P"=>s.reach
local notation "T"=>P*P
local notation "sheet"=>s.installed I base m
variable (ok:s.Fits I base w) (room:s.roof base<2^w)
def lifted (pitch:ℕ) (l:Fin s.lowSites) (h:Fin s.priorHosts):Option (Fin s.hosts):=
  if yes:l.val<pitch ∧ h.val*pitch+l.val < s.hosts then some ⟨_,yes.2⟩ else none

theorem view_index (h:Fin s.hosts) (j:Fin T):
    s.publicIndex I.hostPitch (h.val*T+j.val)=(s.rack I.hostPitch h).elim s.hdrRows (fun u=>u.val*T+j.val):=by
  have inside:h.val*T+j.val<span s.viewRows:=(rect h j).trans_le (span_ge _)
  simp only [publicIndex,ite_eq_left inside,divIdx,remIdx,rack]
  split <;> rfl

theorem transpose_index (l:Fin s.lowSites) (h:Fin s.priorHosts) (j:Fin N):
    s.publicIndex I.hostPitch (span s.viewRows+l.val*span s.oldSlab+(h.val*N+j.val))=(s.lifted I.hostPitch l h).elim s.slab (fun u=>u.val*N+j.val):=by
  let t:=h.val*N+j.val
  have rowlt:t<span s.oldSlab:=(rect h j).trans_le (span_ge _)
  have inside:l.val*span s.oldSlab+t < s.lowSites*span s.oldSlab:=rect l ⟨t,rowlt⟩
  have lo:¬span s.viewRows+l.val*span s.oldSlab+t<span s.viewRows:=by omega
  have sub:span s.viewRows+l.val*span s.oldSlab+t-span s.viewRows=l.val*span s.oldSlab+t:=by omega
  simp only [publicIndex,ite_eq_right lo,sub,ite_eq_left inside,remIdx _ (⟨t,rowlt⟩:Fin (span s.oldSlab)),divIdx _ (⟨t,rowlt⟩:Fin (span s.oldSlab)),t,divIdx,remIdx,lifted]
  split <;> rfl

theorem host_index (h:Fin s.hosts) (j:Fin N):
    s.publicIndex I.hostPitch (span s.viewRows+s.lowSites*span s.oldSlab+(h.val*N+j.val))=(if I.hostPitch=0 then s.priorHosts else min (h.val/I.hostPitch) s.priorHosts)*P:=by
  let t:=h.val*N+j.val
  have rowlt:t<span s.slab:=(rect h j).trans_le (span_ge _)
  simp only [publicIndex]
  split
  · omega
  · split
    · omega
    · have eqn:span s.viewRows+s.lowSites*span s.oldSlab+t-span s.viewRows-s.lowSites*span s.oldSlab=t:=by omega
      simp only [eqn,ite_eq_left rowlt,t,divIdx]

theorem chunk_index (h:Fin s.hosts) (j:Fin N):
    s.publicIndex I.hostPitch (span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+(h.val*N+j.val))=j.val:=by
  let t:=h.val*N+j.val
  have rowlt:t<span s.slab:=(rect h j).trans_le (span_ge _)
  simp only [publicIndex]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · have eqn:span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+t-span s.viewRows-s.lowSites*span s.oldSlab-span s.slab=t:=by omega
        simp only [eqn,ite_eq_left rowlt,t,remIdx]

theorem offset_index (h:Fin s.priorHosts):
    s.publicIndex I.hostPitch (span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+span s.slab+h.val)=h.val*N:=by
  let a := span s.viewRows
  let b := s.lowSites*span s.oldSlab
  let c := span s.slab
  have h₁ : ¬a+b+c+c+h.val < a := by omega
  have h₂ : a+b+c+c+h.val-a = b+c+c+h.val := by omega
  have h₃ : ¬b+c+c+h.val < b := by omega
  have h₄ : b+c+c+h.val-b = c+c+h.val := by omega
  have h₅ : ¬c+c+h.val < c := by omega
  have h₆ : c+c+h.val-c = c+h.val := by omega
  have h₇ : ¬c+h.val < c := by omega
  have h₈ : c+h.val-c = h.val := by omega
  dsimp only [a,b,c] at *
  simp only [publicIndex, h₁, ↓reduceIte, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

include ok room in
theorem public_index_word (i:Fin s.mapIndices):
    sheet (s.mapBase base+i.val)=(s.publicIndex I.hostPitch i.val:Word w):=by
  exact (s.funded_map I base m ok room ⟨_,i.isLt.trans_le (Nat.le_add_right ..)⟩).trans (by simp [maps,i.isLt])

include ok room in
theorem shape_word (h:Fin s.hosts) (j:Fin T):
    sheet ((s.mapBase base)+(h.val*T+j.val))=((s.rack I.hostPitch h).elim s.hdrRows (fun u=>u.val*T+j.val):ℕ):=by
  have hi:h.val*T+j.val < s.mapIndices:=by
    have z:=(rect h j).trans_le (span_ge s.viewRows)
    unfold mapIndices;omega
  exact (s.public_index_word I base m ok room ⟨_,hi⟩).trans (congrArg (fun a:ℕ=>(a:Word w)) (s.view_index I h j))

include ok room in
theorem transpose_word (l:Fin s.lowSites) (h:Fin s.priorHosts) (j:Fin N):
    sheet ((subbank (s.mapTranspose base) s.oldSlab l.val).base+(h.val*N+j.val))=
      ((s.lifted I.hostPitch l h).elim s.slab (fun u=>u.val*N+j.val):ℕ):=by
  let t:=span s.viewRows+l.val*span s.oldSlab+(h.val*N+j.val)
  have inner:=((rect h j).trans_le (span_ge s.oldSlab))
  have upper: l.val*span s.oldSlab+(h.val*N+j.val) < s.lowSites*span s.oldSlab:=rect l ⟨_,inner⟩
  have hi:t < s.mapIndices:=by dsimp [t,mapIndices];omega
  simpa only [t,subbank,mapTranspose,Nat.add_assoc] using
    (s.public_index_word I base m ok room ⟨t,hi⟩).trans (congrArg (fun a:ℕ=>(a:Word w)) (s.transpose_index I l h j))

include ok room in
theorem host_word (h:Fin s.hosts) (j:Fin N):
    sheet ((s.mapHost base)+(h.val*N+j.val))=(((if I.hostPitch=0 then s.priorHosts else min (h.val/I.hostPitch) s.priorHosts)*P:ℕ):Word w):=by
  let t:=span s.viewRows+s.lowSites*span s.oldSlab+(h.val*N+j.val)
  have inside:=(rect h j).trans_le (span_ge s.slab)
  have hi:t < s.mapIndices:=by dsimp [t,mapIndices];omega
  simpa only [t,mapHost,mapTranspose,Nat.add_assoc] using (s.public_index_word I base m ok room ⟨t,hi⟩).trans
    (congrArg (fun a:ℕ=>(a:Word w)) (s.host_index I h j))

include ok room in
theorem chunk_word (h:Fin s.hosts) (j:Fin N):
    sheet ((s.mapChunk base)+(h.val*N+j.val))=(j.val:Word w):=by
  let t:=span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+(h.val*N+j.val)
  have inside:=(rect h j).trans_le (span_ge s.slab)
  have hi:t < s.mapIndices:=by dsimp [t,mapIndices];omega
  simpa only [t,mapChunk,mapHost,mapTranspose,Nat.add_assoc] using (s.public_index_word I base m ok room ⟨t,hi⟩).trans
    (congrArg (fun a:ℕ=>(a:Word w)) (s.chunk_index I h j))

include ok room in
theorem offset_word (h:Fin s.priorHosts):
    sheet (s.mapOffset base+h.val)=((h.val*N:ℕ):Word w):=by
  let t:=span s.viewRows+s.lowSites*span s.oldSlab+span s.slab+span s.slab+h.val
  have inside:=h.isLt.trans_le (span_ge s.priorHosts)
  have hi:t < s.mapIndices:=by dsimp [t,mapIndices];omega
  simpa only [t,mapOffset,mapChunk,mapHost,mapTranspose,Nat.add_assoc] using (s.public_index_word I base m ok room ⟨t,hi⟩).trans
    (congrArg (fun a:ℕ=>(a:Word w)) (s.offset_index I h))
theorem eval_indexed {count w out:ℕ} (B:Bank) (m:Memory w) (index:Expr) (row:Word w) (choice:Option (Fin count))
    (observed:index.eval m row=((choice.elim count Fin.val:ℕ):Word w)) (fits:B.Fits w out) (enough:count≤B.size):
    (indexed index count B).eval m row=choice.elim 0 (fun n=>m (B.base+n.val)):=by
  cases choice with
  | none=>
    change (if Comparison.eq.test (index.eval m row) (count:Word w) then 0 else _) = _
    simp [observed,Comparison.test]
  | some n=>
    have hn:count<2^w:=enough.trans_lt fits.2.1
    have neq:(n.val:Word w)≠(count:Word w):=by
      intro h;have eqn:=congrArg Fin.val h
      rw [Fin.val_cast_of_lt (n.isLt.trans hn),Fin.val_cast_of_lt hn] at eqn
      exact (Nat.ne_of_lt n.isLt) eqn
    change (if Comparison.eq.test (index.eval m row) (count:Word w) then 0 else B.read m (index.eval m row))=m (B.base+n.val)
    simpa [observed,Comparison.test,neq] using bank_read B m (n.isLt.trans_le enough) fits

include ok room in
theorem normalized_header (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts)) (size:T<2^s.fieldBits)
    (real:DescentOrdinaryDonorRankDirectory.Reads R I.rankBanks m)
    (fit:DescentOrdinaryDonorRankDirectory.Fits I.rankBanks base s.priorHosts P w)
    (early:∀f,(DescentOrdinaryDonorRankDirectory.expression I.rankBanks s.priorHosts f).Fits w base)
    (headerFits:∀i:Fin 3,(subbank base s.hdrRows i.val).Fits w (s.tailStart base))
    (mapFits:(subbank (s.mapBase base) s.viewRows 0).Fits w (s.tailStart base)):
    ∀f (h:Fin s.hosts) (j:Fin T),sheet ((subbank (s.viewBase base) s.viewRows (fieldNumber f)).base+(h.val*T+j.val))=
      ((s.directoryAt R size I.hostPitch f h j).val:Word w):=by
  have keep:∀a<base,sheet a=m a:=(s.installed_words I base m ok room).2
  intro f h j
  let i:Fin 3:=match f with | .reverse=>0 | .localEndpoint=>1 | .sharedEndpoint=>2
  have fi:fieldIndex i=f:=by cases f <;> rfl
  have num:fieldNumber f=i.val:=by cases f <;> rfl
  have entry (v:Fin s.priorHosts) (a:Fin T):
      sheet ((subbank base s.hdrRows i.val).base+(v.val*T+a.val))=((DescentOrdinaryDonorRankDirectory.directory R size f v a).val:Word w):=by
    apply DescentOrdinaryDonorRankDirectory.header_words R f size sheet (subbank base s.hdrRows i.val).base _ v a
    intro u p q
    let n:=Ranks.id u (PairRanks.pair p q)
    exact (s.funded_field I base m ok room i n).trans (by
      rw [fi]
      exact (eval_below _ _ m sheet (early f) keep).trans
        (DescentOrdinaryDonorRankDirectory.observed R I.rankBanks base fit m real f u p q))
  let z:Fin s.viewRows:=⟨h.val*T+j.val,rect h j⟩
  let mapB:=subbank (s.mapBase base) s.viewRows 0
  let srcB:=subbank base s.hdrRows i.val
  have ix:((.lookup mapB .row):Expr).eval sheet (z.val:Word w)=((s.rack I.hostPitch h).elim s.hdrRows (fun u=>u.val*T+j.val):ℕ):=by
    change mapB.read sheet (z.val:Word w)=_
    rw [bank_read mapB sheet (z.isLt.trans_le (span_ge _)) mapFits]
    simpa only [mapB, z, subbank, Nat.zero_mul, Nat.add_zero] using s.shape_word I base m ok room h j
  rw [num]
  apply (s.funded_view I base m ok room i z).trans
  let choice:Option (Fin s.hdrRows):=(s.rack I.hostPitch h).map (fun u=>(⟨u.val*T+j.val,rect u j⟩:Fin s.hdrRows))
  have indexRead:((.lookup mapB .row):Expr).eval sheet (z.val:Word w)=((choice.elim s.hdrRows Fin.val:ℕ):Word w):=by
    rw [ix];cases hr:s.rack I.hostPitch h <;> simp [choice,hr]
  refine (eval_indexed srcB sheet (.lookup mapB .row) (z.val:Word w) choice indexRead (headerFits i) (span_ge _)).trans ?_
  cases hr:s.rack I.hostPitch h with
  | none=>simp [choice,hr,directoryAt]
  | some v=>simpa [choice,hr,directoryAt] using entry v j

theorem packed_choice {a n G M:ℕ} (f:Fin n→Fin G→Cell a) (r:Option (Fin n)) (j:Fin (chunks G M)):
    (data (fun _ : Fin 1=>fun g=>r.elim 0 (fun u=>f u g)) ((0:Fin 1),j)).val=r.elim 0 (fun u=>(data f (u,j)).val):=by
  cases r with
  | none=>change (finFunctionFinEquiv (fun i:Fin M=>if _ : j.val*M+i.val<G then (0:Cell a) else 0)).val=0;simp
  | some u=>rfl

include ok room in
theorem projected_words (raw:s.Socket→Fin 11→Fin s.hosts→Fin s.groups→Cell s.fieldBits)
    (original:∀z f,Source (s.rawField base z f) (raw z f) s.lanes sheet)
    (oldFit:∀l:Fin s.lowSites,(subbank (s.mapTranspose base) s.oldSlab l.val).Fits w (s.tailStart base))
    (newFit:∀z f,(subbank (s.localStart base) s.slab (s.localId z f)).Fits w (s.tailStart base))
    (z:s.Socket) (f:Fin 11) (l:Fin s.lowSites):
    Reads (subbank (s.projectedStart base) s.oldSlab (s.projectedId z f l))
      (fun h g=>(s.lifted I.hostPitch l h).elim 0 (fun u=>raw z f u g)) s.lanes sheet:=by
  rintro ⟨h,j⟩
  let row₀:=DescentSIMDLookup.row s.priorHosts s.groups s.lanes (h,j)
  let B:=subbank (s.localStart base) s.slab (s.localId z f)
  let ptr:Expr:=.lookup (subbank (s.mapTranspose base) s.oldSlab l.val) .row
  let choice:Option (Fin s.slab):=(s.lifted I.hostPitch l h).map (fun u=>DescentSIMDLookup.row s.hosts s.groups s.lanes (u,j))
  have loc:ptr.eval sheet (row₀.val:Word w)=((choice.elim s.slab Fin.val:ℕ):Word w):=by
    change (subbank (s.mapTranspose base) s.oldSlab l.val).read sheet (row₀.val:Word w)=_
    rw [bank_read _ sheet (row₀.isLt.trans_le (span_ge _)) (oldFit l)]
    change sheet (_+(DescentSIMDLookup.row s.priorHosts s.groups s.lanes (h,j)).val)=_
    rw [rowId,s.transpose_word I base m ok room l h j]
    cases hit:s.lifted I.hostPitch l h with
    | none =>
      have hc : choice=none := by change Option.map _ _=none; rw [hit]; rfl
      rw [hc]
      rfl
    | some u =>
      have hc : choice=some (DescentSIMDLookup.row s.hosts s.groups s.lanes (u,j)) := by
        change Option.map _ _=some _; rw [hit]; rfl
      rw [hc]
      exact congrArg (fun a : ℕ => (a:Word w)) (rowId u j).symm
  apply (s.funded_transpose I base m ok room z f l row₀).trans
  apply (eval_indexed B sheet ptr _ choice loc (newFit z f) (span_ge _)).trans
  cases hit:s.lifted I.hostPitch l h with
  | none=>
    change _=(↑(data (fun h g=>(s.lifted I.hostPitch l h).elim 0 (fun u=>raw z f u g)) (h,j)).val:Word w)
    have eqn:(data (fun h g=>(s.lifted I.hostPitch l h).elim 0 (fun u=>raw z f u g)) (h,j)).val=
        (s.lifted I.hostPitch l h).elim 0 (fun u=>(data (raw z f) (u,j)).val):=packed_choice (raw z f) (s.lifted I.hostPitch l h) j
    have hc : choice=none := by change Option.map _ _=none; rw [hit]; rfl
    rw [hc,eqn,hit]
    rfl
  | some u=>
    have read:=original z f (u,j)
    change B.read sheet ((DescentSIMDLookup.row s.hosts s.groups s.lanes (u,j)).val:Word w)=_ at read
    rw [bank_read _ sheet ((DescentSIMDLookup.row s.hosts s.groups s.lanes (u,j)).isLt.trans_le (span_ge _)) (newFit z f)] at read
    have eqn:(data (fun h g=>(s.lifted I.hostPitch l h).elim 0 (fun a=>raw z f a g)) (h,j)).val=
        (s.lifted I.hostPitch l h).elim 0 (fun a=>(data (raw z f) (a,j)).val):=packed_choice (raw z f) (s.lifted I.hostPitch l h) j
    have hc : choice=some (DescentSIMDLookup.row s.hosts s.groups s.lanes (u,j)) := by
      change Option.map _ _=some _; rw [hit]; rfl
    rw [hc]
    change _=(((data (fun h g=>(s.lifted I.hostPitch l h).elim 0 (fun u=>raw z f u g)) (h,j)).val:ℕ):Word w)
    rw [eqn,hit]
    exact read

def selected (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts)) (p:Fin s.reach) (h:Fin s.hosts):Option (Fin s.priorHosts):=
  (s.rack I.hostPitch h).bind (fun v=>Gather.select (Gather.reaching R) v p)

include ok room in
/-- The second hop of the return. Its donor is the first occurrence in
the real deduplicated halo at the projected old rack of the receiver. -/
theorem remote_source (R:Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts))
    (seen:∀v p,sheet (I.rankBanks.endpoints.base+(Ranks.id v p).val)=(number (Gather.select (Gather.reaching R) v p):Word w))
    (c:s.Consumer) (f:Fin 11) (v:Fin s.priorHosts→Fin s.groups→Cell s.fieldBits)
    (data_:Reads (subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)) v s.lanes sheet)
    (rootFit:(subbank (s.mapHost base) s.slab 0).Fits w (s.tailStart base))
    (endFit:I.rankBanks.endpoints.Fits w (s.tailStart base)) (endSize:s.priorHosts*P≤I.rankBanks.endpoints.size)
    (offFit:(subbank (s.mapOffset base) s.priorHosts 0).Fits w (s.tailStart base))
    (chunkFit:(subbank (s.mapChunk base) s.slab 0).Fits w (s.tailStart base))
    (returnFit:(subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)).Fits w (s.tailStart base)):
    Source (s.remoteWord I base c f) (fun h g=>(s.selected I R (s.priorSlot c).1 h).elim 0 (fun u=>v u g)) s.lanes sheet:=by
  rintro ⟨h,j⟩
  let p:=(s.priorSlot c).1
  let row₀:=DescentSIMDLookup.row s.hosts s.groups s.lanes (h,j)
  let words (u:Fin s.priorHosts):=(data v (u,j)).val
  let choose:=s.selected I R p h
  have digits:(data (fun t g=>(s.selected I R p t).elim 0 (fun u=>v u g)) (h,j)).val=choose.elim 0 words:=
    packed_choice v choose j
  have roomH:s.priorHosts<2^w:=(span_ge _).trans_lt offFit.2.1
  have upto:s.priorHosts*P<2^w:=endSize.trans_lt endFit.2.1
  let hdr:Expr:=.lookup (subbank (s.mapHost base) s.slab 0) .row
  let who:Expr:=.lookup I.rankBanks.endpoints (.op .add hdr (.lit p.val))
  let chr:Expr:=.lookup (subbank (s.mapChunk base) s.slab 0) .row
  let st:Expr:=.lookup (subbank (s.mapOffset base) s.priorHosts 0) who
  let B:=subbank (s.returnedStart base) s.oldSlab (s.returnedId c f)
  have host:hdr.eval sheet (row₀.val:Word w)=(((s.rack I.hostPitch h).elim (s.priorHosts*P) (fun u=>u.val*P):ℕ):Word w):=by
    change (subbank (s.mapHost base) s.slab 0).read sheet (row₀.val:Word w)=_
    rw [bank_read _ sheet (row₀.isLt.trans_le (span_ge _)) rootFit]
    change sheet (_+(DescentSIMDLookup.row s.hosts s.groups s.lanes (h,j)).val)=_
    simp only [subbank,Nat.zero_mul,Nat.add_zero,rowId]
    rw [s.host_word I base m ok room h j]
    unfold rack
    by_cases pos:0<I.hostPitch
    · simp only [ite_eq_right pos.ne']
      split <;> rename_i good
      · simp [min_eq_left good.2.le]
      · have h₀:s.priorHosts≤h.val/I.hostPitch:=by omega
        simp [min_eq_right h₀]
    · have z:I.hostPitch=0:=by omega
      simp [z]
  change (if Comparison.eq.test (hdr.eval sheet (row₀.val:Word w)) (s.priorHosts*P:ℕ) then 0 else
    if Comparison.eq.test (who.eval sheet (row₀.val:Word w)) s.priorHosts then 0 else
      B.read sheet ((st.eval sheet (row₀.val:Word w))+(chr.eval sheet (row₀.val:Word w))))=_
  rw [digits]
  cases hr:s.rack I.hostPitch h with
  | none=>simp [host,hr,Comparison.test,choose,selected]
  | some u=>
    have spp:0<P:=by dsimp [reach,breadth];positivity
    have smaller:u.val*P < s.priorHosts*P:=Nat.mul_lt_mul_of_pos_right u.isLt spp
    have ne:((u.val*P:ℕ):Word w)≠(s.priorHosts*P:ℕ):=by
      intro h';have same:=congrArg Fin.val h';rw [Fin.val_cast_of_lt (smaller.trans upto),Fin.val_cast_of_lt upto] at same;omega
    have root:who.eval sheet (row₀.val:Word w)=(number (Gather.select (Gather.reaching R) u p):Word w):=by
      have i:=(rect u p).trans_le endSize
      change I.rankBanks.endpoints.read sheet (BinaryOp.eval .add (hdr.eval sheet (row₀.val:Word w)) (p.val:Word w))=_
      simp only [host,hr,Option.elim_some,BinaryOp.eval,←Nat.cast_add,bank_read _ sheet i endFit]
      simpa [Ranks.id,finProdFinEquiv_apply_val,reach,Nat.mul_comm,Nat.add_comm] using seen u p
    cases found:Gather.select (Gather.reaching R) u p with
    | none=>simp [host,hr,root,found,number,Comparison.test,choose,selected]
    | some d=>
      have nd:(d.val:Word w)≠(s.priorHosts:Word w):=by
        intro h';have same:=congrArg Fin.val h';rw [Fin.val_cast_of_lt (d.isLt.trans roomH),Fin.val_cast_of_lt roomH] at same;omega
      have ofs:st.eval sheet (row₀.val:Word w)=((d.val*N:ℕ):Word w):=by
        change (subbank (s.mapOffset base) s.priorHosts 0).read sheet (who.eval sheet (row₀.val:Word w))=_
        simp only [root,found,number,Option.elim_some,bank_read _ sheet (d.isLt.trans_le (span_ge _)) offFit]
        simpa [subbank] using s.offset_word I base m ok room d
      have chip:chr.eval sheet (row₀.val:Word w)=(j.val:Word w):=by
        change (subbank (s.mapChunk base) s.slab 0).read sheet (row₀.val:Word w)=_
        rw [bank_read _ sheet (row₀.isLt.trans_le (span_ge _)) chunkFit]
        simpa [row₀,rowId,subbank] using s.chunk_word I base m ok room h j
      have idx:(d.val*N+j.val)<B.size:=(rect d j).trans_le (span_ge _)
      have test₁ : Comparison.eq.test ((u.val*P:ℕ):Word w) ((s.priorHosts*P:ℕ):Word w)=false := by
        simpa only [Comparison.test, beq_eq_false_iff_ne] using ne
      have test₂ : Comparison.eq.test (d.val:Word w) (s.priorHosts:Word w)=false := by
        simpa only [Comparison.test, beq_eq_false_iff_ne] using nd
      simp only [host,hr,root,found,number,Option.elim_some,test₁,test₂,Bool.false_eq_true,↓reduceIte,
        choose,selected,Option.bind_some,ofs,chip,←Nat.cast_add,bank_read B sheet idx returnFit, words]
      simpa only [rowId] using data_ (d,j)


end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
