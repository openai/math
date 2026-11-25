import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentRecordedReservationRead
import OAI.Hierarchy.DescentRotorPeerIssue
import OAI.Hierarchy.DescentRotorHostMetadata
import OAI.Hierarchy.DescentPaddedFlowRoster

namespace OAI
/-! # The six rotor reservation fields at a native, padded old-host row -/
namespace Hierarchy.DescentReservationHeader
open ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
def entries (levels total : ℕ) := 2^levels+2^(levels+total)

def entry (levels total K scale Y : ℕ) (j : ℕ) :=
  if j<2^levels then 2^total*j else
    let key:=j-2^levels
    width K scale (key/2^total) (key%2^total) Y

def span (hosts : ℕ) := 2^(Nat.clog 2 hosts)
def reserveEntries (hosts levels total : ℕ) := entries levels total+span hosts+span hosts

theorem reserveEntries_le (hosts levels total : ℕ) :
    reserveEntries hosts levels total≤2^levels*(1+2^total)+4*hosts+2 := by
  have port : span hosts≤2*hosts+1:=DescentDyadicSpan.span_le hosts
  unfold reserveEntries entries
  rw [pow_add,Nat.mul_add,Nat.mul_one]
  omega

theorem reserveEntries_depth (hosts dim total : ℕ) :
    reserveEntries hosts (Nat.clog 2 (dim+2)) total ≤
      (2*(dim+2)+1)*(1+2^total)+4*hosts+2 := by
  apply (reserveEntries_le ..).trans
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (DescentDyadicSpan.span_le (dim+2))) _) _
def reserveEntry (hosts pitch dim high levels total K scale Y : ℕ) (j : ℕ) :=
  let cells:=entries levels total
  if j<cells then entry levels total K scale Y j
  else if j<cells+span hosts then (j-cells)*(dim+1)
  else (hosts*(dim+1)+(j-(cells+span hosts))*pitch)*2^high

def strideDepth (base hosts levels total : ℕ) : Bank :=⟨base+entries levels total,Nat.clog 2 hosts⟩
def strideLead (base hosts levels total : ℕ) : Bank :=⟨base+(entries levels total+span hosts),Nat.clog 2 hosts⟩

structure Strides {w : ℕ} (base hosts pitch dim high levels total ceiling : ℕ) (m : Memory w) : Prop where
  depthRoom : (strideDepth base hosts levels total).Fits w ceiling
  leadRoom : (strideLead base hosts levels total).Fits w ceiling
  depth (v : Fin hosts) : m ((strideDepth base hosts levels total).base+v.val)=(v.val*(dim+1):ℕ)
  lead (v : Fin hosts) : m ((strideLead base hosts levels total).base+v.val)=((hosts*(dim+1)+v.val*pitch)*2^high:ℕ)
end
end Hierarchy.DescentReservationHeader

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentPackedWalsh DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSharedLeafLookup
open DescentPlainTerminal.Suffix.PortLevels DescentPlainTerminal.Suffix.Cutoff DescentGroupPeerOrder
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option quotPrecheck false
namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i

/-- Both depths are the first site column of the measured rectangle. -/
def depthAt (E : EstimatorArena) (base hosts levels total : ℕ) (host : Expr) : Expr :=
  .lookup E.depthRows (.lookup (DescentReservationHeader.strideDepth base hosts levels total) host)

/-- Look up the start of an old host's contact spectra and add the chosen zero column. -/
def contactAt (E : EstimatorArena) (base hosts levels total slot : ℕ) (host : Expr) : Expr :=
  .op .add (.lookup (DescentReservationHeader.strideLead base hosts levels total) host) (.lit (slot*2^E.high))

def sizeAt (E : EstimatorArena) (hosts _pitch slot base levels total : ℕ) (self next : Expr) : Expr :=
  term base levels total (depthAt E base hosts levels total self) (depthAt E base hosts levels total next)
    (firstTotal (firstContactBank E) (contactAt E base hosts levels total slot self) E.precision)

def reservationFields {Δ : ℕ} (E : EstimatorArena) (B : Header) (P : Ports Δ)
    (hosts pitch c r base levels total : ℕ) (self : Expr) (query candidate : Fin Δ) (field : Fin 6) : Expr :=
  let neighbor:=neighborID P candidate
  DescentRotorPeerIssue.broadcast B.cut B.broadcast
    (DescentRotorPeerIssue.operandAt P hosts c r query candidate (level (.lit c) (depthAt E base hosts levels total neighbor))
      (sizeAt E hosts pitch candidate.val base levels total self neighbor) field)

/-- Each candidate reads a fixed number of original and adjacent operands per packed word. -/
theorem reservationFields_work {Δ : ℕ} (B : Header) (P : Ports Δ)
    (hosts pitch c r base levels total : ℕ) (self : Expr) (q j : Fin Δ) (field : Fin 6) :
    (reservationFields E B P hosts pitch c r base levels total self q j field).work≤300+4*self.work := by
  fin_cases field <;>
    simp only [reservationFields,DescentRotorPeerIssue.broadcast,DescentRotorPeerIssue.operandAt,
      relative,protect,DescentShortReservationPeer.fields,neighborID,depthAt,sizeAt,contactAt,DescentPlainTerminal.Suffix.Cutoff.term,DescentPlainTerminal.Suffix.Cutoff.level,firstTotal,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_fin_one,Expr.work] <;> omega

theorem reservationFields_fits_of_span {w ceiling hosts pitch c r base levels total Δ groups batch field : ℕ}
    (B : Header) (P : Ports Δ) (old : Bank) (self : Expr)
    (fit : self.Fits w ceiling) (support : Accessible P old hosts groups batch w ceiling)
    (extent : base+DescentReservationHeader.reserveEntries hosts levels total≤ceiling)
    (Broom : DescentRotorPeerIssue.BroadcastRoom B hosts groups batch field w ceiling)
    (depth : E.depthRows.Fits w ceiling) (first : (firstContactBank E).Fits w ceiling)
    (roof : ceiling<2^w) (q j : Fin Δ) (u : Fin 6) :
    (reservationFields E B P hosts pitch c r base levels total self q j u).Fits w ceiling := by
  let pad:=DescentReservationHeader.span hosts
  have pos : 0<pad:=Nat.two_pow_pos _
  change base+((2^levels+2^(levels+total))+pad+pad)≤ceiling at extent
  have a : 0<(2^levels:ℕ):=Nat.two_pow_pos _
  have b : 0<(2^(levels+total):ℕ):=Nat.two_pow_pos _
  have depthRoom : (DescentReservationHeader.strideDepth base hosts levels total).Fits w ceiling := by
    change 0<pad ∧ pad<2^w ∧ base+(2^levels+2^(levels+total))+pad≤ceiling
    exact ⟨pos,by omega,by omega⟩
  have leadRoom : (DescentReservationHeader.strideLead base hosts levels total).Fits w ceiling := by
    change 0<pad ∧ pad<2^w ∧ base+((2^levels+2^(levels+total))+pad)+pad≤ceiling
    exact ⟨pos,by omega,by omega⟩
  have l:(levelBank base levels).Fits w ceiling:=by
    change 0<(2^levels:ℕ) ∧ 2^levels<2^w ∧ base+2^levels≤ceiling
    exact ⟨a,by omega,by omega⟩
  have t:(tableBank base levels total).Fits w ceiling:=by
    change 0<(2^(levels+total):ℕ) ∧ 2^(levels+total)<2^w ∧ base+2^levels+2^(levels+total)≤ceiling
    exact ⟨b,by omega,by omega⟩
  fin_cases u <;>
    simp only [reservationFields,DescentRotorPeerIssue.broadcast,DescentRotorPeerIssue.operandAt,
      relative,protect,DescentShortReservationPeer.fields,neighborID,depthAt,sizeAt,contactAt,DescentPlainTerminal.Suffix.Cutoff.term,DescentPlainTerminal.Suffix.Cutoff.level,firstTotal,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_fin_one,Expr.Fits,
      Broom.cut,Broom.repeatFit,depth,first,t,l,leadRoom,depthRoom,fit,support.roster,support.ids,
      and_self]

theorem reservationFields_fits {w ceiling hosts pitch c r base levels total Δ groups batch field : ℕ}
    (B : Header) (P : Ports Δ) (old : Bank) (mem : Memory w) (self : Expr)
    (fit : self.Fits w ceiling) (support : Accessible P old hosts groups batch w ceiling)
    (chart : DescentReservationHeader.Strides base hosts pitch E.dim E.high levels total ceiling mem)
    (Broom : DescentRotorPeerIssue.BroadcastRoom B hosts groups batch field w ceiling)
    (depth : E.depthRows.Fits w ceiling) (first : (firstContactBank E).Fits w ceiling)
    (roof : ceiling<2^w) (q j : Fin Δ) (u : Fin 6) :
    (reservationFields E B P hosts pitch c r base levels total self q j u).Fits w ceiling := by
  apply reservationFields_fits_of_span E B P old self fit support _ Broom depth first roof q j u
  simpa only [DescentReservationHeader.strideLead, DescentReservationHeader.reserveEntries, Bank.size,
    DescentReservationHeader.span,Nat.add_assoc] using chart.leadRoom.2.2

theorem depth_at_eval {w base hosts pitch levels total ceiling : ℕ} (m : Memory w) (tick : Word w)
    (self : Expr) (v : Fin hosts)
    (chart : DescentReservationHeader.Strides base hosts pitch E.dim E.high levels total ceiling m)
    (seen : self.eval m tick=(v.val:Word w)) :
    (depthAt E base hosts levels total self).eval m tick=(attainedDepth E v.val).eval m tick := by
  have cap : hosts≤(DescentReservationHeader.strideDepth base hosts levels total).size:=Nat.le_pow_clog (by decide) _
  simp only [depthAt,attainedDepth,Expr.eval,seen,bank_read _ _ (v.isLt.trans_le cap) chart.depthRoom,chart.depth]

/-- Ordering the original neighbors by the numbered vertex gives exactly their contact column. -/
theorem contact_slot (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (v u : input.V) (j : Fin (A).degree)
    (active : hostRoster A (input.vertex.trans Fin.valEmbedding) v j=some u) :
    ∃e : Contacts (A).mutual,e.1=v ∧ e.2.val=u ∧
      (contactRow E dim maxPorts ports hostCount e).val=
        S.hostSize i*(E.dim+1)+(input.vertex v).val*maxPorts+j.val := by
  let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
  let name:=((A).numberedHeader digits input.vertex).site
  unfold hostRoster at active
  split at active
  · rename_i present
    obtain rfl : present.choose.val=u := Option.some.inj active
    let e : Contacts (A).mutual:=⟨v,⟨present.choose.val,(PackedFlow.mutual_near A).symm ▸ present.choose.property⟩⟩
    refine ⟨e,rfl,rfl,?_⟩
    unfold contactRow PackedFlow.Canvas.loc
    change ((publicRectangle _ _ _ _ _ _) (.inr e)).val=_
    erw [public_port]
    change _+(input.vertex v).val*maxPorts+((DescentPackedExchange.neighborOrder name ((A).mutual v)) e.2).val=_
    congr 1
    rw [PackedFlow.numbered_rank]
    change (((A).mutual v).filter (fun x => name x < name present.choose.val)).card=j.val
    rw [PackedFlow.mutual_near]
    exact (hostSlot_val A (input.vertex.trans Fin.valEmbedding) v present.choose).symm.trans
      (congrArg Fin.val present.choose_spec)
  · contradiction

private theorem cutoff_congr {w : ℕ} (mem : Memory w) (tick : Word w) (base levels total precision : ℕ)
    (bank : Bank) {a b x d e y : Expr} (left : a.eval mem tick=d.eval mem tick)
    (right : b.eval mem tick=e.eval mem tick) (index : x.eval mem tick=y.eval mem tick) :
    (term base levels total a b (firstTotal bank x precision)).eval mem tick=
      (term base levels total d e (firstTotal bank y precision)).eval mem tick := by
  simp only [DescentPlainTerminal.Suffix.Cutoff.term,DescentPlainTerminal.Suffix.Cutoff.level,firstTotal,Expr.eval,left,right,index]

include accepted in
/-- A row index and a peer read from the real directory select the same threshold table and
    first contact word as the recorded ordered reset. -/
theorem size_at_read {w ceiling : ℕ} (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (m : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) m)
    (depths :
      let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name:=((A).numberedHeader digits input.vertex).site
      ∀v,m (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w))
    (depthLegal : E.depthRows.Fits w ceiling) (depthRoom : ∀v,(input.vertex v).val*(E.dim+1)<E.depthRows.size)
    (bankLegal : (firstContactBank E).Fits w ceiling) (wordBits : E.precision≤w)
    (base levels total : ℕ) (v u : input.V) (j : Fin (A).degree)
    (active : hostRoster A (input.vertex.trans Fin.valEmbedding) v j=some u)
    (maxDepth : max (reset.reset.placement.b (reset.frame.host v)) (reset.reset.placement.b (reset.frame.host u))<2^levels)
    (sumFits : (∑x,(A).resetFlow sourceDigits v u x)<2^total)
    (widthBits : levels+total≤w) (output : n<w) (hw : 0<wire) (hK : 0<K) (positive : 0<wire*(z*G.b)*(A).cap)
    (static : DescentReservationHeader.Resident base levels total K (2^f*(wire*(z*G.b)*(A).cap)) (2^n) m)
    (chart : DescentReservationHeader.Strides base (S.hostSize i) maxPorts E.dim E.high levels total ceiling m)
    (tick : Word w) (self next : Expr) (owner : self.eval m tick=((input.vertex v).val:Word w))
    (neighbor : next.eval m tick=((input.vertex u).val:Word w)) :
    ((sizeAt E (S.hostSize i) maxPorts j.val base levels total self next).eval m tick).val=
      min (2^n) (reset.terminals.columns.size (reset.frame.host v) (reset.frame.host u)) := by
  obtain ⟨e,he,hu,slot⟩:=contact_slot (reset:=reset) E dim maxPorts ports hostCount v u j active
  let c:=contactRow E dim maxPorts ports hostCount e
  let who:=(input.vertex v).castLE input.valid.host
  have cap : S.hostSize i≤(DescentReservationHeader.strideLead base (S.hostSize i) levels total).size:=
    Nat.le_pow_clog (by decide) _
  have owner' : self.eval m tick=(who.val:Word w):=owner
  have index : (contactAt E base (S.hostSize i) levels total j.val self).eval m tick=
      ((DescentPackedWalsh.row c (fun _ : Fin E.high=>false)).val:Word w) := by
    have hit : (DescentReservationHeader.strideLead base (S.hostSize i) levels total).read m (who.val:Word w) =
        (((S.hostSize i * (E.dim+1) + who.val * maxPorts)*2^E.high : ℕ):Word w) :=
      (bank_read _ _ (who.isLt.trans_le cap) chart.leadRoom).trans (chart.lead who)
    change (DescentReservationHeader.strideLead base (S.hostSize i) levels total).read m (self.eval m tick) +
      ((j.val*2^E.high:ℕ):Word w) = _
    rw [owner',hit]
    simp only [DescentPackedWalsh.row,finProdFinEquiv_apply_val,zero_ordinal,Nat.zero_add,c,slot,who,Fin.val_castLE,Nat.add_mul,Nat.mul_add,Nat.cast_add,Nat.cast_mul]
   ; ac_rfl
  have paid:=accepted.reservation_word E dim maxPorts ports hostCount m first e depths depthLegal depthRoom
    bankLegal wordBits base levels total (by simpa only [he,hu] using maxDepth)
    (by simpa only [he,hu] using sumFits) widthBits output hw hK positive static tick
  simp only [he,hu] at paid
  have left:=depth_at_eval E m tick self who chart owner
  have right:=depth_at_eval E m tick next ((input.vertex u).castLE input.valid.host) chart neighbor
  apply Eq.trans _ paid
  apply congrArg Fin.val
  exact cutoff_congr m tick base levels total E.precision (firstContactBank E) left right index
/-- Use the reached old vertex names to interpret the padded host table. -/
def oldName (input : Reached W G q ε S k i z D wire hist) :
    input.V≃Fin (Fintype.card input.V) :=
  Equiv.ofBijective input.vertex ((Fintype.bijective_iff_injective_and_card _).mpr ⟨input.vertex.injective, by simp⟩)

def paddedValue {H b : ℕ} (c r : ℕ) (next : Fin H→Fin D→Option (Fin H))
    (depth : Fin H→ℕ) (width : Fin H→Fin H→ℕ) (v : Fin H) (query candidate : Fin D) (f : Fin 6) : Cell b :=
  match next v query,next v candidate with
  | some dest,some u=>
    let box:=DescentShortReservationPeer.compare (2^r) u.val dest.val
    (![depth u-c,width v u,box.first,box.second,box.less.toNat,box.same.toNat] f:ℕ)
  | _,_=>0

def oldHost (input : Reached W G q ε S k i z D wire hist) (h₀ : Fin (S.hostSize i)) : Option input.V :=
  (DescentPackedFlowPair.Padded.project (Fintype.card input.V) h₀).map (oldName input).symm

def oldDepth (reset : ClosedReset input ctl) (v : Fin (S.hostSize i)) : ℕ :=
  (oldHost input v).elim 0 (fun u=>reset.reset.placement.b (reset.frame.host u))

def oldWidth (reset : ClosedReset input ctl) (v u : Fin (S.hostSize i)) : ℕ :=
  (oldHost input v).elim 0 (fun a=>(oldHost input u).elim 0 (fun b=>
    min (2^n) (reset.terminals.columns.size (reset.frame.host a) (reset.frame.host b))))

private theorem oldHost_at (v : input.V) :
    oldHost input ((input.vertex v).castLE input.valid.host)=some v := by
  change (DescentPackedFlowPair.Padded.project _ (((oldName input) v).castLE input.valid.host)).map _=_
  simp [DescentPackedFlowPair.Padded.project_cast]

/-- The reached source host rank selects the original basis depth in the public padded table. -/
theorem oldDepth_at (reset : ClosedReset input ctl) (v : input.V) :
    oldDepth reset ((input.vertex v).castLE input.valid.host)=reset.reset.placement.b (reset.frame.host v) :=by
  rw [oldDepth,oldHost_at];rfl


theorem peer_at (v : input.V) (j : Fin (A).degree) :
    let emit:=fun u:input.V=>(input.vertex u).castLE input.valid.host
    PackedFlow.Padded.roster (D:=(A).degree) A (oldName input) input.valid.host (emit v) j=
      (hostRoster A (input.vertex.trans Fin.valEmbedding) v j).map emit := by
  intro emit
  unfold PackedFlow.Padded.roster DescentPackedFlowPair.Padded.next
  change ((DescentPackedFlowPair.Padded.project _ (((oldName input) v).castLE input.valid.host)).bind _)=_
  simp only [DescentPackedFlowPair.Padded.project_cast,
    show DescentPackedFlowPair.Padded.project (A).degree j=some j from
      DescentPackedFlowPair.Padded.project_cast le_rfl j,Option.bind_some]
  generalize hn : (oldName input) v = h
  have hv : (oldName input).symm h = v := by rw [←hn, Equiv.symm_apply_apply]
  subst v
  unfold PackedFlow.next hostRoster
  dsimp only
  by_cases hit : ∃u,hostSlot A (input.vertex.trans Fin.valEmbedding) ((oldName input).symm h) u=j
  · simp only [show PackedFlow.socket A ((oldName input).toEmbedding.trans Fin.valEmbedding) =
        hostSlot A (input.vertex.trans Fin.valEmbedding) from rfl, dite_eq_left hit, Option.map_some]
    rfl
  · simp only [show PackedFlow.socket A ((oldName input).toEmbedding.trans Fin.valEmbedding) =
        hostSlot A (input.vertex.trans Fin.valEmbedding) from rfl, dite_eq_right hit, Option.map_none]

private theorem peer_origin (v u : Fin (S.hostSize i)) (j : Fin (A).degree)
    (found : PackedFlow.Padded.roster (D:=(A).degree) A (oldName input) input.valid.host v j=some u) :
    ∃x y : input.V,(input.vertex x).castLE input.valid.host=v ∧
      (input.vertex y).castLE input.valid.host=u ∧ hostRoster A (input.vertex.trans Fin.valEmbedding) x j=some y := by
  cases proj : DescentPackedFlowPair.Padded.project (Fintype.card input.V) v with
  | none=>simp [PackedFlow.Padded.roster,DescentPackedFlowPair.Padded.next,proj] at found
  | some old=>
    let x:=(oldName input).symm old
    have eqn : (input.vertex x).castLE input.valid.host=v := by
      change (((oldName input) ((oldName input).symm old)).castLE input.valid.host)=v
      rw [Equiv.apply_symm_apply]
      exact (DescentPackedFlowPair.Padded.project_some proj input.valid.host).symm
    rw [←eqn,peer_at] at found
    cases pe : hostRoster A (input.vertex.trans Fin.valEmbedding) x j with
    | none=>simp [pe] at found
    | some y=>exact ⟨x,y,eqn,by simpa only [pe,Option.map_some,Option.some.injEq] using found,pe⟩


include accepted in
/-- All six words of a chosen old site use its actual old/adjacent names, attained depths
and thresholded column size. An unoccupied old site or adjacent port broadcasts zero. -/
theorem reservation_sources {w ceiling field batch groups names : ℕ}
    (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (m : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) m)
    (depths :
      let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name:=((A).numberedHeader digits input.vertex).site
      ∀v,m (E.depthRows.base+(name v).val*(E.dim+1))=(((A).mixerHeader digits name).depth A f v:Word w))
    (depthLegal : E.depthRows.Fits w ceiling) (depthRoom : ∀v,(input.vertex v).val*(E.dim+1)<E.depthRows.size)
    (bankLegal : (firstContactBank E).Fits w ceiling) (wordBits : E.precision≤w)
    (base levels total : ℕ) (depthFits : ∀v,reset.reset.placement.b (reset.frame.host v)<2^levels)
    (sumFits : ∀v u,(∑x,(A).resetFlow sourceDigits v u x)<2^total)
    (widthBits : levels+total≤w) (output : n<w) (hw : 0<wire) (hK : 0<K) (positive : 0<wire*(z*G.b)*(A).cap)
    (static : DescentReservationHeader.Resident base levels total K (2^f*(wire*(z*G.b)*(A).cap)) (2^n) m)
    (chart : DescentReservationHeader.Strides base (S.hostSize i) maxPorts E.dim E.high levels total ceiling m)
    (P : Ports (A).degree) (prior : Bank) (B : Header) (self : Expr)
    (support : Accessible P prior (S.hostSize i) groups batch w ceiling)
    (mounted : Mounted P (PackedFlow.Padded.roster A (oldName input) input.valid.host) m groups batch)
    (Broom : DescentRotorPeerIssue.BroadcastRoom B (S.hostSize i) groups batch field w ceiling)
    (Bfixed : Fixed B names (S.hostSize i) groups batch field m)
    (owner : ∀z : Row (S.hostSize i) groups batch,self.eval m ((row _ _ _ z).val:Word w)=(z.1.val:Word w))
    (hosts : S.hostSize i<2^w) (date : reset.terminals.commonDepth<2^w) (short : 2^(reset.reset.k-reset.terminals.commonDepth)<2^w)
    (fieldRoom : max (max (reset.reset.k-reset.terminals.commonDepth) (2^n))
      (2^(reset.reset.k-reset.terminals.commonDepth))<2^field)
    (q j : Fin (A).degree) (u : Fin 6) :
    let c:=reset.terminals.commonDepth
    let r:=reset.reset.k-c
    let next:=PackedFlow.Padded.roster (D:=(A).degree) A (oldName input) input.valid.host
    Source (reservationFields E B P (S.hostSize i) maxPorts c r base levels total self q j u)
      (fun v (_:Fin groups)=>paddedValue (b:=field) c r next (oldDepth reset) (oldWidth reset) v q j u) batch m := by
  intro c r next
  apply DescentRotorPeerIssue.broadcast_at B _ m ceiling Broom Bfixed
    (fun v=>paddedValue (b:=field) c r next (oldDepth reset) (oldWidth reset) v q j u)
  intro t
  let tick:Word w:=((row _ _ _ t).val:Word w)
  have peer (j : Fin (A).degree) := peer_id P prior ceiling next m support mounted j t
  have prepared (v : Fin (S.hostSize i)) (live : next t.1 j=some v) :
      (level (.lit c) (depthAt E base (S.hostSize i) levels total (neighborID P j))).eval m tick=((max c (oldDepth reset v):ℕ):Word w) ∧
      (sizeAt E (S.hostSize i) maxPorts j.val base levels total self (neighborID P j)).eval m tick=(oldWidth reset t.1 v:Word w) := by
    obtain ⟨a,b,src,dst,real⟩:=peer_origin t.1 v j live
    have orig:(neighborID P j).eval m tick=((input.vertex b).val:Word w) := by
      simpa only [live,target,Option.elim_some,←dst,Fin.val_castLE] using peer j
    have old : oldDepth reset v=reset.reset.placement.b (reset.frame.host b):=by rw [←dst,oldDepth,oldHost_at];rfl
    have got:=(depth_at_eval E m tick _ ((input.vertex b).castLE input.valid.host) chart orig).trans (accepted.attainedDepth_read E dim m depths depthLegal depthRoom b tick)
    have size:=accepted.size_at_read E dim maxPorts ports hostCount m first depths depthLegal depthRoom bankLegal wordBits
      base levels total a b j real (max_lt (depthFits a) (depthFits b)) (sumFits a b) widthBits output hw hK positive static chart
      tick self _ (by simpa only [←src,Fin.val_castLE] using owner t) orig
    refine ⟨?_,?_⟩
    · rw [old]
      have less := (depthFits b).trans_le (Nat.pow_le_pow_right (n:=2) (by decide) (show levels≤w by omega))
      have out := read_level (.lit c) _ m tick c _ rfl got (max_lt date less)
      apply out.trans
      have csmall : c < 2^w := date
      simp only [max_def, Fin.le_def, Fin.val_cast_of_lt csmall, Fin.val_cast_of_lt less]
      split <;> rfl
    · rw [←src,←dst,oldWidth,oldHost_at,oldHost_at]
      simpa only [Fin.cast_val_eq_self,Option.elim_some] using congrArg (fun n:ℕ=>(n:Word w)) size
  have nonzero : 1<2^w:=lt_of_le_of_lt (Nat.one_le_two_pow) short
  have scalar:=DescentRotorPeerIssue.operandAt_read P c r q j _ _ u m tick (next t.1 q) (next t.1 j)
    (fun v=>max c (oldDepth reset v)) (oldWidth reset t.1) (peer q) (peer j)
    (fun _ lv=>(prepared _ lv).1) (fun _ lv=>(prepared _ lv).2) (fun _=>le_max_left ..) hosts short nonzero
  apply scalar.trans
  cases hq : next t.1 q with
  | none=>simp [paddedValue,hq]
  | some d₀=>
    cases hj : next t.1 j with
    | none=>simp [paddedValue,hq,hj]
    | some v=>
      obtain ⟨a,b,src,dst,_⟩:=peer_origin t.1 v j hj
      have dz : oldDepth reset v≤reset.reset.k:=by rw [←dst,oldDepth,oldHost_at];exact reset.reset.placement.depth _
      have sz : oldWidth reset t.1 v≤2^n:=by rw [←src,←dst,oldWidth,oldHost_at,oldHost_at];exact min_le_left ..
      have rel : max c (oldDepth reset v)-c=oldDepth reset v-c:=by omega
      have relBound : oldDepth reset v-c≤r:=Nat.sub_le_sub_right dz c
      have one : 0<2^r:=Nat.two_pow_pos _
      have yes (t : Bool) : t.toNat≤1:=by cases t <;> decide
      simp only [paddedValue,hq,hj,rel]
      congr 1
      symm
      apply Fin.val_cast_of_lt
      let box:=DescentShortReservationPeer.compare (2^r) v.val d₀.val
      have left : box.first≤2^r:=min_le_right ..
      have right : box.second≤2^r:=min_le_right ..
      change max (max r (2^n)) (2^r) < 2^field at fieldRoom
      have hd : r < 2^field := ((le_max_left r (2^n)).trans (le_max_left _ (2^r))).trans_lt fieldRoom
      have hs : 2^n < 2^field := ((le_max_right r (2^n)).trans (le_max_left _ (2^r))).trans_lt fieldRoom
      have hb : 2^r < 2^field := (le_max_right _ _).trans_lt fieldRoom
      fin_cases u
      · exact relBound.trans_lt hd
      · exact sz.trans_lt hs
      · exact left.trans_lt hb
      · exact right.trans_lt hb
      · exact ((yes box.less).trans one).trans_lt hb
      · exact ((yes box.same).trans one).trans_lt hb

theorem paddedValue_at {b : ℕ} (v : input.V) (q j : Fin (A).degree) (u : Fin 6) :
    let c:=reset.terminals.commonDepth
    let r:=reset.reset.k-c
    let rank:=fun t:input.V=>(input.vertex t).castLE input.valid.host
    let next:=PackedFlow.Padded.roster (D:=(A).degree) A (oldName input) input.valid.host
    paddedValue (b:=b) c r next (oldDepth reset) (oldWidth reset) (rank v) q j u=
      match hostRoster A (input.vertex.trans Fin.valEmbedding) v q, hostRoster A (input.vertex.trans Fin.valEmbedding) v j with
      | some d,some t=>
        let box:=DescentShortReservationPeer.compare (2^r) (input.vertex t).val (input.vertex d).val
        (![reset.reset.placement.b (reset.frame.host t)-c,
          min (reset.terminals.columns.size (reset.frame.host v) (reset.frame.host t)) (2^reset.reset.n),
          box.first,box.second,box.less.toNat,box.same.toNat] u:ℕ)
      | _,_=>0 := by
  intro c r rank next
  unfold paddedValue
  dsimp only [next,rank]
  rw [peer_at (input:=input) v q,peer_at (input:=input) v j]
  cases hq : hostRoster A (input.vertex.trans Fin.valEmbedding) v q <;>
    cases hj : hostRoster A (input.vertex.trans Fin.valEmbedding) v j <;>
    simp only [Option.map_some,Option.map_none,oldDepth,oldWidth,oldHost_at,Option.elim_some,
      reset.dimension,min_comm]; rfl


end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
