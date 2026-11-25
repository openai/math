import OAI.Hierarchy.DescentPhysicalResetStencil
import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentRotorReservationSources

namespace OAI
/-! # The reservation lookup in the installed root pages -/
namespace Hierarchy.DescentReservationHeader
open ProtocolRAM DescentPlainTerminal.Suffix.Cutoff Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

theorem entries_read {w} (m : Memory w) (base levels total K scale Y : ℕ)
    (seen : ∀j<entries levels total,m (base+j)=(entry levels total K scale Y j:Word w)) :
    Resident base levels total K scale Y m := by
  constructor
  · intro j hj
    simpa [entry,hj] using seen j (hj.trans_le (Nat.le_add_right ..))
  · intro j hj z hz
    have h:=index_lt levels total j z hj hz
    have ok:=seen (2^levels+(2^total*j+z)) (Nat.add_lt_add_left h _)
    simpa [entry,not_lt_of_ge (Nat.le_add_right ..),Nat.add_assoc,Nat.mul_add_div (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hz,Nat.mul_add_mod,Nat.mod_eq_of_lt hz] using ok
end
end Hierarchy.DescentReservationHeader

namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentReservationHeader DescentGL DescentColonies DescentSixParty DescentSixParty.Chronology DescentCompiler
open ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)

/-- The root book's own mounted second page contains all reservation bytes. -/
theorem prepared_reservation_table (space : a.PreparedFits b) (page : RootPage r (2^n)) (mem : Memory w)
    (pitch dim high levels total K₀ scale Y : ℕ) (size : b.extraSize=reserveEntries H levels total)
    (data : b.extraWord=reserveEntry H pitch dim high levels total K₀ scale Y) :
    let base:=b.auxAt a.projectionEnd H (2^c) M
    Resident base levels total K₀ scale Y (a.preparedMid b space mem) ∧
      Strides base H pitch dim high levels total (a.headerEnd b) (a.preparedMid b space mem) := by
  intro base
  let cells:=entries levels total
  let pad:=span H
  have positive : 0<pad:=Nat.two_pow_pos _
  have host : H≤pad:=Nat.le_pow_clog (by decide) _
  have count : 2≤Fintype.card (RootPage r (2^n)):=by
    let left : RootPage r (2^n):=(false,page.2)
    let right : RootPage r (2^n):=(true,page.2)
    have l:=(rootIndex _ _ left).isLt
    have r₀:=(rootIndex _ _ right).isLt
    by_contra! fewer
    have eqn:(rootIndex _ _ left).val=(rootIndex _ _ right).val:=by omega
    have bad:=congrArg Prod.fst ((rootIndex _ _).injective (Fin.ext eqn))
    contradiction
  have tw:=Nat.mul_le_mul_right (b.width H (2^c) M) count
  have two: b.width H (2^c) M=b.payloadWidth H (2^c) M+b.sharedWords M:=rfl
  have many:b.extraSize≤b.sharedWords M:=le_max_right ..
  have cap : base+(cells+pad+pad)≤a.headerEnd b:=by
    change b.repeatEnd a.projectionEnd H (2^c) M+b.width H (2^c) M+b.payloadWidth H (2^c) M+(cells+pad+pad)≤
      b.repeatEnd a.projectionEnd H (2^c) M+Fintype.card (RootPage r (2^n))*b.width H (2^c) M
    change b.extraSize=cells+pad+pad at size
    omega
  have read (j : ℕ) (hj : j<cells+pad+pad) :
      a.preparedMid b space mem (base+j)=(reserveEntry H pitch dim high levels total K₀ scale Y j:Word w):=by
    rw [←data];exact a.prepared_extra b space page mem j (size.symm ▸ hj)
  have roof:=space.literals
  constructor
  · apply entries_read
    intro j h
    simpa only [reserveEntry,ite_eq_left h] using read j (by change j<cells at h;omega)
  · refine ⟨?_,?_,?_,?_⟩
    · change 0<pad ∧ pad<2^w ∧ base+cells+pad≤a.headerEnd b
      omega
    · change 0<pad ∧ pad<2^w ∧ base+(cells+pad)+pad≤a.headerEnd b
      omega
    · intro v
      have hv:=v.isLt.trans_le host
      have got:=read (cells+v.val) (by omega)
      change a.preparedMid b space mem (base+cells+v.val)=_
      rw [Nat.add_assoc]
      have e₁ : ¬(cells+v.val < entries levels total) := by change ¬(cells+v.val<cells); omega
      have e₂ : cells+v.val < entries levels total + span H := Nat.add_lt_add_left hv cells
      simpa only [reserveEntry,ite_eq_right e₁,ite_eq_left e₂,cells,Nat.add_sub_cancel_left] using got
    · intro v
      have hv:=v.isLt.trans_le host
      have got:=read (cells+pad+v.val) (by omega)
      change a.preparedMid b space mem (base+(cells+pad)+v.val)=_
      rw [Nat.add_assoc]
      have e₁ : ¬(cells+pad+v.val < entries levels total) := by change ¬(cells+pad+v.val<cells); omega
      have e₂ : ¬(cells+pad+v.val < entries levels total + span H) := by
        change ¬(cells+pad+v.val < cells+pad); omega
      simpa only [reserveEntry,ite_eq_right e₁,ite_eq_right e₂,cells,pad,Nat.add_sub_cancel_left] using got

/-- Only the cut and scalar repetition tables of this header are accessed by a rotor field. -/
theorem prepared_broadcast_room_of_top (top : a.headerEnd b<2^w) (page : RootPage r (2^n)) :
    DescentRotorPeerIssue.BroadcastRoom (b.rankHeader a.projectionEnd H (2^c) M page)
      H (2^c) M field w (a.headerEnd b) := by
  let base:=b.scalarEnd a.projectionEnd H
  let stride:=DescentSharedLeafLookup.Public.stride H (2^c) M
  let lanes:=2^Nat.clog 2 ((M+1)*2^field)
  have bound : base+2*stride+lanes≤a.headerEnd b:=(b.limits a.projectionEnd H (2^c) M).2.2
  have pos : 0<stride:=Nat.two_pow_pos _
  have live : 0<lanes:=Nat.two_pow_pos _
  constructor
  · change 0<stride ∧ stride<2^w ∧ (base+stride)+stride≤a.headerEnd b
    omega
  · change 0<lanes ∧ lanes<2^w ∧ (base+2*stride)+lanes≤a.headerEnd b
    omega
  · exact Nat.le_pow_clog (by decide) _
  · exact Nat.le_pow_clog (by decide) _

theorem prepared_broadcast_room (space : a.PreparedFits b) (page : RootPage r (2^n)) :
    DescentRotorPeerIssue.BroadcastRoom (b.rankHeader a.projectionEnd H (2^c) M page)
      H (2^c) M field w (a.headerEnd b) :=
  a.prepared_broadcast_room_of_top b space.literals page

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentGL DescentColonies DescentCompiler DescentMeasuredWeights DescentMeasuredHeader DescentPackedWalsh
open DescentSixParty.Chronology
open ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} {E : EstimatorArena}

/-- Only the two original estimator banks are needed after the stencil. -/
theorem StencilReservationWords.retain {w base maxPorts : ℕ} {dim : E.dim=reset.reset.k} {ports : D≤ maxPorts}
    {old m : Memory w} (prior : StencilReservationWords (reset:=reset) E dim maxPorts ports old)
    (floor : E.endAddress≤base) (fit : E.Fits w) (same : ∀x<base,m x=old x) :
    StencilReservationWords (reset:=reset) E dim maxPorts ports m := by
  obtain ⟨hostCount,totals,depths⟩:=prior
  refine ⟨hostCount,E.retained_totals old m _ floor same totals,?_⟩
  intro v
  exact (same _ ((depth_before_end E fit (input.vertex v).val (S.hostSize i) maxPorts
    ((input.vertex v).isLt.trans_le input.valid.host) hostCount).trans_le floor)).trans (depths v)

open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentPackedColony DescentPackedZip
open DescentSharedLeafLookup DescentReservationHeader ThreeFlat.RAM PhysicalProcedure
set_option quotPrecheck false
local notation "A" => input.placement
local notation "HP" => S.hostSize i
local notation "cc" => reset.terminals.commonDepth
local notation "inc" => S.resetInputDigits ctl.base ctl.radix i
local notation "fee" => quota S.rounds
local notation "scale" => 2^f*(wire*(z*G.b)*(A).cap)
local notation "levels" => Nat.clog 2 (E.dim+2)
local notation "total" => E.dim+S.censusBits p

/-- The original scalar depth of one occupied host at the prepared step, before packing or
subtracting the common level. The two actual address reads are independent of the chosen host. -/
theorem prepared_attained_depth {cap N G₀ K₀ R batch h₀ l t field Ht w : ℕ}
    (accepted : reset.Recorded p) (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (a : Receiver (A).degree cap N n (E.dim-cc) cc HP G₀ K₀ R batch h₀ l t field Ht w)
    (b : RootBook n (E.dim-cc) (A).degree (2^(E.dim-cc)) cap field) (space : a.PreparedFits b)
    (page : RootPage (E.dim-cc) (2^n)) (mem : Memory w)
    (prior : StencilReservationWords (reset:=reset) E dim maxPorts ports mem)
    (safe : E.Fits w) (before : E.endAddress≤a.origin)
    (size : b.extraSize=reserveEntries HP levels total)
    (data : b.extraWord=reserveEntry HP maxPorts E.dim E.high levels total fee scale (2^n))
    (depthLegal : E.depthRows.Fits w (a.headerEnd b)) (v : input.V) (self : Expr) (tick : Word w)
    (owner : self.eval (a.preparedMid b space mem) tick=((input.vertex v).val:Word w)) :
    let base:=b.auxAt a.projectionEnd HP (2^cc) batch
    (depthAt E base HP levels total self).eval (a.preparedMid b space mem) tick=
      (reset.reset.placement.b (reset.frame.host v):Word w) := by
  intro base
  obtain ⟨hh,_,depth⟩:=prior.retain before safe (a.prepared_lower b space mem)
  have book:=a.prepared_reservation_table b space page mem maxPorts E.dim E.high levels total fee scale (2^n) size data
  let ord:=(input.vertex v).castLE input.valid.host
  have cap : ord.val*(E.dim+1)<E.depthRows.size := by
    apply ((Nat.mul_lt_mul_of_pos_right ord.isLt (Nat.succ_pos E.dim)).trans_le _).trans_le safe.hostRows.1
    rw [hh];exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  rw [depth_at_eval E _ tick self ord book.2 owner]
  change E.depthRows.read _ (((input.vertex v).val*(E.dim+1):ℕ):Word w)=_
  exact (bank_read E.depthRows (a.preparedMid b space mem) cap depthLegal).trans
    ((depth v).trans (congrArg (fun z : ℕ => (z : Word w)) (accepted.measured.depth v).symm))

/-- The actual second root page and the original estimator banks meet on the single
post-memory produced by the signed-prefix reader and private root header installation. -/
theorem prepared_reservation_sources {cap N G₀ K₀ R batch h₀ l t field Ht w r : ℕ}
    (accepted : reset.Recorded p) (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (a : Receiver (A).degree cap N n r cc HP G₀ K₀ R batch h₀ l t field Ht w)
    (b : RootBook n r (A).degree (2^r) cap field) (space : a.PreparedFits b)
    (page : RootPage r (2^n)) (mem : Memory w)
    (prior : StencilReservationWords (reset:=reset) E dim maxPorts ports mem)
    (safe : E.Fits w) (before : E.endAddress≤a.origin)
    (size : b.extraSize=reserveEntries HP levels total)
    (data : b.extraWord=reserveEntry HP maxPorts E.dim E.high levels total fee scale (2^n))
    (depthLegal : E.depthRows.Fits w (a.headerEnd b))
    (bankLegal : (firstContactBank E).Fits w (a.headerEnd b))
    (wordBits : E.precision≤w) (widthBits : levels+total≤w) (output : n<w)
    (hw : 0<wire) (positive : 0<wire*(z*G.b)*(A).cap)
    (census : (A).wire*((A).z*G.b)*(A).cap<2^(S.censusBits p))
    (P : Ports (A).degree) (old : Bank) (self : Expr)
    (support : Accessible P old HP (2^cc) batch w (a.headerEnd b))
    (mounted : Mounted P (PackedFlow.Padded.roster A (oldName input) input.valid.host)
      (a.preparedMid b space mem) (2^cc) batch)
    (owner : ∀z : Row HP (2^cc) batch,self.eval (a.preparedMid b space mem) ((row _ _ _ z).val:Word w)=(z.1.val:Word w))
    (hosts : HP<2^w) (date : cc<2^w) (short : 2^(E.dim-cc)<2^w)
    (fieldRoom : max (max (E.dim-cc) (2^n)) (2^(E.dim-cc))<2^field)
    (q j : Fin (A).degree) (u : Fin 6) (rank : r=E.dim-cc := by rfl) :
    let table:=b.auxAt a.projectionEnd HP (2^cc) batch
    let B:=b.rankHeader a.projectionEnd HP (2^cc) batch page
    let next:=PackedFlow.Padded.roster (D:=(A).degree) A (oldName input) input.valid.host
    Source (reservationFields E B P HP maxPorts cc (E.dim-cc) table levels total self q j u)
      (fun v (_:Fin (2^cc))=>paddedValue (b:=field) cc (E.dim-cc) next
        (oldDepth reset) (oldWidth reset) v q j u) batch (a.preparedMid b space mem) := by
  subst r
  intro table B next
  let mid:=a.preparedMid b space mem
  obtain ⟨hh,first,depths⟩:=prior.retain before safe (a.prepared_lower b space mem)
  let digits:=(Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans inc
  have real (v:input.V) :
      mid (E.depthRows.base+(input.vertex v).val*(E.dim+1))=
        (((A).mixerHeader digits ((A).numberedHeader digits input.vertex).site).depth A f v:Word w):=
    (depths v).trans (congrArg (fun z:ℕ=>(z:Word w))
      (cast_inputs A (dim.trans reset.keyWidth) inc input.vertex f v v).1.symm)
  have storage (v:input.V) : (input.vertex v).val*(E.dim+1)<E.depthRows.size:=by
    have left:=Nat.mul_lt_mul_of_pos_right ((input.vertex v).isLt.trans_le input.valid.host) (Nat.succ_pos E.dim)
    apply (left.trans_le _).trans_le safe.hostRows.1
    rw [hh]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  have levelsRoom (v:input.V) : reset.reset.placement.b (reset.frame.host v)<2^levels:=
    ((reset.reset.placement.depth _).trans_eq dim.symm).trans_lt
      ((by omega : E.dim<E.dim+2).trans_le (Nat.le_pow_clog (by decide) _))
  have sums (v t:input.V) : (∑x,(A).resetFlow inc v t x)<2^total:=by
    rw [dim,reset.keyWidth]
    apply DescentPlainTerminal.Suffix.Cutoff.total_fits
    intro x
    exact ((A).reset_words_at S input.valid inc v t x).1.trans_lt
      (((A).reset_words_at S input.valid inc v t x).2.trans_lt census)
  have tables:=a.prepared_reservation_table b space page mem maxPorts E.dim E.high levels total fee scale (2^n) size data
  have native:=accepted.reservation_sources E dim maxPorts ports hh mid first real depthLegal storage bankLegal wordBits
    table levels total levelsRoom sums widthBits output hw (by unfold quota;omega) positive
    tables.1 tables.2 P old B self support mounted
    (a.prepared_broadcast_room b space page) (a.prepared_shared b space mem page).2.2
    owner hosts date (by simpa only [dim] using short) (by simpa only [dim] using fieldRoom) q j u
  simpa only [dim] using native


end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
