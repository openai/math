import OAI.Hierarchy.DescentResetRepackedInputs

namespace OAI
/-! # The split flags, old fields and shared cutoff tables on one native memory -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSixParty.PackedFlow DescentGL DescentGLPacked.BankImage DescentColonies DescentPackedColony
open DescentSIMDLookup DescentIssuedFallbackPanel DescentPackedColony.Phase ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (S : StencilBook) {w : ℕ}

/-- Real port ordinals occupy the first declared sockets. Coordinate planes start after the full
public port aperture, including its unused tail. -/
def chartIndex (i : Channels.Index S.degree S.m) : Channels.Index S.maxPorts S.m :=
  finSumFinEquiv (match finSumFinEquiv.symm i with
    | .inl j => Sum.inl ⟨j.val % (1+S.maxPorts),Nat.mod_lt _ (by omega)⟩
    | .inr d => Sum.inr d)

theorem chart_load : S.chartIndex (Channels.loadIndex S.degree S.m)=Channels.loadIndex S.maxPorts S.m := by
  simp [chartIndex,Channels.loadIndex,finSumFinEquiv,Fin.ext_iff]

theorem chart_flow (h : S.degree≤S.maxPorts) (j : Fin S.degree) :
    S.chartIndex (Channels.flowIndex S.m j)=Channels.flowIndex S.m (j.castLE h) := by
  have idx:j.val+1<1+S.maxPorts:=by have :=j.isLt;omega
  simp [chartIndex,Channels.flowIndex,finSumFinEquiv,Fin.ext_iff,Nat.add_comm]
  exact j.isLt.trans_le h

theorem chart_plane (d : Fin S.m) :
    S.chartIndex (Channels.planeIndex S.degree d)=Channels.planeIndex S.maxPorts d := by
  simp [chartIndex,Channels.planeIndex]

def bankAt (out : ℕ) (i : Channels.Index S.degree S.m) :=
  Channels.shortBank out S.hosts (2^S.c) S.M (S.chartIndex i)
def weightBank (out : ℕ) := S.bankAt out (Channels.loadIndex S.degree S.m)
def layer (base out : ℕ) (roster : Bank) := S.split base roster (S.weightBank out)
def chosen (base out : ℕ) (roster : Bank) := (S.layer base out roster).issued S.degree S.r S.b S.M
def castImage (base : ℕ) : Arena.Image w := Channels.narrowImage (S.narrow base).base S.b S.r S.M

def scalarProgram (base K scale bound w : ℕ) :=
  let L:=S.header base
  ((L.chart (w:=w)).program.seq (L.cutoff S.levels S.total K scale bound).program).seq
    (S.castImage (w:=w) base).program

def scalarTime (base : ℕ) := (8+10*((S.narrow base).base-(S.header base).origin))+
  (4+10*(S.castImage (w:=0) base).length)

def splitProgram (base out : ℕ) (roster : Bank) (D cap w : ℕ) :=
  (splitImage (S.layer base out roster) S.degree S.hosts S.c S.r S.b S.M D cap w).program.seq
    (ProtocolRAM.program w (passes (S.chosen base out roster) S.hosts (2^S.c) S.M S.r))

def splitTime (base out : ℕ) (roster : Bank) (D cap : ℕ) :=
  (4+10*(splitImage (S.layer base out roster) S.degree S.hosts S.c S.r S.b S.M D cap 0).length)+
    clock (passes (S.chosen base out roster) S.hosts (2^S.c) S.M S.r)

theorem scalar_issue (base K scale bound : ℕ) (mem : Memory w) (safe : S.afterHeader base<2^w) :
    let L:=S.header base
    ∃dst,(S.scalarProgram base K scale bound w).Exec mem dst (S.scalarTime base) ∧
      L.chart.Resident dst ∧ Cutoff.Resident L.stop S.levels S.total K scale bound dst ∧
      (S.castImage base).Resident dst ∧
      (∀z,z<L.origin ∨ S.afterHeader base≤z→dst z=mem z) ∧ CheapCode (S.scalarProgram base K scale bound w) := by
  let L:=S.header base
  let N:=S.narrow base
  let I:Arena.Image w:=S.castImage base
  have l:L.origin≤L.stop:=by dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,
    PortLevels.AddressBook.depth,PortLevels.AddressBook.pos];omega
  have e:L.stop≤N.base:=(Nat.le_add_right L.stop _).trans (Nat.le_add_right ..)
  have endAt:I.stop=S.afterHeader base:=rfl
  have ni:I.low=N.base:=rfl
  have n:N.base≤S.afterHeader base:=Nat.le_add_right ..
  have fit:I.low+I.length<2^w:=by unfold Arena.Image.length;omega
  obtain ⟨head,positions,cuts,frame,cheap⟩:=L.issue S.levels S.total K scale bound mem (n.trans_lt safe)
  obtain ⟨narrow,word,keep⟩:=I.issue _ fit
  refine ⟨_,head.then narrow,?_,⟨?_,?_⟩,word,?_,cheap_seq cheap I.hardware.1⟩
  · intro z lo hi
    exact (keep z (.inl (hi.trans_le e))).trans (positions z lo hi)
  · intro j hj
    apply (keep _ (Or.inl ?_)).trans (cuts.1 j hj)
    exact (Nat.add_lt_add_left hj L.stop).trans_le (Nat.le_add_right ..)
  · intro j hj z hz
    apply (keep _ (Or.inl ?_)).trans (cuts.2 j hj z hz)
    have p:=Nat.mul_le_mul_right (2^S.total) hj
    rw [Nat.succ_mul,←pow_add] at p
    change L.stop+2^S.levels+(2^S.total*j+z)<L.stop+2^S.levels+2^(S.levels+S.total)
    rw [Nat.mul_comm (2^S.total) j]
    omega
  · intro z bound
    rcases bound with low|high
    · exact (keep _ (.inl (low.trans_le (l.trans e)))).trans (frame _ (.inl low))
    · exact (keep _ (.inr (by simpa only [endAt] using high))).trans (frame _ (.inr (n.trans high)))

theorem layer_room (base out : ℕ) (roster : Bank)
    (ends : out+((1+S.maxPorts)+S.m)*S.hosts*chunks (2^S.c) S.M≤base)
    (top : roster.Fits w (S.start base)) (ports : S.hosts*S.degree≤roster.size)
    (fit : (S.header base).origin<2^w) :
    Frame.Room (S.layer base out roster) S.hosts (2^S.c) S.degree S.r S.b S.M w := by
  let A:=S.layer base out roster
  have land:=S.split_end base roster (S.weightBank out)
  have room:A.fresh S.degree S.r+(S.r+1)*A.page<2^w:=land.trans_lt fit
  have pos:A.origin≤A.fresh S.degree S.r:=Nat.le_add_right ..
  have headroom : S.start base<2^w:=by change A.origin<2^w;omega
  have storage (i : Channels.Index S.maxPorts S.m) := Channels.short_fits (c:=S.c) (M:=S.M) out i
    (show out+((1+S.maxPorts)+S.m)*S.hosts*chunks (2^S.c) S.M+2^(Nat.clog 2 S.rows)≤S.start base from
      Nat.add_le_add_right ends _) headroom
  obtain ⟨sites,cells,tabs⟩:=Frame.enough S.hosts (2^S.c) S.r S.b S.M
  have power {e : ℕ} (le:e≤DescentPackedColony.unit S.r S.b) : 2^(e*S.M)≤A.page:=
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right _ le)).trans tabs
  exact ⟨sites,cells,power ((Nat.le_add_right _ _).trans (le_max_left ..)),power (le_max_right ..),
    power (le_max_left ..),top,ports,storage _,Nat.le_pow_clog (by decide) _,room⟩

theorem after_splits (small : S.c≤S.m) (base out : ℕ) (roster : Bank) (D cap K scale bound : ℕ)
    (rs : Fin S.hosts→Fin S.degree→Option (Fin S.hosts)) (loads : Fin S.hosts→Block S.m→Cell S.b)
    (L : DescentGL.Layout S.m) (mem : Memory w) (endChip : out+((1+S.maxPorts)+S.m)*S.rows≤base)
    (top : roster.Fits w (S.start base)) (ports : S.hosts*S.degree≤roster.size)
    (safe : S.afterHeader base<2^w)
    (peers : ∀v j,mem (roster.base+(v.val*S.degree+j.val))=(target (rs v j):Word w))
    (word : Reads (S.weightBank out) (Channels.blockValues (h:=S.m) (l:=0) small loads L) S.M mem) :
    let A:=S.layer base out roster
    let ly:=S.chosen base out roster
    let H:=S.header base
    let rows:=fun hi=>Scan.build (incoming (DescentPackedColony.peers rs))
      (fun v x=>(loads v ((rearrange L).symm (join small hi x))).val) D cap S.r
    let program:=(S.splitProgram base out roster D cap w).seq (S.scalarProgram base K scale bound w)
    ∃dst,program.Exec mem dst (S.splitTime base out roster D cap+S.scalarTime base) ∧ CheapCode program ∧
      Reads (ly.source S.r) (fun v hi=>cache (rows hi) v) S.M dst ∧ Mounted ly.ports rs dst (2^S.c) S.M ∧
      H.chart.Resident dst ∧ Cutoff.Resident H.stop S.levels S.total K scale bound dst ∧
      (S.castImage base).Resident dst ∧ (∀z,z<A.origin ∨ S.afterHeader base≤z→dst z=mem z) := by
  let A:=S.layer base out roster
  let ly:=S.chosen base out roster
  let H:=S.header base
  have he:H.origin≤H.stop:=by dsimp [PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,
    PortLevels.AddressBook.depth,PortLevels.AddressBook.pos];omega
  have gone:H.stop≤S.afterHeader base:=((Nat.le_add_right H.stop _).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have clockRoom:=S.layer_room base out roster (by simpa only [rows,Nat.mul_assoc,Nat.add_assoc] using endChip)
    top ports ((he.trans gone).trans_lt safe)
  have ready:=dated_splits_ports (h:=S.m) (l:=0) small A clockRoom rs (fun v x=>(loads v x).val) L D cap mem
    (fun v x=>(loads v x).isLt) peers (by
      change Reads (S.weightBank out) _ _ _
      unfold Channels.blockValues at word
      simpa only [Fin.cast_val_eq_self] using word)
  obtain ⟨mid,native,cheap,digits,_,keep,mounted⟩:=ready
  obtain ⟨dst,scalar,static,cut,casts,frame,cheap'⟩:=S.scalar_issue base K scale bound mid safe
  have land:=S.split_end base roster (S.weightBank out)
  change A.fresh S.degree S.r+(S.r+1)*A.page=H.origin at land
  have hi:A.fresh S.degree S.r+S.r*A.page≤H.origin:=by rw [←land,Nat.succ_mul];omega
  have pre:A.origin≤A.fresh S.degree S.r:=Nat.le_add_right ..
  have pad:A.fresh S.degree S.r≤H.origin:=by omega
  let old:=Frame.low A clockRoom
  have frozen (z) (use:z<ly.fresh):dst z=mid z:=frame _ (.inl (use.trans_le pad))
  have rowSize : S.rows≤A.page:=clockRoom.cells
  have areas (p:Row S.hosts (2^S.c) S.M) : (ly.source S.r).base+(DescentSIMDLookup.row _ _ _ p).val<H.origin:=by
    have length:=(DescentSIMDLookup.row S.hosts (2^S.c) S.M p).isLt
    have cell_lt : (DescentSIMDLookup.row S.hosts (2^S.c) S.M p).val < A.page := length.trans_le clockRoom.cells
    cases eqn:S.r with
    | zero=>
      have init:=Frame.slot_before A (.initial : Frame.Slot S.degree S.r)
      change ((A.issued S.degree S.r S.b S.M).source 0).base+_ < H.origin
      rw [eqn]
      change (A.atSlot (.initial : Frame.Slot S.degree 0)).base+_ < H.origin
      rw [eqn] at init pad
      exact (Nat.add_lt_add_left cell_lt _).trans_le (init.trans pad)
    | succ j=>
      change ((A.issued S.degree S.r S.b S.M).source (j+1)).base+_ < H.origin
      rw [eqn]
      change A.fresh S.degree (j+1)+j*A.page+_ < H.origin
      rw [eqn] at land
      have le:j*A.page≤(j+1+1)*A.page:=Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul,Nat.succ_mul] at land
      omega
  refine ⟨dst,native.then scalar,cheap_seq cheap cheap',?_,?_,static,cut,casts,?_⟩
  · intro p
    exact (frame _ (.inl (areas p))).trans (digits p)
  · constructor
    · intro p i
      exact (frozen _ ((Nat.add_lt_add_left (DescentSIMDLookup.row S.hosts (2^S.c) S.M p).isLt _).trans_le (old.ids i))).trans (mounted.ids p i)
    · intro v j
      have u:=Nat.mul_le_mul_right S.degree v.isLt
      rw [Nat.succ_mul] at u
      exact (frozen _ ((Nat.add_lt_add_left ((Nat.add_lt_add_left j.isLt _).trans_le u) _).trans_le old.roster)).trans (mounted.roster v j)
    · intro v
      exact (frozen _ ((Nat.add_lt_add_left v.isLt _).trans_le old.offsets)).trans (mounted.offsets v)
    · intro p
      exact (frozen _ ((Nat.add_lt_add_left (DescentSIMDLookup.row S.hosts (2^S.c) S.M p).isLt _).trans_le old.chunk)).trans (mounted.chunks p)
  · intro z bound
    rcases bound with lo|upper
    · exact (frame _ (.inl (lo.trans_le (pre.trans pad)))).trans (keep _ (.inl lo))
    · exact (frame _ (.inr upper)).trans (keep _ (.inr (hi.trans ((he.trans gone).trans upper))))

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

end OAI
