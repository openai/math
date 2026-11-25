import OAI.Hierarchy.TaggedWideCalendarPartyPins

namespace OAI
/-! # Evaluating a concrete packed party from the original signed and installed fields -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.WireTelescope.PassMatrix.PartyPins
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open ThreeFlat.Diagonal.MotifOuterTerms
open Tagged Probe ChosenPackets RowRouting TurnShelf CalendarTape AdaptiveProbe
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F V : Type} [Field F] [Fintype V] {S N r D cap deg M e p digits W n count : ℕ}
    (Q : Placed F S) (c : Histogram (Fin Q.data.terms) r) {phys : Fin N→Chord S}
    (R : RowRouting (Row.packet Q r) phys) (i : Fin Q.sites) (tap : (portGraph Q.sites).Port i)
local notation "s" => Q.place i
local notation "roles" => Fintype.card R.Roles
local notation "RS" => Fin roles×Bool
local notation "slot" => Fin (roles*3)
local notation "oldEnds" => Installs.starts (source:=R.source) R.order
local notation "rs" => R.install.steps R.order
local notation "weights" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad rs weights
local notation "preWidth" => Q.data.inputWidths r
local notation "outWidth" => Q.data.outputWidths c+Q.graph.chordWidths (fun _=>r*Q.data.selectorBits)
local notation "tapWidth" => Q.graph.chordWidths (fun _=>r*Q.data.selectorBits)
local notation "slab" => (2^e)
local notation "MiddleField" => PacketTurns.MiddleField roles
variable (localEnds : Fin (Fintype.card R.Roles)→Chord Q.sites)
    (fit : r*Q.data.selectorBits≤(Q.graph.chordWidths (fun _=>r*Q.data.selectorBits)) tap.val.1)
    (old : ℕ) (le : Fintype.card R.Roles≤M) (read : ℕ→ℕ→V⊕Bool) (v : V→Bool)
    (before after : Fin D×Fin cap→Bool)
local notation "env" => Sum.elim (Sum.elim v before) after
local notation "val" => fun a b=>Sum.elim v id (read a b)
local notation "midCol" f => middleStart old M D Q.sites+(PacketTurns.middleNumber M (PacketTurns.Operands.middleLift le f)).val
variable (rest : Widths S) (gs : Fin n→Widths S) (pick : Fin n)
local notation "tot" => fun q : (portGraph S).Port s=>(rest+∑j,gs j) q.val.1
variable (parts : PassiveWindow.Parts ((portGraph S).Port (Q.place i)) (Fin D) cap
      (fun q=>(rest+∑j,gs j) q.val.1))
    (oldFit : ∀a,Installs.numbered R.order (R.bits c) a≤2^e)
local notation "oi" => Middle.parts R c s slab oldFit

omit [Fintype V] in
private theorem fromPooled (x : V⊕Bool) :
    Sum.elim env id (host (D:=D) (width:=cap) x)=Sum.elim v id x := by
  cases x <;>rfl

omit [Fintype V] in
/-- Read every signed intermediate operand from the archived block emitted
by the native packet. A true width, role mark, pooled source length and
oriented head all use the same actual processing memory. -/
theorem ballot_middle (o : PacketTurns.Operands fun a=>(rs a).length)
    (mem : Memory W) (arg : Word W) (party : Expr)
    (geom : PacketTurns.Reads oldEnds phys rs weights o mem arg)
    (here : party.eval mem arg=((s).val:Word W)) (siteFit : S≤2^W)
    (rowFit : ∀a,installedWidths oldEnds weights (oldEnds a)≤ slab) (native : slab<2^W)
    (posted : ∀f : MiddleField,∀b,val (midCol f) b=
      ((o.middleFields M party (PacketTurns.middleNumber M (PacketTurns.Operands.middleLift le f))).eval mem arg).val.testBit b) :
    (∀a b,val (midCol (.inl (a,if b then 2 else 1))) 0=decide ((rowGraph oldEnds).vertex a b=s)) ∧
    (∀a (j:Fin (e+1)),val (midCol (.inl (a,0))) j.val=(weights a).testBit j.val) ∧
    (∀u q j,val (midCol (.inr (u,q))) j.val=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.sizeAt oi u q)) j) ∧
    (∀u j,val (midCol (.inl (u.1,3))) j.val=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.head oi u true)) j) ∧
    (∀u (j:Fin (e+1)),val (midCol (.inl (u.1,if u.2 then 5 else 4))) j.val=
      (ChordAperture.room oi u).testBit j.val) := by
  have numerical:=PacketTurns.Operands.middleFields_read oldEnds phys rs weights o mem arg geom siteFit
    party s here M le
  have allFields:=PacketTurns.Operands.gather_field_read (R:=R) (c:=c) («s»:=s) (party:=party) (fit:=siteFit)
    (atSite:=here) (es:=phys) (walk:=rs) (fields:=o) (receipt:=geom) (M:=M) (le:=le)
    (cap:=slab) (fits:=oldFit) (allRoom:=rowFit)
  have one : 1<2^W := (show 1≤ slab from Nat.one_le_two_pow).trans_lt native
  have readBit (f : MiddleField) (b x : ℕ)
      (stored : (o.middleFields M party (PacketTurns.middleNumber M (PacketTurns.Operands.middleLift le f))).eval mem arg=(x:Word W))
      (small : x<2^W) : val (midCol f) b=x.testBit b := by
    exact (posted f b).trans ((congrArg (fun w : Word W=>w.val.testBit b) stored).trans
      (congrArg (fun y : ℕ=>y.testBit b) (Fin.val_cast_of_lt small)))
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a b
    let test := (portGraph S).vertex (oldEnds a) b=s
    have mark : PacketTurns.Operands.middleValues oldEnds weights s (.inl (a,if b then 2 else 1))=
        (if test then 1 else 0) := by cases b <;> rfl
    have small : (if test then 1 else 0)<2^W := by split <;> omega
    have same : (rowGraph oldEnds).vertex a b=(portGraph S).vertex (oldEnds a) b := by cases b <;> rfl
    rw [same]
    refine (readBit _ 0 _ ((numerical _).trans (congrArg (fun x : ℕ=>(x:Word W)) mark)) small).trans ?_
    change (if test then 1 else 0 : ℕ).testBit 0=decide test
    by_cases hit : test <;> simp [hit]
  · intro a j
    rw [posted,numerical]
    change ((weights a:Word W).val.testBit j.val)=_
    simp [Fin.val_natCast,Nat.mod_eq_of_lt ((oldFit a).trans_lt native)]
  · intro u q j
    have small:=(Nat.le_of_lt_succ (ChordAperture.sizeAt oi u q).isLt).trans_lt native
    exact readBit (.inr (u,q)) j.val _ (allFields.1 u q) small
  · intro u j
    have small:=(Nat.le_of_lt_succ (ChordAperture.head oi u true).isLt).trans_lt native
    exact readBit (.inl (u.1,3)) j.val _ (allFields.2.1 u) small
  · intro u j
    have bound : ChordAperture.room oi u≤ slab :=by
      rw [Middle.room_fields]
      split
      · have shape := (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)
        exact (congrArg (fun v : Widths S=>v (oldEnds u.1)) shape).symm.le.trans (rowFit u.1)
      · exact Nat.zero_le _
    exact readBit (.inl (u.1,if u.2 then 5 else 4)) j.val _ (allFields.2.2 u) (bound.trans_lt native)

/-- The numerical premises identify three genuine groups of data: the selected
original neighbor, the native intermediate rows, and the installed five-column turn. -/
theorem circuit_read (shape : gs pick=R.post c) (away : ∀u,u≠pick→Subsingleton (State (gs u) s))
    (x : State (Q.wants r) s) (z : State (rest+∑j,gs j) s)
    (short : ∀a,(rs a).length≤2) (turns : Fin count≃Positions rs)
    (top : ∀q,tot q≤cap) (sectors : roles*2+D<2^p)
    (chordFit : ∀a,installedWidths phys mass (phys a)≤ slab) (live : ∀a,weights a<2^W)
    (o : PacketTurns.Operands fun a=>(rs a).length) (mem : Memory W) (arg : Word W)
    (party : Expr) (len nbr : Fin D→Expr) (here : party.eval mem arg=((s).val:Word W))
    (geom : PacketTurns.Reads oldEnds phys rs weights o mem arg) (sites : S≤2^W) (rows : N≤2^W)
    (mounted : PacketTurns.NeighborReads mem arg parts len nbr)
    (cpu : ∀(t:slot) (f:Control p e),val (old+(finProdFinEquiv (t,(projection f).1)).val) (projection f).2=
      (((o.column (o.gatheredWords R.ordinal len nbr) party (finProdFinEquiv (t,(projection f).1))).eval mem arg).val.testBit (projection f).2))
    (post : ∀q j,after (q,j)=ChordAperture.canonical parts (fun p k=>(z p).val.testBit k) q j)
    (roleBits : 2^p≤2^W) (laneBits : slab≤2^W)
    (aligned : ∀a,oldEnds a=Probe.physicalChord Q.place (localEnds a))
    (sizeFit : ∀q : (portGraph S).Port s,Q.offers c q.val.1≤ slab)
    (roomFit : ∀a,ChordAperture.room oi a<2^(e+1))
    (sides : ∀a b,val (midCol (.inl (a,if b then 2 else 1))) 0=decide ((rowGraph oldEnds).vertex a b=s))
    (amount : ∀a (j:Fin (e+1)),val (midCol (.inl (a,0))) j.val=(weights a).testBit j.val)
    (lengths : ∀u q j,val (midCol (.inr (u,q))) j.val=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.sizeAt oi u q)) j)
    (heads : ∀u j,val (midCol (.inl (u.1,3))) j.val=
      (addressEquiv _).symm (BinaryBarrelTurns.address (ChordAperture.head oi u true)) j)
    (rooms : ∀u (j:Fin (e+1)),val (midCol (.inl (u.1,if u.2 then 5 else 4))) j.val=
      (ChordAperture.room oi u).testBit j.val)
    (capacity : ∀p : (portGraph Q.sites).Port i,tapWidth p.val.1+r*SiteHardware.widthCap (SiteHardware.localWidth Q.data i)≤ slab)
    (key : Fin Q.sites→Word digits)
    (keys : ∀a j,val (socketStart old M D+a.val) j.val=bits (key a) j)
    (counters : ∀a (j : Fin (Nat.clog 2 (r+1))),val (2+a.val) j.val=SelectorShelf.bits c _ a j)
    (wanted : ∀t (j:Fin slab),Sum.elim before id
      (PacketNeighbor.wantedSocket preWidth i key id t j)=
      ((PhysicalMatrix.read Q.place _ i (cast (congrArg (fun U=>State U s) (Q.placedInput (r:=r)).symm) x)) t).val.testBit j.val) :
    let target:=cast (congrArg (fun U=>State U s) shape) (blockPortState gs s ((splitPortState rest (∑u,gs u) s z).2) pick)
    TypedWiring.value (circuit (e:=e) (p:=p) (digits:=digits) (D:=D) (width:=cap)
      old le read Q.data Q.graph i tap localEnds fit) env=R.entry c s x target := by
  intro target
  unfold circuit
  rw [specialize_value]
  apply partyProgram_value R c s rest gs pick parts shape away z short turns _ _ _ (Sum.elim env id) top sectors
    oldFit chordFit live o mem arg party len nbr here geom sites rows mounted
  · intro t f
    exact (fromPooled v before after _).trans (cpu t f)
  · exact post
  · rfl
  · exact roleBits
  · exact laneBits
  · intro u b
    exact (fromPooled v before after _).trans (sides u b)
  · intro u j
    exact (fromPooled v before after _).trans (amount u j)
  · intro yy
    unfold middleBody
    let m:=packedMiddle c s (middlePlace R c s slab oldFit) yy
    have columns : (2:ℕ)^e≤2^(e+1) := by rw [Nat.pow_succ]; omega
    apply signedContribution Q c R i tap fit _ _ _ localEnds aligned _ _ _ _ oldFit
      (Sum.elim (Sum.elim env id) m) key x yy sizeFit columns roomFit
    · intro u q j
      exact (fromPooled v before after _).trans (lengths u q j)
    · intro u side j
      cases side with
      | false=>
        change false=(0:ℕ).testBit j.val
        simp
      | true=>exact (fromPooled v before after _).trans (heads u j)
    · intro u j
      exact (fromPooled v before after _).trans (rooms u j)
    · intro j;rfl
    · exact capacity
    · intro u j
      exact (fromPooled v before after _).trans (keys u j)
    · intro u j
      exact (fromPooled v before after _).trans (counters u j)
    · intro t j
      refine Eq.trans ?_ (wanted t j)
      by_cases hit : j.val<preWidth t.val.1 ∧ j.val<cap ∧ (key (PacketNeighbor.other t)).val<D
      · simp only [PacketNeighbor.wantedSocket,dite_eq_left hit]; rfl
      · simp only [PacketNeighbor.wantedSocket,dite_eq_right hit]; rfl

/-- All intermediate index, mark, local offset and length bits are obtained
from a single actual native read of the emitted party block. -/
theorem native_circuit_read (shape : gs pick=R.post c) (away : ∀u,u≠pick→Subsingleton (State (gs u) s))
    (x : State (Q.wants r) s) (z : State (rest+∑j,gs j) s)
    (short : ∀a,(rs a).length≤2) (turns : Fin count≃Positions rs)
    (top : ∀q,tot q≤cap) (sectors : roles*2+D<2^p)
    (chordFit : ∀a,installedWidths phys mass (phys a)≤ slab) (live : ∀a,weights a<2^W)
    (o : PacketTurns.Operands fun a=>(rs a).length) (mem : Memory W) (arg : Word W)
    (party : Expr) (len nbr : Fin D→Expr) (here : party.eval mem arg=((s).val:Word W))
    (geom : PacketTurns.Reads oldEnds phys rs weights o mem arg) (sites : S≤2^W) (rows : N≤2^W)
    (mounted : PacketTurns.NeighborReads mem arg parts len nbr)
    (cpu : ∀(t:slot) (f:Control p e),val (old+(finProdFinEquiv (t,(projection f).1)).val) (projection f).2=
      (((o.column (o.gatheredWords R.ordinal len nbr) party (finProdFinEquiv (t,(projection f).1))).eval mem arg).val.testBit (projection f).2))
    (post : ∀q j,after (q,j)=ChordAperture.canonical parts (fun p k=>(z p).val.testBit k) q j)
    (roleBits : 2^p≤2^W) (laneBits : slab≤2^W)
    (aligned : ∀a,oldEnds a=Probe.physicalChord Q.place (localEnds a))
    (sizeFit : ∀q : (portGraph S).Port s,Q.offers c q.val.1≤ slab)
    (roomFit : ∀a,ChordAperture.room oi a<2^(e+1))
    (sourceFit : ∀a,installedWidths oldEnds weights (oldEnds a)≤ slab) (unwrapped : slab<2^W)
    (posted : ∀f : MiddleField,∀b,val (midCol f) b=
      ((o.middleFields M party (PacketTurns.middleNumber M (PacketTurns.Operands.middleLift le f))).eval mem arg).val.testBit b)
    (capacity : ∀p : (portGraph Q.sites).Port i,tapWidth p.val.1+r*SiteHardware.widthCap (SiteHardware.localWidth Q.data i)≤ slab)
    (key : Fin Q.sites→Word digits)
    (keys : ∀a j,val (socketStart old M D+a.val) j.val=bits (key a) j)
    (counters : ∀a (j : Fin (Nat.clog 2 (r+1))),val (2+a.val) j.val=SelectorShelf.bits c _ a j)
    (wanted : ∀t (j:Fin slab),Sum.elim before id
      (PacketNeighbor.wantedSocket preWidth i key id t j)=
      ((PhysicalMatrix.read Q.place _ i (cast (congrArg (fun U=>State U s) (Q.placedInput (r:=r)).symm) x)) t).val.testBit j.val) :
    let target:=cast (congrArg (fun U=>State U s) shape) (blockPortState gs s ((splitPortState rest (∑u,gs u) s z).2) pick)
    TypedWiring.value (circuit (e:=e) (p:=p) (digits:=digits) (D:=D) (width:=cap)
      old le read Q.data Q.graph i tap localEnds fit) env=R.entry c s x target := by
  obtain ⟨marked,amount,lengths,heads,rooms⟩:=ballot_middle (Q:=Q) (v:=v) (le:=le) (read:=read) (old:=old)
    (R:=R) (c:=c) (i:=i) (oldFit:=oldFit) (e:=e) o mem arg party geom here sites sourceFit unwrapped posted
  exact circuit_read Q c R i tap localEnds fit old le read v before after rest gs pick parts oldFit
    shape away x z short turns top sectors chordFit live o mem arg party len nbr here geom sites rows mounted
    cpu post roleBits laneBits aligned sizeFit roomFit marked amount lengths heads rooms capacity key keys counters wanted

end Hierarchy.WireTelescope.PassMatrix.PartyPins
end

end OAI
