import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPackedGroupExchange

namespace OAI
/-! # Short remote source-wire receipts across genuine shared neighbor words -/
namespace Hierarchy.DescentSharedCableNames.Exchange
open DescentColonies DescentSixParty DescentHostDirectory Stage DescentPackedExchange
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype P] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Host J V k↪ℕ)
local notation "B" => Stage.source A native
local notation "N" => Stage.neighbors A native names
local notation "fit" => Stage.measured A native S ready
local notation "hSrc" => fun e : W.graph.Edge => Stage.home A (W.graph.src e)
local notation "hDst" => fun e : W.graph.Edge => Stage.home A (W.graph.dst e)
local notation "H" => Fintype.card V
local notation "R" => Fintype.card J

def sourcePort (q : Grain A) : A.CellPorts (hSrc q.1).1.1 (hSrc q.1).1.2 (hSrc q.1).2 := .inl ⟨⟨q.1,rfl,rfl⟩,q.2⟩
def targetPort (q : Grain A) : A.CellPorts (hDst q.1).1.1 (hDst q.1).1.2 (hDst q.1).2 := .inr ⟨⟨q.1,rfl,rfl⟩,q.2⟩
set_option quotPrecheck false in
local notation "left" => fun q : Grain A=>live A native S ready names (hSrc q.1) (sourcePort A q)
set_option quotPrecheck false in
local notation "right" => fun q : Grain A=>live A native S ready names (hDst q.1) (targetPort A q)

omit [Fintype P] in
private theorem source_names (q : Grain A) :
    (B).src (stream A native q)=hSrc q.1 ∧ (B).dst (stream A native q)=hDst q.1 :=by simp [Stage.source]

omit [Fintype P] in
/-- The receiving row's own serial is the same key used by the sender,
including for two ends of a loop and for oppositely oriented parallel wires. -/
theorem serial_same (q : Grain A) : (left q).wire=(right q).wire :=by
  let e:=stream A native q
  have l : (B).src e=hSrc q.1:=(source_names A native q).1
  have r : (B).dst e=hDst q.1:=(source_names A native q).2
  have srcPeer : (B).peer (hSrc q.1) e=hDst q.1 := (ite_eq_left l).trans r
  have dstPeer : (B).peer (hDst q.1) e=hSrc q.1:=by
    by_cases eqn : (B).src e=hDst q.1
    · exact (ite_eq_left eqn).trans (r.trans (eqn.symm.trans l))
    · exact (ite_eq_right eqn).trans l
  apply Fin.ext
  change (B).serial (hSrc q.1) ((B).peer (hSrc q.1) e) e=(B).serial (hDst q.1) ((B).peer (hDst q.1) e) e
  rw [srcPeer,dstPeer,←l,←r]
  exact (B).both_ends e

/-- Fixed lookup on the actual short signed slots of one source. The query
only carries the reciprocal immutable neighbor and the shared grain serial. -/
abbrev Triple (deg cap : ℕ) := Fin deg × Fin cap × Fin cap

def sender {deg cap : ℕ} (t : Live deg cap) : Option (Triple deg cap) :=
  if t.target then none else some (t.neighbor,t.wire,t.sourceWire)

def query {m deg cap : ℕ} (row : Fin m→Option (Triple deg cap)) (peer : Fin deg) (serial : Fin cap) : Option (Fin cap) :=
  if ok : ∃s w,row s=some (peer,serial,w) then some ok.choose_spec.choose else none

def chooseWire {deg cap : ℕ} (row : Fin (2*cap)→Option (Live deg cap)) (peer : Fin deg) (serial : Fin cap) : Option (Fin cap) :=
  query (fun s=>(row s).bind sender) peer serial

omit [Fintype P] in
theorem matching (q : Grain A) (s : Fin (2*A.cap)) (t : Live A.degree A.cap)
    (hit : signedPanel A native S ready names (hSrc q.1) s=some t)
    (peer : t.neighbor=(left q).neighbor) (serial : t.wire=(right q).wire) :
    t.sourceWire=Stage.outgoing A native S ready ⟨q.1,Nat.zero_lt_of_lt q.2.isLt⟩ :=by
  let h:=hSrc q.1
  let p:=sourcePort A q
  let addr:=signed A native S ready h.1 h.2
  have atSlot : ∃u,addr u=s :=by
    by_contra missing
    rw [signed_empty A native S ready names h s (not_exists.mp missing)] at hit
    contradiction
  obtain ⟨u,atU⟩:=atSlot
  rw [←atU,signed_read] at hit
  have eqn : live A native S ready names h u=t:=Option.some.inj hit
  let a:=Stage.ofPort A native h u
  let b:=Stage.ofPort A native h p
  have adj : (B).peer h a.val=(B).peer h b.val:=((N).same h a b).1 (by change (live A native S ready names h u).neighbor=(left q).neighbor;exact (congrArg Live.neighbor eqn).trans peer)
  have serialEq : (B).serial h ((B).peer h a.val) a.val=(B).serial h ((B).peer h b.val) b.val:=by
    exact congrArg Fin.val (((congrArg Live.wire eqn).trans serial).trans (serial_same A native S ready names q).symm)
  rw [←adj] at serialEq
  have equal:=(B).distinguish (((B).mem_parallel ..).2 ⟨a.property,rfl⟩) (((B).mem_parallel ..).2 ⟨b.property,adj.symm⟩) serialEq
  have ra (z : A.CellPorts h.1.1 h.1.2 h.2) : Stage.recover A h z=(stream A native).symm (Stage.ofPort A native h z).val :=by
    cases z <;> simp [Stage.ofPort,Stage.recover]
  have same : Stage.recover A h u=q:=(ra u).trans ((congrArg (stream A native).symm equal).trans (ra p).symm)
  rw [←eqn]
  apply congrArg (Stage.outgoing A native S ready);exact Subtype.ext (congrArg Sigma.fst same)

omit [Fintype P] in
theorem choose_at (q : Grain A) :
    chooseWire (signedPanel A native S ready names (hSrc q.1)) (left q).neighbor (right q).wire=
      some (Stage.outgoing A native S ready ⟨q.1,Nat.zero_lt_of_lt q.2.isLt⟩) :=by
  let h:=hSrc q.1
  let p:=sourcePort A q
  let addr:=signed A native S ready h.1 h.2
  let row:=signedPanel A native S ready names h
  have ok : ∃s wire,(row s).bind sender=some ((left q).neighbor,(right q).wire,wire):=by
    refine ⟨addr p,(left q).sourceWire,?_⟩
    have atP : row (addr p)=some (left q):=signed_read A native S ready names h p
    rw [atP,←serial_same A native S ready names q];rfl
  unfold chooseWire query;rw [dite_eq_left ok]
  let u:=ok.choose
  let w:=ok.choose_spec.choose
  have chosen : (row u).bind sender=some ((left q).neighbor,(right q).wire,w):=ok.choose_spec.choose_spec
  cases hit : row u with
  | none=>rw [hit] at chosen;contradiction
  | some t=>
    rw [hit] at chosen
    change (if t.target then none else some (t.neighbor,t.wire,t.sourceWire))=some ((left q).neighbor,(right q).wire,w) at chosen
    split at chosen
    · contradiction
    · have same:=Option.some.inj chosen
      have id :=matching A native S ready names q u t hit (congrArg Prod.fst same) (congrArg (fun z=>z.2.1) same)
      exact congrArg some ((congrArg (fun z=>z.2.2) same).symm.trans id)

/-- One native common-host vector, partitioned into group, original block,
reciprocal peer, shared grain serial, and a small source-ordinal bit. -/
def width (r k deg cap : ℕ) := r*(2^k*(deg*(cap*Packed.bits cap)))
def address {r k deg cap : ℕ} (g : Fin r) (x : Block k) (peer : Fin deg) (s : Fin cap) (j : Fin (Packed.bits cap)) : Fin (width r k deg cap) :=
  finProdFinEquiv (g,finProdFinEquiv (x,finProdFinEquiv (peer,finProdFinEquiv (s,j))))

def vector (v : Fin H) (i : Fin (width R k A.degree A.cap)) : Bool :=
  let gx : Fin R × Fin (2^k*(A.degree*(A.cap*Packed.bits A.cap))):=finProdFinEquiv.symm i
  let xd : Block k × Fin (A.degree*(A.cap*Packed.bits A.cap)):=finProdFinEquiv.symm gx.2
  let ds : Fin A.degree × Fin (A.cap*Packed.bits A.cap):=finProdFinEquiv.symm xd.2
  let sj : Fin A.cap × Fin (Packed.bits A.cap):=finProdFinEquiv.symm ds.2
  let h : Host J V k:=(((Fintype.equivFin J).symm gx.1,(Fintype.equivFin V).symm v),xd.1)
  wordBits (Packed.bits A.cap) (Packed.token (chooseWire (signedPanel A native S ready names h) ds.1 sj.1)) sj.2

omit [Fintype P] in
theorem vector_at (q : Grain A) (j : Fin (Packed.bits A.cap)) :
    let h:=hSrc q.1
    vector A native S ready names ((Fintype.equivFin V) h.1.2)
      (address ((Fintype.equivFin J) h.1.1) h.2 (left q).neighbor (right q).wire j)=
      wordBits _ (Packed.token (some (Stage.outgoing A native S ready ⟨q.1,Nat.zero_lt_of_lt q.2.isLt⟩))) j :=by
  intro h
  simp only [vector,address,Equiv.symm_apply_apply,Prod.mk.eta]
  rw [choose_at A native S ready names q]

private def chunk {b : ℕ} (pos : 0<w) (s : Fin b) : Fin (batch w b):=
  ⟨s.val/w,(Nat.div_lt_iff_lt_mul pos).2 (by simpa [batch,Nat.mul_comm] using s.isLt.trans_le (CallPool.count_le_batches_mul b w pos))⟩
private def bit {b : ℕ} (pos : 0<w) (s : Fin b) : Fin w:=⟨s.val%w,Nat.mod_lt _ pos⟩

def ReadBack (out : ℕ) (positive : 0<w) (m : Memory w) (q : Grain A) : Prop :=
  let h:=hSrc q.1
  ∃ port : Fin A.degree,∀ j : Fin (Packed.bits A.cap),
    let s:=address ((Fintype.equivFin J) h.1.1) h.2 (left q).neighbor (right q).wire j
    wordBits w (m (out+(id H A.degree w (width R k A.degree A.cap) (chunk positive s,(Fintype.equivFin V) (hDst q.1).1.2,port)).val)) (bit positive s)=
      wordBits _ (Packed.token (some (Stage.outgoing A native S ready ⟨q.1,Nat.zero_lt_of_lt q.2.isLt⟩))) j

omit [Fintype P] in
/-- The executable is the immutable common-neighbor scan, with one transfer
per packed row and peer and no transfer per global edge name. -/
theorem run (g : Banks) (out : ℕ) (pos : 0<w) (wide : Fits g out H A.degree w (width R k A.degree A.cap)) :
    let b:=width R k A.degree A.cap
    let x:=vector A native S ready names
    (program out H A.degree w b g).Spec (Reads g (stageNext A) x)
      (fun m result=> result=image out (rows H A.degree w b) (gather g) m ∧
        ∀q,ReadBack A native S ready names out pos result q)
      (4+rows H A.degree w b*(2*work g+4)) ∧ CheapCode (program out H A.degree w b g) :=by
  intro b x
  obtain ⟨real,cheap⟩:=stage_spec A g out wide x
  refine ⟨real.mono (fun _ h=>h) ?_ (le_refl _),cheap⟩
  rintro m result ⟨written,reads⟩;refine ⟨written,?_⟩
  intro q;obtain ⟨port,copy⟩:=(reads q.1).2
  refine ⟨port,?_⟩;intro j
  let h:=hSrc q.1
  let s:=address ((Fintype.equivFin J) h.1.1) h.2 (left q).neighbor (right q).wire j
  let c:=chunk pos s
  let t:=bit pos s
  have coord : c.val*w+t.val=s.val:=by
    change s.val/w*w+s.val%w=s.val;rw [Nat.mul_comm,Nat.add_comm,Nat.mod_add_div]
  have read:=copy c t
  have fit' : c.val*w+t.val<b:=by rw [coord];exact s.isLt
  rw [dite_eq_left fit'] at read
  exact read.trans ((congrArg (x ((Fintype.equivFin V) h.1.2)) (Fin.ext coord)).trans (vector_at A native S ready names q j))

end
end Hierarchy.DescentSharedCableNames.Exchange

end OAI
