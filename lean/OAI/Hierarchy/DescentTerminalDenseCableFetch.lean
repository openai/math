import OAI.Hierarchy.DescentTerminalCableSlots

namespace OAI
/-! # The genuine two-word cable read at a canonical terminal group -/

namespace Hierarchy.DescentTerminalDenseCableFetch
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalCableOrder
open DescentTerminalDenseWindow DescentTerminalDenseGraphRead DescentTerminalPorts
open ThreeFlat.Routing Computability.VPVNP.RAMSerialization Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
noncomputable section

variable {D S p q : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
    (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "L" => order N home native p external nodes ops

/-- A request is a whole row of one actual neighbor group. -/
structure Packet (L' : Order N S p) (q : ℕ) where
  site : Fin S
  other : Fin S
  group : Order.Group L' site
  toOther : group.val=some other
  row : Fin (poolBatchCount (Fintype.card (Order.At L' site group)) q)

private def flatten (L' : Order N S p) : Packet N L' q ↪
    (i : Fin S) × (g : Order.Group L' i) × Fin (poolBatchCount (Fintype.card (Order.At L' i g)) q) where
  toFun a := ⟨a.site,a.group,a.row⟩
  inj' := by
    rintro ⟨i,j,g,t,r⟩ ⟨i',j',g',t',r'⟩ eqn
    cases eqn
    have ids : j=j' := Option.some.inj (t.symm.trans t')
    cases ids
    rfl

noncomputable instance packetFinite (L' : Order N S p) : Fintype (Packet N L' q) :=
  Fintype.ofInjective _ (flatten (q:=q) N L').injective

/-- Each actual cable packet occupies a single purchased port row. -/
theorem packet_port_rows :
    Fintype.card (Packet N L q) ≤ ∑i,((L).site i).portRows q := by
  have inside := Fintype.card_le_of_injective _ (flatten (q:=q) N L).injective
  have port (i : Fin S) : (∑g : Order.Group L i,poolBatchCount (Fintype.card (Order.At L i g)) q)=
      ((L).site i).portRows q := by
    symm
    exact (Order.groups L i).symm.sum_comp (fun g=>poolBatchCount (Fintype.card (Order.At L i g)) q)
  simpa only [Fintype.card_sigma,Fintype.card_fin,port] using inside

theorem packet_count_of {W : ℕ} (wp : 0<W) (sites : Fin S→DescentTerminalRecipeRows.Site)
    (portRows : ∀i,((L).site i).portRows q ≤ (sites i).rows q) :
    Fintype.card (Packet N L q) ≤ DescentTerminalBinPack.purchased W (DescentTerminalRecipeRows.counts (q:=q) sites) := by
  have paid:=Fintype.card_le_of_injective _ (DescentTerminalBinPack.rowIndex wp
    (DescentTerminalRecipeRows.counts (q:=q) sites)).injective
  simp only [Fintype.card_sigma,Fintype.card_fin] at paid
  exact (packet_port_rows N home native external nodes ops).trans
    ((Finset.sum_le_sum (fun i _=>portRows i)).trans paid)

/-- One request per actual neighbor row. The packed bin allocation covers them all. -/
theorem packet_count {W : ℕ} (wp : 0<W) :
    Fintype.card (Packet N L q) ≤ DescentTerminalBinPack.purchased W (DescentTerminalRecipeRows.counts (q:=q) (L).site) :=
  packet_count_of N home native external nodes ops wp (L).site (fun i=>by
    unfold DescentTerminalRecipeRows.Site.rows;omega)

variable (qp : 0<q*p)
private theorem small (b : Packet N L q) (u : Fin (Fintype.card (Order.At L b.site b.group))) :
    groupLengths N L b.site b.group u ≤ p := by
  unfold groupLengths
  cases ((Order.inGroup L b.site b.group).symm u).val <;> exact Nat.min_le_left ..

def fmt (b : Packet N L q) : Format q p :=
  format (groupLengths N L b.site b.group) qp (small N home native external nodes ops b)
    (pairBase N home b.site b.other) b.row.val

def index (b : Packet N L q) : ℕ :=
  first (groupLengths N L b.site b.group) q (pairBase N home b.site b.other) b.row.val/(q*p)

theorem fetch_bit {rawRows : ℕ} (room : (∑e,N.width e) ≤ rawRows*(q*p))
    (pay : RowBit rawRows (q*p)→Bool) (b : Packet N L q) (s : Fin q)
    (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p))
    (hit : b.row.val*q+s.val<Fintype.card (Order.At L b.site b.group))
    (label : ((Order.inGroup L b.site b.group).symm ⟨_,hit⟩).val=.inl ⟨e,k⟩) (j : Fin p) :
    let i := index N home native external nodes ops b
    wordBits _ (word (fmt N home native external nodes ops qp b)
        (dense (q*p) (stream pay) i) (dense (q*p) (stream pay) (i+1))) (finProdFinEquiv (s,j))=
      TaggedShorterFields.slice p (takeBits N (denseBits N (edgeCode N home native) room) pay e) k.val j := by
  have hp : 0<p := Nat.pos_of_ne_zero (by intro eq;simp [eq] at qp)
  obtain ⟨atBit,live⟩ := cable_slot_address N home native external nodes ops hp b.site b.other b.group
    b.toOther b.row.val s e k hit label
  exact cable_slot N (groupLengths N L b.site b.group) qp (small N home native external nodes ops b)
    (pairBase N home b.site b.other) b.row.val (edgeCode N home native) room pay e k.val s atBit live j

theorem blank_bit (all : ℕ→Bool) (b : Packet N L q) (s : Fin q) (j : Fin p)
    (past : Fintype.card (Order.At L b.site b.group) ≤ b.row.val*q+s.val) :
    let i := index N home native external nodes ops b
    wordBits _ (word (fmt N home native external nodes ops qp b) (dense (q*p) all i)
      (dense (q*p) all (i+1))) (finProdFinEquiv (s,j))=false := by
  intro i
  rw [word_at]
  simp [select,fmt,format,lengthAt,Nat.not_lt.mpr past]

include qp in
theorem index_sentinel {rawRows : ℕ} (room : (∑e,N.width e) ≤ rawRows*(q*p)) (b : Packet N L q) :
    index N home native external nodes ops b+1<rawRows+2 := by
  have hq : 0<q := Nat.pos_of_ne_zero (by intro eq;simp [eq] at qp)
  have hp : 0<p := Nat.pos_of_ne_zero (by intro eq;simp [eq] at qp)
  have ix := piece_used hq b.row
  let s : Fin q := ⟨0,hq⟩
  have curr : b.row.val*q+s.val<Fintype.card (Order.At L b.site b.group) := by simpa [s] using ix
  let original := (Order.inGroup L b.site b.group).symm ⟨_,curr⟩
  have endpoint := original.property.2.trans b.toOther
  cases h : original.val with
  | inr z => simp [h,Order.neighbor] at endpoint
  | inl cable =>
    obtain ⟨atBit,_⟩ := cable_slot_address N home native external nodes ops hp b.site b.other b.group b.toOther
      b.row.val s cable.1 cable.2 curr h
    have edgeEnd := ProtocolRAMPortRanks.prefix_end N.width (edgeCode N home native) cable.1
    have within := piece_used hp cable.2
    have firstBound : first (groupLengths N L b.site b.group) q (pairBase N home b.site b.other) b.row.val<
        rawRows*(q*p) := by
      simp only [s,DescentTerminalDenseWindow.begin,Nat.add_zero] at atBit
      unfold first
      omega
    have bounded : index N home native external nodes ops b<rawRows := (Nat.div_lt_iff_lt_mul qp).mpr firstBound
    omega

theorem native_bit {wordSize rawRows count : ℕ} (out : ℕ) (wordRoom : q*p ≤ wordSize)
    (room : (∑e,N.width e) ≤ rawRows*(q*p)) (pay : RowBit rawRows (q*p)→Bool)
    (request : Fin count→Packet N L q) (m : Memory wordSize) (u : Fin count)
    (s : Fin q) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p))
    (hit : (request u).row.val*q+s.val<Fintype.card (Order.At L (request u).site (request u).group))
    (label : ((Order.inGroup L (request u).site (request u).group).symm ⟨_,hit⟩).val=.inl ⟨e,k⟩) (j : Fin p) :
    let addresses := fun t=>index N home native external nodes ops (request t)
    let formats := fun t=>fmt N home native external nodes ops qp (request t)
    let data := dense (q*p) (stream pay)
    let after := ThreeFlat.RAM.fillSegment out count (DescentTerminalDenseWindowRAM.file out addresses formats data) m
    wordBits wordSize (after (out+u.val)) ((finProdFinEquiv (s,j)).castLE wordRoom)=
      TaggedShorterFields.slice p (takeBits N (denseBits N (edgeCode N home native) room) pay e) k.val j := by
  intro addresses formats data after
  exact (DescentTerminalDenseWindowRAM.output_bit out addresses formats data m u _ wordRoom).trans
    (fetch_bit N home native external nodes ops qp room pay (request u) s e k hit label j)

end
end Hierarchy.DescentTerminalDenseCableFetch

end OAI
