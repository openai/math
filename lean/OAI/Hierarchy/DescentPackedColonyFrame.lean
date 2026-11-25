import OAI.Hierarchy.DescentPackedColonyROM

namespace OAI
/-! # Literal public split-trial words beside the retained roster and measured source -/
namespace Hierarchy.DescentPackedColony.Frame
open DescentSIMDLookup DescentColonies DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section
variable {H G Δ k M b w : ℕ}

inductive Slot (Δ k : ℕ)
  | id (i : Fin Δ)
  | offsets | chunks | initial
  | dictionary (s : Fin k) (t : Fin 4)

def number : Slot Δ k→ℕ
  | .id i=>i.val
  | .offsets=>Δ
  | .chunks=>Δ+1
  | .initial=>Δ+2
  | .dictionary s t=>Δ+3+4*s.val+t.val

theorem number_lt (x : Slot Δ k) : number x<Δ+3+4*k := by
  cases x with
  | id i=>simp only [number];omega
  | offsets | chunks | initial=>simp only [number];omega
  | dictionary s t=>have:=s.isLt;have:=t.isLt;simp only [number];omega

theorem number_injective : Function.Injective (number : Slot Δ k→ℕ) := by
  intro x y eqn
  cases x <;> cases y <;> simp only [number] at eqn
  all_goals first | rfl | (congr 1 <;> apply Fin.ext <;> omega) | omega

structure Chart where
  origin : ℕ
  bits : ℕ
  roster : Bank
  weights : Bank

open Chart

def Chart.page (A : Chart) := 2^A.bits
def Chart.start (A : Chart) (tag : ℕ) := A.origin+tag*A.page
def Chart.fresh (A : Chart) (Δ k : ℕ) := A.start (Δ+3+4*k)
def Chart.atSlot (A : Chart) (q : Slot Δ k) : Bank := ⟨A.start (number q),A.bits⟩

def byte (A : Chart) (x : Slot Δ k×Fin A.page) := A.start (number x.1)+x.2.val

theorem byte_injective (A : Chart) : Function.Injective (byte A : Slot Δ k×Fin A.page→ℕ) := by
  rintro ⟨x,i⟩ ⟨y,j⟩ equal
  have raw : number x*A.page+i.val=number y*A.page+j.val := by simpa [byte,start,Nat.add_assoc] using equal
  have ni : i.val=j.val := by
    have h:=congrArg (fun z=>z%A.page) raw
    simpa [Nat.mul_comm (number x) A.page,Nat.mul_comm (number y) A.page,Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using h
  have digit : number x*A.page=number y*A.page := by omega
  have high : number x=number y := (Nat.mul_left_inj (Nat.ne_of_gt (Nat.two_pow_pos A.bits))).mp digit
  exact Prod.ext (number_injective high) (Fin.ext ni)

theorem slot_before (A : Chart) (x : Slot Δ k) : (A.atSlot x).base+A.page≤A.fresh Δ k := by
  change A.origin+number x*A.page+A.page≤A.origin+(Δ+3+4*k)*A.page
  have := Nat.mul_le_mul_right A.page (Nat.succ_le_of_lt (number_lt x))
  rw [Nat.succ_mul] at this
  omega

def Chart.layerTables (A : Chart) (Δ k b M s : ℕ) (t : Fin 4) : Bank :=
  let high:=width k
  let n:=if t.val=0 ∨ t.val=2 then high else if t.val=1 then high+b*2^k else high+high
  ⟨A.start (Δ+3+4*s+t.val),n*M⟩

def Chart.issued (A : Chart) (Δ k b M : ℕ) : Layout Δ where
  ports := ⟨fun i=>A.atSlot (.id i : Slot Δ k),A.roster,A.atSlot (.offsets : Slot Δ k),A.atSlot (.chunks : Slot Δ k)⟩
  weight := A.weights
  source s := match s with
    | 0=>A.atSlot (.initial : Slot Δ k)
    | j+1=>⟨A.fresh Δ k+j*A.page,A.bits⟩
  base s:=⟨A.layerTables Δ k b M s 0,A.layerTables Δ k b M s 1⟩
  merge s:=⟨A.layerTables Δ k b M s 2,A.layerTables Δ k b M s 3⟩
  fresh:=A.fresh Δ k

/-- None of these numerical initial words depends on the input counts or the
incoming roster. The two dynamic predecessor arrays keep their earlier addresses. -/
def literal (Δ H G k b M w D cap : ℕ) (a μ : Bits k) (q : Slot Δ k) (i : ℕ) : Word w :=
  match q with
  | .id j=>if h:i<H*DescentSIMDLookup.chunks G M then
      (idWord ((row H G M).symm ⟨i,h⟩) j:ℕ) else 0
  | .offsets=>(DescentSIMDLookup.chunks G M*i:ℕ)
  | .chunks=>if h:i<H*DescentSIMDLookup.chunks G M then (chunkWord ((row H G M).symm ⟨i,h⟩):ℕ) else 0
  | .initial=>if h:i<H*DescentSIMDLookup.chunks G M then (emptyWord ((row H G M).symm ⟨i,h⟩) k:ℕ) else 0
  | .dictionary s t=>
    let d:=k-(s.val+1)
    if t.val=0 then ((2^((b*2^k)*M)*i:ℕ):Word w)
    else if t.val=1 then
      if h:i<2^((width k+b*2^k)*M) then
        ((DescentPackedZip.table (M:=M) (baseUpdate (b:=b) a μ cap d) ⟨i,h⟩).val:ℕ) else 0
    else if t.val=2 then ((2^(width k*M)*i:ℕ):Word w)
    else if h:i<2^((width k+width k)*M) then ((DescentPackedZip.table (M:=M) (merge (k:=k) D d) ⟨i,h⟩).val:ℕ)
         else 0

def Chart.mount (A : Chart) (Δ H G k b M D cap : ℕ) (a μ : Bits k) (m : Memory w) (z : ℕ) : Word w :=
  if h : ∃ p : Slot Δ k×Fin A.page,byte A p=z then literal Δ H G k b M w D cap a μ h.choose.1 h.choose.2.val
  else m z

theorem at_byte (A : Chart) (Δ H G k b M D cap : ℕ) (a μ : Bits k) (m : Memory w)
    (q : Slot Δ k) (i : Fin A.page) : mount A Δ H G k b M D cap a μ m (byte A (q,i))=
      literal Δ H G k b M w D cap a μ q i.val := by
  let yes : ∃z : Slot Δ k×Fin A.page,byte A z=byte A (q,i):=⟨(q,i),rfl⟩
  rw [mount,dite_eq_left yes,byte_injective A yes.choose_spec]

theorem before (A : Chart) (Δ H G k b M D cap : ℕ) (a μ : Bits k) (m : Memory w)
    {i : ℕ} (lo : i<A.origin) : mount A Δ H G k b M D cap a μ m i=m i := by
  rw [mount,dite_eq_right]
  rintro ⟨x,hx⟩
  unfold byte start at hx
  omega

theorem after (A : Chart) (Δ H G k b M D cap : ℕ) (a μ : Bits k) (m : Memory w)
    {i : ℕ} (hi : A.fresh Δ k≤ i) : A.mount Δ H G k b M D cap a μ m i=m i := by
  rw [mount,dite_eq_right]
  rintro ⟨⟨q,r⟩,eqn⟩
  have low := slot_before A q
  change A.start (number q)+A.page≤A.fresh Δ k at low
  change A.start (number q)+r.val=i at eqn
  have := r.isLt
  omega

structure Room (A : Chart) (H G Δ k b M w : ℕ) : Prop where
  sites : H≤A.page
  cells : H*DescentSIMDLookup.chunks G M≤A.page
  panel : 2^(width k*M)≤A.page
  withCounts : 2^((width k+b*2^k)*M)≤A.page
  both : 2^((width k+width k)*M)≤A.page
  topology : A.roster.Fits w A.origin
  topSize : H*Δ≤A.roster.size
  weight : A.weights.Fits w A.origin
  wtSize : H*DescentSIMDLookup.chunks G M≤A.weights.size
  endFits : A.fresh Δ k+(k+1)*A.page<2^w

private theorem page_small (A : Chart) (lim : Room A H G Δ k b M w) : A.page<2^w := by
  have fit:=lim.endFits
  rw [Nat.succ_mul] at fit
  omega

private theorem shift_fit {t out : ℕ} (B : Bank) (h : B.Fits w t) (le : t≤out) : B.Fits w out :=
  ⟨h.1,h.2.1,h.2.2.trans le⟩

private theorem stage_size (A : Chart) (s : ℕ) : ((A.issued Δ k b M).source s).size=A.page := by
  cases s <;> rfl

private theorem stage_end (A : Chart) (s : ℕ) : ((A.issued Δ k b M).source s).base+A.page≤A.fresh Δ k+s*A.page := by
  cases s with
  | zero=>simpa [issued] using slot_before A (.initial : Slot Δ k)
  | succ s=>change A.fresh Δ k+s*A.page+A.page≤A.fresh Δ k+(s+1)*A.page;rw [Nat.succ_mul,Nat.add_assoc]

private theorem dic_size (A : Chart) (lim : Room A H G Δ k b M w) (s : ℕ) (t : Fin 4) :
    (A.layerTables Δ k b M s t).size≤A.page := by
  fin_cases t <;> first | exact lim.panel | exact lim.withCounts | exact lim.both

private theorem dic_end (A : Chart) (lim : Room A H G Δ k b M w) (s : Fin k) (t : Fin 4) :
    (A.layerTables Δ k b M s.val t).base+(A.layerTables Δ k b M s.val t).size≤A.fresh Δ k :=
  (Nat.add_le_add_left (dic_size A lim _ t) _).trans (slot_before A (.dictionary s t))

theorem low (A : Chart) (lim : Room A H G Δ k b M w) : Low (A.issued Δ k b M) H G k b M := by
  have origin : A.origin≤A.fresh Δ k:=Nat.le_add_right ..
  constructor
  · intro i;exact (Nat.add_le_add_left lim.cells _).trans (slot_before A (.id i))
  · exact (Nat.add_le_add_left lim.topSize _).trans (lim.topology.2.2.trans origin)
  · exact (Nat.add_le_add_left lim.sites _).trans (slot_before A (.offsets : Slot Δ k))
  · exact (Nat.add_le_add_left lim.cells _).trans (slot_before A (.chunks : Slot Δ k))
  · exact (Nat.add_le_add_left lim.wtSize _).trans (lim.weight.2.2.trans origin)
  · intro s hs;exact dic_end A lim ⟨s,hs⟩ 0
  · intro s hs;exact dic_end A lim ⟨s,hs⟩ 1
  · intro s hs;exact dic_end A lim ⟨s,hs⟩ 2
  · intro s hs;exact dic_end A lim ⟨s,hs⟩ 3

theorem hardware (A : Chart) (lim : Room A H G Δ k b M w) : Hardware (A.issued Δ k b M) H G k b M w := by
  have small:=page_small A lim
  have origin : A.origin≤A.fresh Δ k:=Nat.le_add_right ..
  constructor
  · intro s hs
    let out:=A.fresh Δ k+s*A.page
    have opened : A.fresh Δ k≤out:=Nat.le_add_right ..
    have fixed (q : Slot Δ k) : (A.atSlot q).Fits w out :=
      ⟨Nat.two_pow_pos _,small,(slot_before A q).trans opened⟩
    have rom (t : Fin 4) : (A.layerTables Δ k b M s t).Fits w out :=
      ⟨Nat.two_pow_pos _,(dic_size A lim s t).trans_lt small,(dic_end A lim ⟨s,hs⟩ t).trans opened⟩
    constructor
    · constructor
      · intro i;exact fixed (.id i)
      · intro _;exact lim.cells
      · exact shift_fit _ lim.topology (origin.trans opened)
      · exact lim.topSize
      · exact fixed .offsets
      · exact lim.sites
      · exact fixed .chunks
      · exact lim.cells
      · refine ⟨Nat.two_pow_pos _,?_,?_⟩
        · rw [stage_size];exact small
        · rw [stage_size];exact stage_end A s
      · rw [stage_size];exact lim.cells
    · exact shift_fit _ lim.weight (origin.trans opened)
    · exact lim.wtSize
    · exact ⟨rom 0,rom 1,rfl,rfl⟩
    · exact ⟨rom 2,rom 3,rfl,rfl⟩
  · intro s hs;exact Nat.le_add_right ..
  · intro s hs
    change A.fresh Δ k+s*A.page+H*DescentSIMDLookup.chunks G M<2^w
    have future:=Nat.mul_le_mul_right A.page (Nat.succ_le_succ hs.le)
    rw [Nat.succ_mul,Nat.succ_mul] at future
    have endfits:=lim.endFits
    rw [Nat.succ_mul] at endfits
    have budget:=lim.cells
    omega

theorem input (A : Chart) (lim : Room A H G Δ k b M w) (rs : Fin H→Fin Δ→Option (Fin H))
    (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a μ : Bits k) (m : Memory w)
    (top : ∀v i,m (A.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (wt : Reads A.weights (fun v g=>counts b (W g v)) M m) :
    Input (A.issued Δ k b M) rs W D cap b M a μ (A.mount Δ H G k b M D cap a μ m) := by
  let literalAt (q : Slot Δ k) (j : ℕ) (small : j<A.page) := at_byte A Δ H G k b M D cap a μ m q ⟨j,small⟩
  constructor
  · constructor
    · intro p i
      simpa [issued,byte,atSlot,number,literal,(row H G M p).isLt,idWord] using
        literalAt (.id i) (row H G M p).val ((row H G M p).isLt.trans_le lim.cells)
    · intro v i
      have low : v.val*Δ+i.val<H*Δ := by
        have:=Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt v.isLt)
        rw [Nat.succ_mul] at this
        have:=i.isLt
        omega
      have lo:=lim.topology.2.2
      have yes: A.roster.base+(v.val*Δ+i.val)<A.origin :=
        (Nat.add_lt_add_left (low.trans_le lim.topSize) _).trans_le lo
      exact (before A Δ H G k b M D cap a μ m yes).trans (top v i)
    · intro v
      simpa [issued,byte,atSlot,number,literal] using literalAt .offsets v.val (v.isLt.trans_le lim.sites)
    · intro p
      simpa [issued,byte,atSlot,number,literal,(row H G M p).isLt,chunkWord] using
        literalAt .chunks (row H G M p).val ((row H G M p).isLt.trans_le lim.cells)
  · intro p
    exact (before A Δ H G k b M D cap a μ m ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le lim.wtSize) _).trans_le
      lim.weight.2.2)).trans (wt p)
  · apply empty_rows
    intro p
    simpa [issued,byte,atSlot,number,literal,(row H G M p).isLt] using
      literalAt .initial (row H G M p).val ((row H G M p).isLt.trans_le lim.cells)
  · intro s hs
    constructor
    · intro i
      simpa [issued,layerTables,byte,number,literal] using literalAt (.dictionary ⟨s,hs⟩ 0) i.val (i.isLt.trans_le lim.panel)
    · intro i
      simpa [issued,layerTables,byte,number,literal,i.isLt] using
        literalAt (.dictionary ⟨s,hs⟩ 1) i.val (i.isLt.trans_le lim.withCounts)
  · intro s hs
    constructor
    · intro i
      simpa [issued,layerTables,byte,number,literal] using literalAt (.dictionary ⟨s,hs⟩ 2) i.val (i.isLt.trans_le lim.panel)
    · intro i
      simpa [issued,layerTables,byte,number,literal,i.isLt] using literalAt (.dictionary ⟨s,hs⟩ 3) i.val (i.isLt.trans_le lim.both)

/-- Choose the page exponent from the actual packed row count and common
short state width. Thus unused intervals for the public tags cannot hide
a full RAM word for each raw group occurrence. -/
def pageBits (H G k b M : ℕ) :=
  max ((max H (H*DescentSIMDLookup.chunks G M)).log2+1) (unit k b*M)

theorem enough (H G k b M : ℕ) :
    H≤2^pageBits H G k b M ∧ H*DescentSIMDLookup.chunks G M≤2^pageBits H G k b M ∧
      2^(unit k b*M)≤2^pageBits H G k b M := by
  let n:=max H (H*DescentSIMDLookup.chunks G M)
  have hi : n≤2^pageBits H G k b M :=
    Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  exact ⟨(le_max_left ..).trans hi,(le_max_right ..).trans hi,Nat.pow_le_pow_right (by decide) (le_max_right ..)⟩

theorem page_price (H G k b w : ℕ) (positive : 0<unit k b) (wide : 2*unit k b≤w) :
    let M:=lanes w (unit k b)
    2^(pageBits H G k b M)*w≤2^(w/2)*w+2*(2*H*w+4*H*G*unit k b+w) := by
  dsimp only
  let M:=lanes w (unit k b)
  let n:=max H (H*DescentSIMDLookup.chunks G M)
  have hrow:=volume H G w (unit k b) positive wide
  have qty:n≤H+H*DescentSIMDLookup.chunks G M := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
  have twice : 2^(n.log2+1)≤2*(n+1) := by
    rw [Nat.pow_succ]
    by_cases zero:n=0
    · simp [zero]
    · have:=Nat.log2_self_le zero;omega
  have bill:=Nat.mul_le_mul_right w qty
  have pad:=Nat.mul_le_mul_right w twice
  have tab : 2^(unit k b*M)≤2^(w/2) := Nat.pow_le_pow_right (by decide)
    (by rw [Nat.mul_comm];exact lanes_fit ..)
  change 2^(max (n.log2+1) (unit k b*M))*w≤_
  rcases le_total (n.log2+1) (unit k b*M) with lt|lt
  · rw [max_eq_right lt]
    exact (Nat.mul_le_mul_right w tab).trans (Nat.le_add_right ..)
  · rw [max_eq_left lt]
    change H*DescentSIMDLookup.chunks G M*w≤_ at hrow
    nlinarith only [bill,pad,hrow,Nat.zero_le (2^(w/2)*w)]


end
end Hierarchy.DescentPackedColony.Frame

end OAI
