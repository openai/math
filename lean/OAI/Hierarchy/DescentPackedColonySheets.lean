import OAI.Hierarchy.DescentPackedColonyFrame

namespace OAI
/-! # All public multiplier sheets in one fixed, parametrically packed RAM input -/
namespace Hierarchy.DescentPackedColony.Frame
open DescentSIMDLookup DescentColonies DescentGL Chart
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {Δ H G q k M b w : ℕ}

def Chart.sheetSpan (A : Chart) (Δ k : ℕ) := (Δ+3+4*k)*A.page

def Chart.sheet (A : Chart) (Δ k j : ℕ) : Chart := {A with origin:=A.origin+j*A.sheetSpan Δ k}

def Chart.sheetEnd (A : Chart) (Δ k q : ℕ) := A.origin+q*A.sheetSpan Δ k

@[simp] theorem sheet_page (A : Chart) (Δ k j : ℕ) : (A.sheet Δ k j).page=A.page := rfl

theorem sheet_next (A : Chart) (Δ k j : ℕ) : (A.sheet Δ k j).fresh Δ k=(A.sheet Δ k (j+1)).origin := by
  change A.origin+j*A.sheetSpan Δ k+A.sheetSpan Δ k=A.origin+(j+1)*A.sheetSpan Δ k
  rw [Nat.succ_mul,Nat.add_assoc]

def Zone (A : Chart) (Δ k : ℕ) (j i : ℕ) := (A.sheet Δ k j).origin≤ i ∧ i<(A.sheet Δ k j).fresh Δ k

theorem zone_unique (A : Chart) {i Δ k j h : ℕ} (one : Zone A Δ k j i) (two : Zone A Δ k h i) : j=h := by
  have step {s t : ℕ} (st : s<t) : (A.sheet Δ k s).fresh Δ k≤(A.sheet Δ k t).origin := by
    rw [sheet_next]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt st)) _
  rcases lt_trichotomy j h with lj|eq|lh
  · exact (Nat.not_lt_of_ge ((step lj).trans two.1) one.2).elim
  · exact eq
  · exact (Nat.not_lt_of_ge ((step lh).trans one.1) two.2).elim

def Chart.mountAll (A : Chart) (Δ H G k b M D cap : ℕ) (a : Bits k) (seed : Fin q→Bits k)
    (m : Memory w) (i : ℕ) : Word w :=
  if h : ∃j : Fin q,Zone A Δ k j.val i then
    (A.sheet Δ k h.choose.val).mount Δ H G k b M D cap a (seed h.choose) m i
  else m i

theorem mountAll_zone (A : Chart) (Δ H G k b M D cap : ℕ) (a : Bits k) (seed : Fin q→Bits k)
    (m : Memory w) (j : Fin q) {i : ℕ} (zone : Zone A Δ k j.val i) :
    A.mountAll Δ H G k b M D cap a seed m i=(A.sheet Δ k j.val).mount Δ H G k b M D cap a (seed j) m i := by
  let yes:∃h:Fin q,Zone A Δ k h.val i:=⟨j,zone⟩
  rw [mountAll,dite_eq_left yes,show yes.choose=j from Fin.ext (zone_unique A yes.choose_spec zone)]

theorem mountAll_frame (A : Chart) (Δ H G k b M D cap : ℕ) (a : Bits k) (seed : Fin q→Bits k)
    (m : Memory w) {i : ℕ} (out : i<A.origin ∨ A.sheetEnd Δ k q≤ i) :
    A.mountAll Δ H G k b M D cap a seed m i=m i := by
  rw [mountAll,dite_eq_right]
  rintro ⟨j,(lower : (A.sheet Δ k j.val).origin≤ i),(upper : i<(A.sheet Δ k j.val).fresh Δ k)⟩
  rw [sheet_next] at upper
  have next : (A.sheet Δ k (j.val+1)).origin≤A.sheetEnd Δ k q :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
  change A.origin+j.val*A.sheetSpan Δ k≤ i at lower
  omega

private theorem full_byte (A : Chart) (Δ k : ℕ) (i : ℕ) (lo : A.origin≤ i) (hi : i<A.fresh Δ k) :
    ∃p:Slot Δ k×Fin A.page,byte A p=i := by
  let t:=(i-A.origin)/A.page
  have pp:0<A.page:=Nat.two_pow_pos _
  have tag : t<Δ+3+4*k := (Nat.div_lt_iff_lt_mul pp).2 (by change i<A.origin+(Δ+3+4*k)*A.page at hi;omega)
  have each : ∃s : Slot Δ k,number s=t := by
    by_cases id:t<Δ
    · exact ⟨.id ⟨t,id⟩,rfl⟩
    by_cases off:t=Δ
    · exact ⟨.offsets,off.symm⟩
    by_cases ch:t=Δ+1
    · exact ⟨.chunks,ch.symm⟩
    by_cases zero:t=Δ+2
    · exact ⟨.initial,zero.symm⟩
    let n:=t-(Δ+3)
    have nrange:n<4*k:=by unfold n;omega
    let s:Fin k:=⟨n/4,by omega⟩
    let u:Fin 4:=⟨n%4,Nat.mod_lt _ (by decide)⟩
    refine ⟨.dictionary s u,?_⟩
    change Δ+3+4*(n/4)+n%4=t
    have eq:=Nat.mod_add_div n 4
    unfold n at *
    omega
  obtain ⟨s,eq⟩:=each
  let n:=i-A.origin
  let r : Fin A.page:=⟨n%A.page,Nat.mod_lt _ pp⟩
  refine ⟨(s,r),?_⟩
  change A.origin+number s*A.page+n%A.page=i
  rw [eq,Nat.mul_comm t A.page]
  have partition:=Nat.mod_add_div n A.page
  change A.origin+A.page*(n/A.page)+n%A.page=i
  omega

theorem stamped (A : Chart) (Δ H G k b M D cap : ℕ) (a : Bits k) (seed : Fin q→Bits k)
    (m : Memory w) (j : Fin q) :
    let image:=A.mountAll Δ H G k b M D cap a seed m
    (A.sheet Δ k j.val).mount Δ H G k b M D cap a (seed j) image=image := by
  dsimp only
  let C:=A.sheet Δ k j.val
  let image:=A.mountAll Δ H G k b M D cap a seed m
  funext i
  by_cases lo:i<C.origin
  · exact before C Δ H G k b M D cap a (seed j) image lo
  by_cases hi:i<C.fresh Δ k
  · obtain ⟨⟨s,r⟩,rfl⟩:=full_byte C Δ k i (by omega) hi
    rw [mountAll_zone A Δ H G k b M D cap a seed m j ⟨Nat.le_of_not_gt lo,hi⟩]
    exact (at_byte C Δ H G k b M D cap a (seed j) image s r).trans
      (at_byte C Δ H G k b M D cap a (seed j) m s r).symm
  · exact after C Δ H G k b M D cap a (seed j) image (Nat.le_of_not_gt hi)

theorem sourceReady (A : Chart) (rs : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (seed : Fin q→Bits k) (m : Memory w)
    (rooms : ∀j : Fin q,Room (A.sheet Δ k j.val) H G Δ k b M w)
    (realTop : A.roster.base+A.roster.size≤A.origin)
    (realWt : A.weights.base+A.weights.size≤A.origin)
    (top : ∀v i,m (A.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (wt : Reads A.weights (fun v g=>counts b (W g v)) M m) (j : Fin q) :
    Input ((A.sheet Δ k j.val).issued Δ k b M) rs W D cap b M a (seed j)
      (A.mountAll Δ H G k b M D cap a seed m) := by
  let C:=A.sheet Δ k j.val
  let im:=A.mountAll Δ H G k b M D cap a seed m
  have h:=rooms j
  have topology (v : Fin H) (i : Fin Δ) :
      im (C.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w) := by
    have vl:=Nat.mul_le_mul_right Δ v.isLt
    rw [Nat.succ_mul] at vl
    have yes:v.val*Δ+i.val<H*Δ:=by have :=i.isLt;omega
    have fits: H*Δ≤A.roster.size:=h.topSize
    have low := (Nat.add_lt_add_left (yes.trans_le fits) A.roster.base).trans_le realTop
    exact (mountAll_frame A Δ H G k b M D cap a seed m (.inl low)).trans (top v i)
  have weights:Reads C.weights (fun v g=>counts b (W g v)) M im := by
    intro p
    have low:=Nat.add_lt_add_left ((row H G M p).isLt.trans_le h.wtSize) A.weights.base
    exact (mountAll_frame A Δ H G k b M D cap a seed m (.inl (low.trans_le realWt))).trans (wt p)
  have proof:=input C h rs W D cap a (seed j) im topology weights
  have mounted : C.mount Δ H G k b M D cap a (seed j) im = im := stamped A Δ H G k b M D cap a seed m j
  rw [mounted] at proof
  exact proof

/-- A single aperture check and the two genuine banks suffice for every sheet. -/
theorem rooms (A : Chart) (layout : A.bits=pageBits H G k b M)
    (top : A.roster.Fits w A.origin) (topSize : H*Δ≤A.roster.size)
    (weight : A.weights.Fits w A.origin) (wtSize : H*chunks G M≤A.weights.size)
    (aperture : A.sheetEnd Δ k q+(k+1)*A.page<2^w) (j : Fin q) :
    Room (A.sheet Δ k j.val) H G Δ k b M w := by
  let C:=A.sheet Δ k j.val
  have pg : C.page=2^pageBits H G k b M := by change 2^A.bits=_;rw [layout]
  obtain ⟨sites,cells,table⟩:=enough H G k b M
  have powSize {n : ℕ} (le:n≤unit k b) : 2^(n*M)≤C.page := by
    rw [pg]
    exact (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right M le)).trans table
  have org : A.origin≤C.origin:=Nat.le_add_right ..
  have endRoom : C.fresh Δ k≤A.sheetEnd Δ k q := by
    change (A.sheet Δ k j.val).fresh Δ k≤_
    rw [sheet_next]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
  refine ⟨?_,?_,powSize ((Nat.le_add_right _ _).trans (le_max_left ..)),
    powSize (le_max_right ..),powSize (le_max_left ..),
    ⟨top.1,top.2.1,top.2.2.trans org⟩,topSize,
    ⟨weight.1,weight.2.1,weight.2.2.trans org⟩,wtSize,
    (Nat.add_le_add_right endRoom _).trans_lt aperture⟩
  · exact sites.trans_eq pg.symm
  · exact cells.trans_eq pg.symm

theorem bit_price_width (L : Layout Δ) (H G k b width cpu C : ℕ) (_pos : 0<unit k b)
    (wide : 2*unit k b≤width) (upper : cpu≤C*width) :
    let M:=lanes width (unit k b)
    clock (passes L H G M k)*cpu ≤ C*((4+4*k)*width+
      k*(2*(25+56*Δ)+4)*(H*width+4*H*G*unit k b)) := by
  have work:=bit_price L H G k b width wide
  exact (Nat.mul_le_mul_left _ upper).trans (by rw [Nat.mul_left_comm];exact Nat.mul_le_mul_left C work)

theorem page_price_width (H G k b width cpu C : ℕ) (pos : 0<unit k b)
    (wide : 2*unit k b≤width) (upper : cpu≤C*width) :
    let M:=lanes width (unit k b)
    2^(pageBits H G k b M)*cpu≤ C*(2^(width/2)*width+2*(2*H*width+4*H*G*unit k b+width)) := by
  have bill:=page_price H G k b width pos wide
  exact (Nat.mul_le_mul_left _ upper).trans (by rw [Nat.mul_left_comm];exact Nat.mul_le_mul_left C bill)

end
end Hierarchy.DescentPackedColony.Frame

end OAI
