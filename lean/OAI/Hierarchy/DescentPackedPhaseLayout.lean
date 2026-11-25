import OAI.Hierarchy.DescentPackedPhaseTables
import OAI.Hierarchy.DescentPackedTrialLayout
import OAI.Hierarchy.DescentPackedColonySheets

namespace OAI
/-! # Public placement of all ordinary-phase reads and writes -/

namespace Hierarchy.DescentPackedColony.Phase.Arena
open _root_.OAI.Hierarchy.DescentPackedColony.Frame DescentColonies DescentSIMDLookup DescentAffineColors DescentBinaryField ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {k b h w Δ ℓ G : ℕ}

def menu (A : Chart) (Δ k : ℕ) := A.sheetEnd Δ k (2^k-1)
def names (A : Chart) (Δ k h : ℕ) := menu A Δ k+Menu.pages k*2^(h/2)
def first (A : Chart) (Δ k b h : ℕ) := names A Δ k h+PackedWinnerRAM.tableWords k (lanes h (unit k b))
def seedWork (A : Chart) (Δ k b h : ℕ) := first A Δ k b h+(2^k-1)*((k+1)*A.page)
def selected (A : Chart) (Δ k b h : ℕ) := seedWork A Δ k b h+3*A.page+(2^k-1+1)
def colorWork (A : Chart) (Δ k b h : ℕ) := selected A Δ k b h+A.page
def endAt (A : Chart) (Δ k b h : ℕ) := colorWork A Δ k b h+3*A.page+(2^(k+1)+1)

def minimum (A : Chart) {n : ℕ} (work : ℕ) (src dic : Fin n→Bank) : DescentPackedMinimum.Layout n :=
  ⟨src,dic,work,⟨work+2*A.page,A.bits⟩,work+3*A.page⟩

def shelves (A : Chart) (amt : Bank) (Δ k b h : ℕ) : Shelves k Δ :=
  let M:=lanes h (unit k b)
  let cuts:=fun i : Fin (2^k-1)=>A.sheet Δ k i.val
  let trials:=Frame.allTrials cuts (first A Δ k b h) A.page Δ k b M
  let m:=menu A Δ k
  let p:=2^(h/2)
  { layers:=trials,split:=minimum A (seedWork A Δ k b h) (fun i=>(trials i).source k) (fun _=>Menu.split m p k b M),
    color:=minimum A (colorWork A Δ k b h) (fun _=>⟨selected A Δ k b h,A.bits⟩) (Menu.color m p k b M),
    amount:=amt,zip:=Menu.zip m p k b M,selected:=selected A Δ k b h,paintTable:=names A Δ k h,
    output:=endAt A Δ k b h,first:=first A Δ k b h }

/-- The only RAM inputs to the ordinary chart lie below the public ROM shelf.
The terminal capacity condition refers to the last genuinely written word. -/
structure Room (A : Chart) (amt : Bank) (Δ k b h w H G : ℕ) : Prop where
  charts : ∀i : Fin (2^k-1), Frame.Room (A.sheet Δ k i.val) H G Δ k b (lanes h (unit k b)) w
  roster : A.roster.base+A.roster.size≤A.origin
  weights : A.weights.base+A.weights.size≤A.origin
  counts : amt.Fits w A.origin
  rows : H*chunks G (lanes h (unit k b))≤amt.size
  candidates : 2^(k+1)≤A.page
  wide : 2*unit k b≤h
  embed : h≤w
  endFits : endAt A Δ k b h+2^k*(H*chunks G (lanes h (unit k b)))<2^w

def memory (A : Chart) (hk : 0<k) (Δ H G b h D cap : ℕ) (m : Memory w) :=
  let M:=lanes h (unit k b)
  let a:=A.mountAll Δ H G k b M D cap (modulus hk) (fun i=> (seedAt k i).val) m
  let b':=Menu.mount (menu A Δ k) (2^(h/2)) hk b M a
  PackedWinnerRAM.mount hk (names A Δ k h) w M b'

private theorem chartLow (A : Chart) (i : Fin (2^k-1)) : (A.sheet Δ k i.val).fresh Δ k≤ menu A Δ k := by
  rw [Frame.sheet_next]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _

private theorem menuLow (A : Chart) (Δ k b h : ℕ) : menu A Δ k≤first A Δ k b h :=
  (Nat.le_add_right _ _).trans (Nat.le_add_right ..)

private theorem counts_before (A : Chart) (Δ k : ℕ) : A.origin≤ menu A Δ k := Nat.le_add_right ..

local notation "q" => (2^k-1)
local notation "r" => (2^(k+1))
local notation "s" => (1+k*2^k)
local notation "M" => lanes h (unit k b)

/-- The graph and the marked outgoing counts come from the previous stage.
All the other words required by the chooser are literal functions of its
public calendar. The following equality also keeps a dynamic earlier tape. -/
theorem initial (A : Chart) (amtBank : Bank) (hk : 0<k) (D cap : ℕ) (C : Room A amtBank Δ k b h w (2^ℓ) G)
    (rs : DynamicSplit.Roster ℓ Δ) (W amt : Fin G→Fin (2^ℓ)→Block k→ℕ) (m : Memory w)
    (resident : ∀v i,m (A.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (counts : Reads A.weights (fun v g=>DescentPackedColony.counts b (W g v)) M m)
    (amount : Reads amtBank (fun v g=>DescentPackedColony.counts b (amt g v)) M m) :
    let z:=memory A hk Δ (2^ℓ) G b h D cap m
    Initial (shelves A amtBank Δ k b h) hk rs W amt D cap b M z ∧ ∀u<A.origin,z u=m u := by
  let mid:=A.mountAll Δ (2^ℓ) G k b M D cap (modulus hk) (fun i=>(seedAt k i).val) m
  let a:=menu A Δ k
  let p:=2^(h/2)
  let hi:=names A Δ k h
  let rmem:=Menu.mount a p hk b M mid
  let z:=PackedWinnerRAM.mount hk hi w M rmem
  have ah : a≤hi := Nat.le_add_right ..
  have prior (u) (hu:u<a) : z u=mid u := (PackedWinnerRAM.mount_below hk hi w M rmem (hu.trans_le ah)).trans (Menu.lower a p hk b M mid hu)
  have live (u) (hu:u<A.origin) : z u=m u := (prior u (hu.trans_le (counts_before A Δ k))).trans
    (Frame.mountAll_frame A Δ (2^ℓ) G k b M D cap (modulus hk) _ m (Or.inl hu))
  have pub (t : Menu.Tag k) (e : Cell (Menu.bits k b M t)) :
      z ((Menu.bank a p k b M t).base+e.val)=rmem ((Menu.bank a p k b M t).base+e.val) := by
    apply PackedWinnerRAM.mount_below
    apply (Nat.add_lt_add_left (show e.val<(Menu.bank a p k b M t).size from e.isLt) _).trans_le
    exact Menu.end_bank a p k b M t (Menu.size_at k b h a t)
  obtain ⟨split,color,zip⟩:=Menu.reads a p hk b M mid (Menu.size_at k b h a)
  have amountRead (u : Row (2^ℓ) G M) :=
    (live _ ((Nat.add_lt_add_left ((row (2^ℓ) G M u).isLt.trans_le C.rows) amtBank.base).trans_le C.counts.2.2)).trans (amount u)
  refine ⟨⟨?_,amountRead,
    fun i=>⟨fun key=>(pub (.inr (.inr (i,false))) key).trans ((zip i).1 key),fun key=>(pub (.inr (.inr (i,true))) key).trans ((zip i).2 key)⟩,
    fun _ key=>(pub (.inl ()) key).trans (split key),fun j key=>(pub (.inr (.inl j)) key).trans (color j key),
    PackedWinnerRAM.mounted hk hi w M rmem⟩,live⟩
  intro i
  let chart:=A.sheet Δ k i.val
  let base:=Frame.startAt (first A Δ k b h) k A.page i
  apply AllSeeds.input_copy (chart.trialAt base Δ k b M)
    (Frame.trial_low chart (C.charts i) (chartLow A i)) rs W D cap (modulus hk) _ prior
  apply Frame.trial_input
  exact Frame.sourceReady A rs W D cap (modulus hk) (fun j=>(seedAt k j).val) m C.charts C.roster C.weights resident counts i

private theorem bank_mono {B : Bank} {a a' : ℕ} (old : B.Fits w a) (lower : a≤a') : B.Fits w a' :=
  ⟨old.1,old.2.1,old.2.2.trans lower⟩

private theorem final_bank_end (A : Chart) (base Δ b batch : ℕ) (hk : 0<k) :
    ((A.trialAt base Δ k b batch).source k).base+A.page=base+k*A.page := by
  cases k with
  | zero => exact False.elim (Nat.lt_irrefl _ hk)
  | succ j => change base+j*A.page+A.page=base+(j+1)*A.page; rw [Nat.succ_mul, Nat.add_assoc]

private theorem final_bank_size (A : Chart) (base Δ k b batch : ℕ) :
    ((A.trialAt base Δ k b batch).source k).size=A.page := by cases k <;> rfl

/-- The order of all low ROMs, scratch arenas, and selected result words
follows from the single explicit allocation of pages and candidate ranges. -/
theorem space (A : Chart) (amt : Bank) (hk : 0<k) (H G : ℕ) (C : Room A amt Δ k b h w H G) :
    Space (shelves A amt Δ k b h) w H G b M := by
  let S:=shelves A amt Δ k b h
  let pp:=2^(h/2)
  let lo:=menu A Δ k
  let dict:=names A Δ k h
  let hi:=first A Δ k b h
  let sw:=seedWork A Δ k b h
  let out:=selected A Δ k b h
  let cw:=colorWork A Δ k b h
  let last:=endAt A Δ k b h
  let n:=H*chunks G M
  let page:=A.page
  let chart:=fun i : Fin q=>A.sheet Δ k i.val
  have npos : 0<q := by have := Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide : 1<2);omega
  let z : Fin q:=⟨0,npos⟩
  have cap := C.charts z
  have np : n≤page := cap.cells
  have rp:=C.candidates
  have qp : q≤page := (Nat.sub_le _ _).trans ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_succ k)).trans rp)
  have pos : 0<page := Nat.two_pow_pos _
  have «until» : last+2^k*n<2^w := C.endFits
  have ranges : hi≤ sw ∧ sw+3*page+(q+1)=out ∧ out+page=cw ∧ cw+3*page+(r+1)=last :=
    ⟨Nat.le_add_right ..,rfl,rfl,rfl⟩
  obtain ⟨hs,so,oc,cl⟩:=ranges
  have pword : page<2^w := by omega
  have wide : 1<2^w := by
    apply Nat.one_lt_two_pow
    have:=C.wide;have:=C.embed;unfold unit at *;omega
  have lor : lo≤dict := Nat.le_add_right ..
  have dfirst : dict≤hi := Nat.le_add_right ..
  have freq : pp<2^w := by
    have hpos : 0<h := by have:=C.wide;dsimp [unit] at this;omega
    exact (Nat.pow_lt_pow_right (by decide) (Nat.div_lt_self hpos (by decide))).trans_le (Nat.pow_le_pow_right (by decide) C.embed)
  have immutable (t : Menu.Tag k) : (Menu.bank lo pp k b M t).base+(Menu.bank lo pp k b M t).size≤hi :=
    (Menu.end_bank lo pp k b M t (Menu.size_at k b h lo t)).trans dfirst
  have dfits (t : Menu.Tag k) (z : ℕ) (hz : hi≤z) : (Menu.bank lo pp k b M t).Fits w z :=
    ⟨Nat.two_pow_pos _,(Menu.size_at k b h lo t).trans_lt freq,(immutable t).trans hz⟩
  have fixed (i : Fin q) : (chart i).fresh Δ k≤hi := (chartLow A i).trans (lor.trans dfirst)
  have runRoom : AllSeeds.ArrayRoom S.layers hi H G k b M w :=
    Frame.allTrials_room chart hi page (fun _=>rfl) C.charts fixed (show sw<2^w by omega)
  have trialEnd (i : Fin q) : Frame.startAt hi k page i+(k+1)*page ≤ sw := by
    change hi+i.val*((k+1)*page)+(k+1)*page≤hi+q*((k+1)*page)
    rw [Nat.add_assoc, ← Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) hi
  have prior (i : Fin q) : (S.panels i).base+page≤ sw := by
    change (((chart i).trialAt (Frame.startAt hi k page i) Δ k b M).source k).base+(chart i).page ≤ sw
    rw [final_bank_end _ _ _ _ _ hk]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right page (Nat.le_succ k)) _).trans (trialEnd i)
  have ssize (i : Fin q) : (S.panels i).size=page :=
    final_bank_size (chart i) (Frame.startAt hi k page i) Δ k b M
  have sf (i : Fin q) : (S.panels i).Fits w sw :=
    ⟨Nat.two_pow_pos _,(ssize i) ▸ pword,by rw [ssize];exact prior i⟩
  have minFits {t f : ℕ} {work : ℕ} (src rom : Fin t→Bank)
      (srcSize : ∀i,n≤(src i).size) (srcSafe : ∀i,(src i).Fits w work)
      (romBits : ∀i,(rom i).bits=f*M) (romSafe : ∀i,(rom i).Fits w work)
      (entries : t≤page) (enough : work+3*page+t<2^w) :
      DescentPackedMinimum.Fits (minimum A work src rom) w f M H G :=
    ⟨srcSize,romBits,srcSafe,romSafe,by change work+(n+1)≤work+2*page;omega,entries,
      ⟨Nat.two_pow_pos _,pword,by change work+2*page+page≤work+3*page;omega⟩,enough,wide⟩
  have sfit : DescentPackedMinimum.Fits S.split w s M H G := minFits S.panels (fun _=>Menu.split lo pp k b M)
    (fun i=>(ssize i).symm ▸ np) sf (fun _=>rfl) (fun _=>dfits _ sw hs) qp (by omega)
  have colorFit : (⟨out,A.bits⟩:Bank).Fits w cw := ⟨pos,pword,oc.le⟩
  have afit : DescentPackedMinimum.Fits S.color w (PackedContribution.width k b) M H G :=
    minFits (fun _=>⟨out,A.bits⟩) (Menu.color lo pp k b M) (fun _=>np) (fun _=>colorFit)
      (fun _=>rfl) (fun j=>dfits (.inr (.inl j)) cw (by omega)) rp (by omega)
  have f1 : (1+k*2^k)*M≤h/2 := Menu.bit_bound k b h (.inl ())
  have muEq : S.mu=sw+3*page+(q-1):=rfl
  have paintEq : S.paint=cw+3*page+(r-1):=rfl
  have stops (i : Fin q) (d : ℕ) (earlier : d<k) :
        ((S.layers i).source (d+1)).base+n≤ sw := by
    change Frame.startAt hi k page i+d*page+n ≤ sw
    rw [Nat.add_assoc]
    apply (Nat.add_le_add_left _ _).trans (trialEnd i)
    calc d*page+n ≤ d*page+page := Nat.add_le_add_left np _
         _ = (d+1)*page := (Nat.succ_mul d page).symm
         _ ≤ (k+1)*page := Nat.mul_le_mul_right page (Nat.succ_le_succ earlier.le)
  refine ⟨runRoom,sfit,fun _=>rfl,stops,hs,fun _=>immutable (.inl ()),?_,C.rows,?_,?_,?_,?_,?_,?_,afit,
    fun _=>rfl,fun j=>immutable (.inr (.inl j)),?_,?_,le_rfl⟩
  · exact (Nat.add_le_add_left C.rows _).trans (C.counts.2.2.trans ((counts_before A Δ k).trans (lor.trans dfirst)))
  · exact bank_mono C.counts ((counts_before A Δ k).trans (lor.trans (dfirst.trans (show hi≤out by omega))))
  · intro i;exact ⟨immutable (.inr (.inr (i,false))),immutable (.inr (.inr (i,true)))⟩
  · intro i
    exact ⟨dfits (.inr (.inr (i,false))) out (by omega),dfits (.inr (.inr (i,true))) out (by omega),rfl,rfl⟩
  · refine ⟨Nat.two_pow_pos 0,wide,?_⟩;change S.mu+1≤out;omega
  · change sw≤out;omega
  · change out+n<2^w;omega
  · change out+n≤cw;omega
  · refine ⟨fun i=>bank_mono (sf i) (by change sw≤last;omega),fun i=>(ssize i).symm ▸ np,
      ?_,(Nat.pow_le_pow_right (by decide) f1).trans_lt freq,rp.trans pword.le,?_,?_,«until»,wide⟩
    · change hi≤last;omega
    · change S.mu<last;omega
    · change S.paint<last;omega

/-- Build all per-table bounds from the two real physical predecessor banks,
the page exponent and the ultimate last output address. -/
theorem room_of_page (A : Chart) (amt : Bank) (hk : 0<k) (H G : ℕ)
    (sizes : A.bits=Frame.pageBits H G k b M) (roster : A.roster.Fits w A.origin) (ports : H*Δ≤A.roster.size)
    (weight : A.weights.Fits w A.origin) (nw : H*chunks G M≤A.weights.size)
    (marks : amt.Fits w A.origin) (nm : H*chunks G M≤amt.size)
    (wide : 2*unit k b≤h) (hw : h≤w) (terminal : endAt A Δ k b h+2^k*(H*chunks G M)<2^w) :
    Room A amt Δ k b h w H G := by
  have binary : k≤k*2^k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have height : k+1≤DescentPackedColony.unit k b := by
    calc k+1 = 1+k := Nat.add_comm ..
         _ ≤ 1+k*2^k := Nat.add_le_add_left binary 1
         _ ≤ (1+k*2^k)+(1+k*2^k) := Nat.le_add_right ..
         _ ≤ DescentPackedColony.unit k b := le_max_left ..
  have gain : 0<M := (occupancy h (unit k b) (by dsimp [unit];omega) wide).1
  have bound:=height.trans (Nat.le_mul_of_pos_right (DescentPackedColony.unit k b) gain)
  have entries : r≤A.page := by
    change 2^(k+1)≤2^A.bits
    rw [sizes]
    exact (Nat.pow_le_pow_right (by decide) bound).trans (Frame.enough H G k b M).2.2
  have qpos:0<q := Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hk) (by decide : 1<2))
  have segment:=(Nat.le_mul_of_pos_left ((k+1)*A.page) qpos)
  have lower:=menuLow A Δ k b h
  have complete : A.sheetEnd Δ k q+(k+1)*A.page<2^w := by
    change menu A Δ k+(k+1)*A.page<_
    unfold endAt colorWork selected seedWork at terminal
    omega
  exact ⟨Frame.rooms A sizes roster ports weight nw complete,roster.2.2,weight.2.2,marks,nm,entries,wide,hw,terminal⟩


end
end Hierarchy.DescentPackedColony.Phase.Arena

end OAI
