import OAI.Hierarchy.DescentMeasuredHeaderScan
import OAI.Hierarchy.DescentMeasuredMixer

namespace OAI
/-! # Scatter the previously measured block loads into the sparse mixer's row vectors -/
namespace Hierarchy.DescentMeasuredHeader
open DescentMeasuredWeights DescentPackedExchange DescentLinearLayouts ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H k Δ w : ℕ}
local notation "N" => H*(k+1)+H*Δ
local notation "R" => Rows H k Δ

def blockAddress (d : Fin (2^k)) := (DescentColonies.address k (DescentGLScoreRAM.vec d)).val
def sourceOrdinal : R→ℕ := Sum.elim (fun s=>s.1.val) (fun p=>(slot H Δ p).val)
def outputOrdinal (t : R) (d : Fin (2^k)) : Fin (N*2^k) := finProdFinEquiv (rowOrd H k Δ t,d)
def sourceAddress (t : R) (d : Fin (2^k)) := sourceOrdinal t*2^k+blockAddress d
theorem outputOrdinal_val (t : R) (d : Fin (2^k)) : (outputOrdinal t d).val=(rowOrd H k Δ t).val*2^k+d.val := by
  change d.val+2^k*(rowOrd H k Δ t).val=_;ac_rfl

structure DataTape where
  row : Bank
  tag : Bank
  addr : Bank
  live : Bank
  sites : Bank
  traffic : Bank

def dataBanks (D : DataTape) := [D.row,D.tag,D.addr,D.live,D.sites,D.traffic]
structure DataFits (D : DataTape) (w H k Δ out : ℕ) : Prop where
  fits : ∀z∈dataBanks D,z.Fits w out
  «meta» : ∀z∈[D.row,D.tag,D.addr],(H*(k+1)+H*Δ)*2^k≤z.size
  live : H*(k+1)+H*Δ≤D.live.size
  sites : H*2^k≤D.sites.size
  traffic : H*Δ*2^k≤D.traffic.size

/-- The first three columns are immutable and depend only on the board dimensions. -/
def dataStatic (D : DataTape) (m : Memory w) : Prop :=
  ∀(t : R)(d : Fin (2^k)),let i:=(outputOrdinal t d).val
    m (D.row.base+i)=((rowOrd H k Δ t).val:Word w) ∧ m (D.tag.base+i)=(tag t:Word w) ∧
    m (D.addr.base+i)=(sourceAddress t d:Word w)

def oldLoads (D : DataTape) (site : Fin H→Fin (2^k)→ℕ) (traffic : Port H Δ→Fin (2^k)→ℕ) (m : Memory w) : Prop :=
  (∀v z,m (D.sites.base+(v.val*2^k+z.val))=(site v z:Word w)) ∧
  ∀p z,m (D.traffic.base+((slot H Δ p).val*2^k+z.val))=(traffic p z:Word w)

def payloadExpr (D : DataTape) : Expr :=
  let read:=fun b=>Expr.lookup b .row
  .branch .eq (.lookup D.live (read D.row)) (.lit 0) (.lit 0)
    (.branch .eq (read D.tag) (.lit 0) (.lookup D.sites (read D.addr)) (.lookup D.traffic (read D.addr)))

theorem payloadFits (D : DataTape) {out : ℕ} (safe : DataFits D w H k Δ out) : (payloadExpr D).Fits w out := by
  simp only [payloadExpr,Expr.Fits]
  repeat' first | exact safe.fits _ (by simp [dataBanks]) | trivial | constructor

theorem payload_work (D : DataTape) : (payloadExpr D).work=48 := rfl

private theorem raw {w out : ℕ} (bank : Bank) (m : Memory w) (a : ℕ) (small : a<bank.size)
    (fit : bank.Fits w out) : bank.read m (a:Word w)=m (bank.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

theorem payload_read {out : ℕ} (D : DataTape) (safe : DataFits D w H k Δ out)
    (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) (site : Fin H→Fin (2^k)→ℕ)
    (traffic : Port H Δ→Fin (2^k)→ℕ) (m : Memory w) (wide : 1<2^w)
    (pointers : dataStatic (H:=H) (k:=k) (Δ:=Δ) D m) (old : oldLoads D site traffic m)
    (flags : ∀t:R,m (D.live.base+(rowOrd H k Δ t).val)=(isLive b next t:Word w))
    (t : R) (d : Fin (2^k)) :
    (payloadExpr D).eval m ((outputOrdinal t d).val:Word w)=
      (realLoad b next (fun v x=>site v (DescentColonies.address k x))
        (fun p x=>traffic p (DescentColonies.address k x)) t (DescentGLScoreRAM.vec d):Word w) := by
  obtain ⟨row,typ,ptr⟩:=pointers t d
  have «meta» (z) (hz:z∈[D.row,D.tag,D.addr]) :
      z.read m ((outputOrdinal t d).val:Word w)=m (z.base+(outputOrdinal t d).val) := by
    apply raw _ _ _ ((outputOrdinal t d).isLt.trans_le (safe.meta z hz))
    exact safe.fits _ (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl <;>simp [dataBanks])
  have rr := («meta» D.row (by simp)).trans row
  have tt := («meta» D.tag (by simp)).trans typ
  have pp := («meta» D.addr (by simp)).trans ptr
  have good:= (raw D.live m (rowOrd H k Δ t).val ((rowOrd H k Δ t).isLt.trans_le safe.live)
    (safe.fits _ (by simp [dataBanks]))).trans (flags t)
  have oneNe : (1:Word w)≠0 := by
    intro h
    have hv:=congrArg Fin.val h
    have hw : (1:Word w).val=1 := Fin.val_cast_of_lt wide
    simp only [Fin.val_zero,hw] at hv
    omega
  cases t with
  | inl s=>
    obtain ⟨v,j⟩:=s
    have bound : v.val*2^k+blockAddress d<H*2^k :=
      calc _ < (v.val+1)*2^k := by have:=(DescentColonies.address k (DescentGLScoreRAM.vec d)).isLt;simp only [blockAddress,Nat.succ_mul];omega
           _ ≤ _ := Nat.mul_le_mul_right _ v.isLt
    have paid:= (raw D.sites m _ (bound.trans_le safe.sites) (safe.fits _ (by simp [dataBanks]))).trans
      (old.1 v (DescentColonies.address k (DescentGLScoreRAM.vec d)))
    by_cases on : b v+j.val≤k <;> simp [payloadExpr,Expr.eval,Comparison.test,rr,tt,pp,good,
      isLive,tag,realLoad,sourceAddress,sourceOrdinal,oneNe,on]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using paid
  | inr p=>
    have bound : (slot H Δ p).val*2^k+blockAddress d<H*Δ*2^k :=
      calc _ < ((slot H Δ p).val+1)*2^k := by have:=(DescentColonies.address k (DescentGLScoreRAM.vec d)).isLt;simp only [blockAddress,Nat.succ_mul];omega
           _ ≤ _ := Nat.mul_le_mul_right _ (slot H Δ p).isLt
    have paid:= (raw D.traffic m _ (bound.trans_le safe.traffic) (safe.fits _ (by simp [dataBanks]))).trans
      (old.2 p (DescentColonies.address k (DescentGLScoreRAM.vec d)))
    cases hh:next p <;> simp [payloadExpr,Expr.eval,Comparison.test,rr,tt,pp,good,isLive,tag,
      realLoad,sourceAddress,sourceOrdinal,oneNe,hh]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using paid

def mixerTab (start origin : ℕ) (i : Fin N) : DescentMeasuredMixer.Header :=
  ⟨origin+i.val*2^k,start+N+i.val,start+2*N+i.val⟩

theorem data_program {out : ℕ} (D : DataTape) (safe : DataFits D w H k Δ out) (room : out+N*2^k<2^w)
    (m : Memory w) :
    (scan w out (N*2^k) (payloadExpr D)).Exec m (image out (N*2^k) (payloadExpr D) m)
      (4+(N*2^k)*(2*(payloadExpr D).work+4)) ∧ CheapCode (scan w out (N*2^k) (payloadExpr D)) :=
  ⟨scan_exec out (N*2^k) (payloadExpr D) m (payloadFits D safe) room,@scan_cheap _ _ _ _⟩

end
end Hierarchy.DescentMeasuredHeader

end OAI
