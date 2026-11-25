import OAI.Hierarchy.DescentHaloChartHeader
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # One static chart image shared by the ordinal and hub broadcasts -/
namespace Hierarchy.DescentRawCablePanel.DonorChartBook
open DescentSIMDLookup DescentHaloPackedRebase ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M P : ℕ) {w : ℕ}
local notation "n" => H*chunks G M

def pages (M P : ℕ) := (M+1)*(P+1)
def words := n+(n+P*pages M P)
abbrev Index := Fin n ⊕ (Fin n ⊕ (Fin P × Fin (pages M P)))

def ordinal : Index H G M P ≃ Fin (words H G M P) :=
  let last:=((Equiv.refl (Fin n)).sumCongr (finProdFinEquiv (m:=P) («n»:=pages M P))).trans finSumFinEquiv
  ((Equiv.refl (Fin n)).sumCongr last).trans finSumFinEquiv

def tables (base : ℕ) (values : Bank) : Headers P where
  chart:=values
  block:=⟨base,Nat.clog 2 n⟩
  live:=⟨base+n,Nat.clog 2 n⟩
  spread i:=⟨base+n+n+i.val*pages M P,Nat.clog 2 (pages M P)⟩

def address (base : ℕ) : Index H G M P→ℕ
  | .inl i=>base+i.val
  | .inr (.inl i)=>base+n+i.val
  | .inr (.inr (j,x))=>base+n+n+j.val*pages M P+x.val

private theorem address_eq (base : ℕ) (i : Index H G M P) :
    address H G M P base i=base+(ordinal H G M P i).val := by
  rcases i with x|x|⟨j,x⟩
  · rfl
  · change base+n+x.val=base+(n+x.val)
    exact Nat.add_assoc ..
  · change base+n+n+j.val*pages M P+x.val=base+(n+(n+(x.val+pages M P*j.val)))
    ring

def contents : Index H G M P→ℕ
  | .inl i=>((row H G M).symm i).1.val*P
  | .inr (.inl i)=>used G M ((row H G M).symm i).2.val*(P+1)
  | .inr (.inr (j,x))=>
    let p : Fin (M+1)×Fin (P+1):=finProdFinEquiv.symm x
    shift P M j.val p.1.val p.2.val

def data (i : ℕ) :=
  if ok:i<words H G M P then contents H G M P ((ordinal H G M P).symm ⟨i,ok⟩) else 0

def install (base w : ℕ) := DescentStaticWordColumn.program w base (data H G M P) (words H G M P)
def image (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (data H G M P) m (words H G M P)

/-- These three columns are common to every dynamic chart and every
selected layout. A later write to the actual rank or hub vector preserves them. -/
structure Static (base : ℕ) (m : Memory w) : Prop where
  read : ∀i,m (address H G M P base i)=(contents H G M P i:Word w)

theorem mount (base : ℕ) (m : Memory w) (limit : base+words H G M P<2^w) :
    let result:=image H G M P base m
    (install H G M P base w).Exec m result (4+10*words H G M P) ∧ Static H G M P base result ∧
    ∀a,a<base ∨ base+words H G M P≤a→ result a=m a := by
  intro result
  refine ⟨DescentStaticWordColumn.mount base _ _ m limit,⟨?_⟩,DescentStaticWordColumn.frame base _ _ m⟩
  intro i
  rw [address_eq H G M P base i]
  have read:=DescentStaticWordColumn.read base _ (data H G M P) m (j:=(ordinal H G M P i).val) (ordinal H G M P i).isLt
  simpa only [result,image,data,dite_eq_left (ordinal H G M P i).isLt,Fin.eta,Equiv.symm_apply_apply] using read

theorem transfer {base : ℕ} {before after : Memory w} (static : Static H G M P base before)
    (kept : ∀a,base≤a→a<base+words H G M P→after a=before a) : Static H G M P base after := by
  constructor
  intro i
  have atOrdinal:=address_eq H G M P base i
  exact (kept _ (by rw [atOrdinal];omega) (by rw [atOrdinal];have:=(ordinal H G M P i).isLt;omega)).trans (static.read i)

theorem ready (base : ℕ) (values : Bank) (actual : Fin H→Fin P→Fin (P+1)) (mem : Memory w)
    (seals : Static H G M P base mem)
    (chart : ∀v j,mem (values.base+(finProdFinEquiv (v,j)).val)=((actual v j).val:Word w)) :
    Reads (tables H G M P base values) actual M G mem := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v j
    simpa only [tables,finProdFinEquiv_apply_val,Nat.mul_comm P v.val,Nat.add_comm j.val] using chart v j
  · intro p
    simpa [tables,address,contents] using seals.read (.inl (row H G M p))
  · intro p
    simpa [tables,address,contents] using seals.read (.inr (.inl (row H G M p)))
  · intro j val l
    simpa [tables,address,contents,finProdFinEquiv_apply_val,Nat.mul_comm (P+1) l.val,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      seals.read (.inr (.inr (j,finProdFinEquiv (l,val))))

def endAddr (base : ℕ) :=
  base+words H G M P+2^Nat.clog 2 (H*chunks G M)+2^Nat.clog 2 (pages M P)+2^Nat.clog 2 (H*P)

theorem geometry (base first out : ℕ) (previous : first≤base) (space : endAddr H G M P base≤out) (width : out<2^w) :
    DescentHaloPackedRebase.Fits (tables H G M P base ⟨first,Nat.clog 2 (H*P)⟩) H G M w out := by
  have bank (a bits : ℕ) (bound : a+2^bits≤out) : (⟨a,bits⟩:Bank).Fits w out :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt width),bound⟩
  have curves (i : Fin P) : i.val*pages M P≤P*pages M P:=Nat.mul_le_mul_right _ i.isLt.le
  have bounds (rows panel blockRoom spreadRoom chartRoom : ℕ)
      (total : base+(rows+(rows+panel))+blockRoom+spreadRoom+chartRoom≤out) :
      first+chartRoom≤out ∧ base+blockRoom≤out ∧ base+rows+blockRoom≤out ∧
      ∀ offset : ℕ, offset≤panel → base+rows+rows+offset+spreadRoom≤out := by
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro offset limit
    omega
  have room := bounds n (P*pages M P) (2^Nat.clog 2 n)
    (2^Nat.clog 2 (pages M P)) (2^Nat.clog 2 (H*P)) space
  exact ⟨bank _ _ room.1,bank _ _ room.2.1,bank _ _ room.2.2.1,
    fun i=>bank _ _ (room.2.2.2 _ (curves i)),
    Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,
    fun _=>Nat.le_pow_clog (by decide) _⟩

end
end Hierarchy.DescentRawCablePanel.DonorChartBook

end OAI
