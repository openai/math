import OAI.Hierarchy.DescentSharedBookScan
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # The shared scalar fallback book mounted from its public finite coordinates -/
namespace Hierarchy.DescentSharedBookScan.Public
open DescentFallbackShapeTable DescentNativeFallbackShapes DescentPackedColony.Phase.Arena
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def «fields» (r Y D : ℕ) : Fields r Y D≃Fin (width r Y D) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- The operation set is fixed independently of hosts, groups, and measured rows. -/
def opOrdinal :=Fintype.equivFin Op
def lanes:=Fintype.card Op+4
def maxRows (r Y Δ H cap : ℕ) :=
  max (H*width r Y Δ) (max (r+1) (max (2^r) (max (Y+1) (imageSize r Y cap))))
def bits (r Y Δ H cap : ℕ) :=Nat.clog 2 (maxRows r Y Δ H cap)
def page (base digits i : ℕ) : Bank :=⟨base+i*2^digits,digits⟩
def bank (base r Y Δ H cap : ℕ) (oldNeighbors oldHub : Bank) : Chart :=
  let b:=bits r Y Δ H cap
  let first:=Fintype.card Op
  ⟨fun op=>page base b (opOrdinal op).val,oldNeighbors,oldHub,
    ⟨page base b first,page base b (first+1),page base b (first+2),page base b (first+3)⟩⟩
def stop (base r Y Δ H cap : ℕ) :=base+lanes*2^(bits r Y Δ H cap)

def entry (r D g f Y Δ H cap j x : ℕ) : ℕ :=
  let n:=Fintype.card Op
  if o:j<n then
    if h:x<H*width r Y Δ then
      let a : Fin H×Fin (width r Y Δ):=finProdFinEquiv.symm ⟨x,h⟩
      datum (opOrdinal.symm ⟨j,o⟩) a.1 ((«fields» r Y Δ).symm a.2)
    else 0
  else if j=n then x*(strides r Y cap).1
  else if j=n+1 then x*(strides r Y cap).2.1
  else if j=n+2 then x*(strides r Y cap).2.2
  else table r D g f Y cap x

def literals (base r D g f Y Δ H cap w : ℕ) : Image w :=
  let pitch:=2^(bits r Y Δ H cap)
  ⟨base,stop base r Y Δ H cap,fun z=>
    let v:=z-base
    ((entry r D g f Y Δ H cap (v/pitch) (v%pitch)):Word w)⟩

variable {r D g f Y Δ H cap base w : ℕ}
local notation "b" => bits r Y Δ H cap
local notation "I" => literals base r D g f Y Δ H cap w
local notation "room" => maxRows r Y Δ H cap

private theorem datum_read (m : Memory w) (resident : (I).Resident m) (j x : ℕ) (hj:j<lanes) (hx:x<2^b) :
    m ((page base b j).base+x)=((entry r D g f Y Δ H cap j x):Word w) := by
  have hi:=Nat.mul_le_mul_right (2^b) hj
  rw [Nat.succ_mul] at hi
  have word:=resident ((page base b j).base+x) (by change base≤base+_+_;omega)
    (by change base+j*2^b+x<base+lanes*2^b;omega)
  have diff:base+j*2^b+x-base=j*2^b+x:=by omega
  have quotient:(j*2^b+x)/2^b=j:=by
    rw [Nat.mul_comm j,Nat.mul_add_div (Nat.two_pow_pos b),Nat.div_eq_of_lt hx,Nat.add_zero]
  have remainder:(j*2^b+x)%2^b=x:=by
    rw [Nat.mul_comm j,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hx]
  simpa [literals,page,diff,quotient,remainder] using word

theorem stored (oldNeighbors oldHub : Bank) (m : Memory w) (available : stop base r Y Δ H cap<2^w)
    (resident : (I).Resident m) :
    let B:=bank base r Y Δ H cap oldNeighbors oldHub
    fixed B r Y Δ H m ∧ DescentNativeFallbackShapes.Stored B.shapes r D g f Y cap m := by
  intro B
  have word:=datum_read (r:=r) (D:=D) (g:=g) (f:=f) (Y:=Y) (Δ:=Δ) (H:=H) (cap:=cap) (base:=base) m resident
  have capacity : room≤2^b:=Nat.le_pow_clog (by decide) _
  have caps : H*width r Y Δ≤2^b ∧ r+1≤2^b ∧ 2^r≤2^b ∧ Y+1≤2^b ∧ imageSize r Y cap≤2^b:=by
    simpa only [maxRows,max_le_iff] using capacity
  obtain ⟨ops,depths,offsets,rowsCap,allCode⟩:=caps
  have payload:2^b<2^w:=by
    have one:1≤lanes:=by simp [lanes]
    have limit:=Nat.mul_le_mul_right (2^b) one
    rw [Nat.one_mul] at limit
    change base+lanes*2^b<2^w at available
    omega
  constructor
  · intro op v p
    have bound: (absolute v p).val<H*width r Y Δ:=(absolute v p).isLt
    have evaluated:=word (opOrdinal op).val (absolute v p).val (by
      have:= (opOrdinal op).isLt;dsimp [lanes];omega) (bound.trans_le ops)
    change m ((page base b (opOrdinal op).val).base+(absolute v p).val)=_
    rw [evaluated]
    simp only [entry, dite_eq_left (opOrdinal op).isLt, dite_eq_left bound]
    change ((datum (opOrdinal.symm (opOrdinal op)) (finProdFinEquiv.symm (absolute v p)).1
      ((«fields» r Y Δ).symm (finProdFinEquiv.symm (absolute v p)).2) : ℕ) : Word w) = _
    rw [show absolute v p = finProdFinEquiv (v, («fields» r Y Δ) p) from rfl]
    simp only [Equiv.symm_apply_apply]
  · refine ⟨depths,offsets,rowsCap,allCode,?_,?_,?_,?_,?_⟩
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> exact payload
    · intro x hx
      exact (word (Fintype.card Op) x (by simp [lanes]) ((Nat.lt_succ_of_le hx).trans_le depths)).trans (by simp [entry])
    · intro x hx
      exact (word (Fintype.card Op+1) x (by simp [lanes]) (hx.trans_le offsets)).trans (by simp [entry])
    · intro x hx
      exact (word (Fintype.card Op+2) x (by simp [lanes]) (hx.trans_le rowsCap)).trans (by simp [entry])
    · intro x hx
      exact (word (Fintype.card Op+3) x (by simp [lanes]) (hx.trans_le allCode)).trans (by simp [entry])

/-- The only nonliteral fields of this shared chart are the prior host hub/peer columns. -/
theorem room_at (oldNeighbors oldHub : Bank) {target : ℕ} (ceiling : stop base r Y Δ H cap≤target)
    (fits : target<2^w) (neighbor : oldNeighbors.Fits w target) (hh : oldHub.Fits w target)
    (peers : H*Δ≤oldNeighbors.size) (hubs : H≤oldHub.size) (racks : H<2^w) (slots : Δ+1<2^w) :
    Room (bank base r Y Δ H cap oldNeighbors oldHub) r Y Δ H w target := by
  refine ⟨?_,⟨neighbor,peers⟩,⟨hh,hubs⟩,racks,slots⟩
  intro op
  have available:room≤2^b:=Nat.le_pow_clog (by decide) _
  have cells:H*width r Y Δ≤room:=le_max_left ..
  have endCap:=Nat.mul_le_mul_right (2^b) (show (opOrdinal op).val+1≤lanes by
    have atPos:=(opOrdinal op).isLt;unfold lanes;omega)
  rw [Nat.succ_mul] at endCap
  have bound:base+(opOrdinal op).val*2^b+2^b≤target:=by unfold stop at ceiling;omega
  exact ⟨⟨Nat.two_pow_pos _,by change 2^b<2^w;omega,bound⟩,cells.trans available⟩

theorem installed (oldNeighbors oldHub : Bank) (m : Memory w) (available : stop base r Y Δ H cap<2^w) :
    let B:=bank base r Y Δ H cap oldNeighbors oldHub
    (I).program.Exec m ((I).output m) (4+10*(lanes*2^b)) ∧ CheapCode (I).program ∧
    fixed B r Y Δ H ((I).output m) ∧ DescentNativeFallbackShapes.Stored B.shapes r D g f Y cap ((I).output m) ∧
    ∀x,x<base ∨ stop base r Y Δ H cap≤x→(I).output m x=m x := by
  intro B
  have len:(I).length=lanes*2^b:=by simp [literals,Image.length,stop]
  obtain ⟨run,resident,frame⟩:=(I).issue m (by change base+(I).length<_;rw [len];exact available)
  obtain ⟨controls,data⟩:=stored oldNeighbors oldHub ((I).output m) available resident
  refine ⟨?_, (I).hardware.1, controls, data, frame⟩
  rw [← len]
  exact run

end
end Hierarchy.DescentSharedBookScan.Public

end OAI
