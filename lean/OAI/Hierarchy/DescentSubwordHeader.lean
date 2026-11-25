import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentPackedSubwords

namespace OAI
/-! # Fixed CPU words for the packed subword splitter -/
namespace Hierarchy.DescentSIMDLookup.Subwords
open DescentPackedColony.Phase.Arena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {K H G R M w a : ℕ}

def chart (base a H G R M : ℕ) : Tables :=
  let N:=H*chunks G M
  ⟨⟨base,Nat.clog 2 N⟩,⟨base+N,Nat.clog 2 N⟩,⟨base+2*N,Nat.clog 2 (R*stride a R M)⟩⟩

def endAt (base a H G R M : ℕ) := base+2*(H*chunks G M)+R*stride a R M

def literals (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) : Image w :=
  let T:=chart base a H G R M
  let N:=H*chunks G M
  ⟨base,endAt base a H G R M,fun z=>
    if hp : T.parentRows.base≤z ∧ z<T.parentRows.base+N then
      let p:=(row H G M).symm ⟨z-T.parentRows.base,by omega⟩
      ((row H G (R*M) (parent size ratio pos p)).val:Word w)
    else if ho : T.offsets.base≤z ∧ z<T.offsets.base+N then
      let p:=(row H G M).symm ⟨z-T.offsets.base,by omega⟩
      ((part ratio p).val*stride a R M:ℕ)
    else if hd:T.dictionary.base≤z ∧ z<T.dictionary.base+R*stride a R M then
      let j : Fin (R*stride a R M):=⟨z-T.dictionary.base,by omega⟩
      let p : Fin R×Cell (a*(R*M)):=finProdFinEquiv.symm j
      ((take a M p.1 p.2).val:Word w)
    else 0⟩

set_option maxHeartbeats 800000 in
theorem actual (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (mem : Memory w)
    (pub : (literals base H a size ratio pos).Resident mem) :
    Static (a:=a) (H:=H) (chart base a H G R M) size ratio pos mem := by
  let T:=chart base a H G R M
  let N:=H*chunks G M
  have word (z : ℕ) (lo : base≤z) (hi : z<endAt base a H G R M) :=
    pub z lo hi
  constructor
  · intro p
    let u:=row H G M p
    have small:=u.isLt
    have here : T.parentRows.base≤T.parentRows.base+u.val ∧ T.parentRows.base+u.val<T.parentRows.base+N := ⟨by omega,by omega⟩
    rw [word (T.parentRows.base+u.val) (by dsimp [T,chart];omega) (by dsimp [T,chart,endAt,N] at *;omega)]
    dsimp only [T,N,u] at here ⊢
    simp only [literals,dite_eq_left here,Nat.add_sub_cancel_left,Fin.eta,Equiv.symm_apply_apply]
  constructor
  · intro p
    let u:=row H G M p
    have small:=u.isLt
    have no : ¬(T.parentRows.base≤T.offsets.base+u.val ∧ T.offsets.base+u.val<T.parentRows.base+N) := by dsimp [T,chart,N];omega
    have here : T.offsets.base≤T.offsets.base+u.val ∧ T.offsets.base+u.val<T.offsets.base+N := ⟨by omega,by omega⟩
    rw [word (T.offsets.base+u.val) (by dsimp [T,chart];omega) (by dsimp [T,chart,endAt,N] at *;omega)]
    dsimp only [T,N,u] at no here ⊢
    simp only [literals,dite_eq_right no,dite_eq_left here,Nat.add_sub_cancel_left,Fin.eta,Equiv.symm_apply_apply]
  · intro i z
    let v : Fin (R*stride a R M):=finProdFinEquiv (i,z)
    have locate : v.val=i.val*stride a R M+z.val := by
      change z.val+stride a R M*i.val=i.val*stride a R M+z.val
      ring
    have inverse : (finProdFinEquiv : Fin R×Cell (a*(R*M))≃Fin (R*stride a R M)).symm v=(i,z) :=
      Equiv.symm_apply_apply _ _
    have bound:=v.isLt
    have lo : base≤T.dictionary.base+v.val := by dsimp [T,chart];omega
    have hi : T.dictionary.base+v.val<endAt base a H G R M := by dsimp [T,chart,endAt];omega
    have np : ¬(T.parentRows.base≤T.dictionary.base+v.val ∧ T.dictionary.base+v.val<T.parentRows.base+N):=by dsimp [T,chart,N];omega
    have no : ¬(T.offsets.base≤T.dictionary.base+v.val ∧ T.dictionary.base+v.val<T.offsets.base+N):=by dsimp [T,chart,N];omega
    have hd : T.dictionary.base≤T.dictionary.base+v.val ∧ T.dictionary.base+v.val<T.dictionary.base+R*stride a R M:=⟨by omega,by omega⟩
    rw [←locate,word _ lo hi]
    dsimp only [T,N,v] at np no hd inverse ⊢
    simp only [literals,dite_eq_right np,dite_eq_right no,dite_eq_left hd,Nat.add_sub_cancel_left,Fin.eta]
    rw [inverse]

theorem length_eq (base H a : ℕ) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) :
    (literals (w:=w) base H a size ratio pos).length=2*(H*chunks G M)+R*stride a R M := by
  simp [Image.length,literals,endAt]; omega

end
end Hierarchy.DescentSIMDLookup.Subwords

end OAI
