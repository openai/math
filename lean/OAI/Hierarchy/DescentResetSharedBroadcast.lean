import OAI.Hierarchy.DescentResetHaloBroadcast

namespace OAI
/-! # Reading a shared packed broadcast dictionary after later scalar writes -/
namespace Hierarchy.DescentResetSharedBroadcast
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentResetHaloBroadcast
open scoped Classical Fin.CommRing
open private DescentResetHaloBroadcast.point_read from OAI.Hierarchy.DescentResetHaloBroadcast
noncomputable section
variable {w H G M b S : ℕ}

/-- The scalar source and the dictionary may occur in either order below the ceiling. -/
theorem fits_existing (src : Bank) (root H G M b ceiling : ℕ) (old : src.Fits w ceiling)
    (room : endAt root H G M b < 2^w) (below : endAt root H G M b ≤ ceiling) :
    (expr src root H G M b).Fits w ceiling := by
  let N := H*chunks G M
  let u := 2^(bits H G M b)
  have past : root+2*N+u < 2^w := room
  have limit : root+2*N+u ≤ ceiling := below
  have bank {a : ℕ} (ha : a ≤ root+2*N) : (⟨a,bits H G M b⟩ : Bank).Fits w ceiling :=
    ⟨Nat.two_pow_pos _,by change u<2^w;omega,by change a+u ≤ ceiling;omega⟩
  exact ⟨bank le_rfl,⟨bank (by omega),trivial⟩,old,bank (by omega),trivial⟩

/-- Read the exact valid-lane packed word, using the saved row and mask columns
and the real source value in the current memory. -/
theorem read_existing (src : Bank) (root ceiling : ℕ) (site : Fin H→Fin S) (v : Fin S→Cell b) (m : Memory w)
    (old : src.Fits w ceiling) (available : S ≤ src.size)
    (read : ∀i,m (src.base+i.val)=((v i).val:Word w)) (room : endAt root H G M b < 2^w)
    (stored : ∀ i < count H G M b, m (root+i)=(literal b G M site i : Word w)) :
    Source (expr src root H G M b) (fun h (_ : Fin G)=>v (site h)) M m := by
  let total := count H G M b
  let N:=H*chunks G M
  let Z:=(M+1)*2^b
  let u:=2^(bits H G M b)
  let ids:Bank:=⟨root,bits H G M b⟩
  let masks:Bank:=⟨root+N,bits H G M b⟩
  let page:Bank:=⟨root+2*N,bits H G M b⟩
  have size : total+1≤u:=Nat.le_pow_clog (by decide) _
  have past : root+2*N+u<2^w:=room
  have totalEq:total=2*N+Z:=rfl
  have fitIds:ids.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,by change root+u≤root+2*N+u;omega⟩
  have fitMasks:masks.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,by change root+N+u≤root+2*N+u;omega⟩
  have fitPage:page.Fits w (endAt root H G M b):=⟨Nat.two_pow_pos _,by change u<2^w;omega,le_rfl⟩
  intro p
  let i:=row H G M p
  have small:i.val<N:=i.isLt
  have ir:i.val<u:=by omega
  let q:=used G M p.2.val
  let digit:=(v (site p.1)).val
  have bitsRoom:digit<2^b:=(v _).isLt
  have idx:q*2^b+digit<Z:=by
    calc
      _<q*2^b+2^b:=Nat.add_lt_add_left bitsRoom _
      _=(q+1)*2^b:=(Nat.succ_mul ..).symm
      _≤Z:=Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.min_le_left ..))
  have source : m (src.base+(site p.1).val)=(digit:Word w) := read _
  have idCell:m (ids.base+i.val)=((site p.1).val:Word w):=by
    change m (root+i.val)=_
    rw [stored i.val (by omega)]
    simp [literal,N,i,small]
  have maskCell:m (masks.base+i.val)=((q*2^b:ℕ):Word w):=by
    change m (root+N+i.val)=_
    rw [Nat.add_assoc,stored _ (show N+i.val<total by omega)]
    simp [literal,N,show ¬N+i.val<N by omega,small,i,q]
  have valCell:m (page.base+(q*2^b+digit))=((point b M q digit):Word w):=by
    change m ((root+2*N)+(q*2^b+digit))=_
    rw [Nat.add_assoc,stored _ (show 2*N+(q*2^b+digit)<total by omega)]
    have rest:¬2*N+(q*2^b+digit)-N<N:=by omega
    have first : ¬2*N+(q*2^b+digit)<N := by omega
    dsimp only [N] at first rest ⊢
    simp only [literal]
    split
    next hit => exact (first hit).elim
    next =>
      rw [Nat.add_sub_cancel_left,Nat.mul_comm q,Nat.mul_add_div (Nat.two_pow_pos b),
        Nat.div_eq_of_lt bitsRoom,Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt bitsRoom]
  change page.read m (masks.read m (i.val:Word w)+src.read m (ids.read m (i.val:Word w)))=_
  rw [bank_read masks m ir fitMasks,maskCell,bank_read ids m ir fitIds,idCell,
    bank_read src m ((site p.1).isLt.trans_le available) old,source,←Nat.cast_add,
    bank_read page m (by change q*2^b+digit<u; omega) fitPage,valCell]
  exact congrArg (fun n : ℕ => (n : Word w))
    (DescentResetHaloBroadcast.point_read (b:=b) (G:=G) (M:=M) v site p)

end
end Hierarchy.DescentResetSharedBroadcast

end OAI
