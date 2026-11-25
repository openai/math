import OAI.Hierarchy.DescentPackedRectangle
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # The seven public columns for the packed estimator contain only public row coordinates -/
namespace Hierarchy.DescentPackedRectangle
open DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H u l D w : ℕ}
local notation "k" => u+l
local notation "N" => H*(k+1)+H*D
local notation "R" => Rows H k D
local notation "ord" => rowOrd H k D

def shelf (start n : ℕ) (field : Fin n→ℕ) (prior : Memory w) : Memory w :=
  fun a=>if ha : start≤a ∧ a<start+n then (field ⟨a-start,by omega⟩:Word w) else prior a

theorem shelf_at {n : ℕ} (start : ℕ) (field : Fin n→ℕ) (prior : Memory w) (i : Fin n) :
    shelf start n field prior (start+i.val)=(field i:Word w) := by simp [shelf,i.isLt]

theorem shelf_frame {n : ℕ} (start : ℕ) (field : Fin n→ℕ) (prior : Memory w) (a : ℕ) (other : a<start ∨ start+n≤a) :
    shelf start n field prior a=prior a := by
  have h : ¬(start≤a ∧ a<start+n) := by omega
  simp only [shelf,dite_eq_right h]

def words (H u l D : ℕ) :=
  let rows := H*(u+l+1)+H*D
  4*rows+3*(rows*2^u)

def metadata (lo : ℕ) (depth peers : Bank) : Tape where
  tag:=⟨lo,Nat.clog 2 N⟩
  owner:=⟨lo+N,Nat.clog 2 N⟩
  offset:=⟨lo+2*N,Nat.clog 2 N⟩
  tariff:=⟨lo+3*N,Nat.clog 2 N⟩
  depth:=depth
  neighbor:=peers

def gather (lo : ℕ) (live sites flows : Bank) : Gather where
  owner:=⟨lo+4*N,Nat.clog 2 (N*2^u)⟩
  kind:=⟨lo+4*N+N*2^u,Nat.clog 2 (N*2^u)⟩
  pointer:=⟨lo+4*N+2*(N*2^u),Nat.clog 2 (N*2^u)⟩
  live:=live
  sites:=sites
  flows:=flows

def metaLiteral (f B K : ℕ) (a : Fin (4*N)) : ℕ :=
  if hn : 0<N then
    let t:R:=(rowOrd H (u+l) D).symm ⟨a.val%N,Nat.mod_lt _ hn⟩
    if a.val<N then tag t else if a.val<2*N then (owner t).val else if a.val<3*N then arg t else tariff f B K t
  else 0

def gatherLiteral (pitch : ℕ) (a : Fin (3*(N*2^u))) : ℕ :=
  if hn : 0<N*2^u then
    let z:=DescentPackedWalsh.unrow (H:=N) (u:=u) ⟨a.val%(N*2^u),Nat.mod_lt _ hn⟩
    let t:R:=(rowOrd H (u+l) D).symm z.1
    if a.val<N*2^u then z.1.val else if a.val<2*(N*2^u) then tag t else offset (H:=H) (u:=u) (l:=l) (D:=D) pitch t z.2
  else 0

def mount (lo pitch f B K H u l D : ℕ) (prior : Memory w) :=
  let rows := H*(u+l+1)+H*D
  shelf (lo+4*rows) (3*(rows*2^u)) (gatherLiteral (H:=H) (u:=u) (l:=l) (D:=D) pitch)
    (shelf lo (4*rows) (metaLiteral (H:=H) (u:=u) (l:=l) (D:=D) f B K) prior)

theorem mount_frame (lo pitch f B K H u l D : ℕ) (prior : Memory w) (a : ℕ)
    (other : a<lo ∨ lo+words H u l D≤a) :
    mount lo pitch f B K H u l D prior a=prior a := by
  dsimp only [words] at other
  dsimp only [mount]
  rw [shelf_frame _ _ _ _ (by omega),shelf_frame _ _ _ _ (by omega)]

private theorem column_lt {n i j b : ℕ} (hi : i<n) :
    j*n+i < b*n ↔ j<b := by
  constructor
  · intro h
    by_contra! hj
    have hle := Nat.mul_le_mul_right n hj
    omega
  · intro h
    have hle := Nat.mul_le_mul_right n (show j+1≤b from h)
    rw [Nat.add_mul,Nat.one_mul] at hle
    omega

private theorem meta_read (lo pitch f B K : ℕ) (prior : Memory w) (t : R) (j : Fin 4) :
    mount lo pitch f B K H u l D prior (lo+j.val*N+(ord t).val)=
      ((if j.val=0 then tag t else if j.val=1 then (owner t).val else if j.val=2 then arg t else tariff f B K t):Word w) := by
  have hi:=(ord t).isLt
  have full : j.val*N+(ord t).val<4*N := (column_lt hi).2 j.isLt
  let a:Fin (4*N):=⟨_,full⟩
  have find:(a.val%N)=(ord t).val:= Nat.mul_add_mod_of_lt hi
  have hn : 0<N := Nat.zero_lt_of_lt hi
  have idx : (⟨a.val%N,Nat.mod_lt _ hn⟩ : Fin N) = ord t := Fin.ext find
  have c0 : a.val<N ↔ j.val<1 := by simpa only [Nat.one_mul] using (column_lt (j:=j.val) (b:=1) hi)
  have c1 : a.val<2*N ↔ j.val<2 := column_lt hi
  have c2 : a.val<3*N ↔ j.val<3 := column_lt hi
  dsimp only [mount]
  rw [shelf_frame _ _ _ _ (.inl (by omega)),Nat.add_assoc lo (j.val*N) (ord t).val]
  change shelf lo (4*N) _ prior (lo+a.val)=_
  rw [shelf_at]
  simp only [metaLiteral,dite_eq_left hn,idx,Equiv.symm_apply_apply,c0,c1,c2]
  split_ifs <;> first | rfl | omega

private theorem gather_read (lo pitch f B K : ℕ) (prior : Memory w) (t : R) (p : Cube u) (j : Fin 3) :
    mount lo pitch f B K H u l D prior (lo+4*N+j.val*(N*2^u)+(DescentPackedWalsh.row (ord t) p).val)=
      ((if j.val=0 then (ord t).val else if j.val=1 then tag t else offset (H:=H) (u:=u) (l:=l) (D:=D) pitch t p):Word w) := by
  let i:=DescentPackedWalsh.row (ord t) p
  have hi:=i.isLt
  have full : j.val*(N*2^u)+i.val<3*(N*2^u) := (column_lt hi).2 j.isLt
  let a:Fin (3*(N*2^u)):=⟨_,full⟩
  have find:(a.val%(N*2^u))=i.val:= Nat.mul_add_mod_of_lt hi
  have hn : 0<N*2^u := Nat.zero_lt_of_lt hi
  have idx : (⟨a.val%(N*2^u),Nat.mod_lt _ hn⟩ : Fin (N*2^u)) = i := Fin.ext find
  have c0 : a.val<N*2^u ↔ j.val<1 := by simpa only [Nat.one_mul] using (column_lt (j:=j.val) (b:=1) hi)
  have c1 : a.val<2*(N*2^u) ↔ j.val<2 := column_lt hi
  dsimp only [mount]
  rw [Nat.add_assoc (lo+4*N)]
  change shelf (lo+4*N) _ _ _ (lo+4*N+a.val)=_
  rw [shelf_at]
  simp only [gatherLiteral,dite_eq_left hn,idx,i,unrow_row,Equiv.symm_apply_apply,c0,c1]
  split_ifs <;> first | rfl | omega

theorem public_pins (lo pitch f B K : ℕ) (live sites flows : Bank) (prior : Memory w) :
    Public (gather (H:=H) (u:=u) (l:=l) (D:=D) lo live sites flows) pitch H u l D (mount lo pitch f B K H u l D prior) := by
  constructor
  · intro t p;simpa [gather] using gather_read lo pitch f B K prior t p 0
  · intro t p;simpa [gather] using gather_read lo pitch f B K prior t p 1
  · intro t p;simpa [gather] using gather_read lo pitch f B K prior t p 2

theorem meta_pins (lo pitch f B K : ℕ) (depth peers : Bank) (prior : Memory w)
    (dep : Fin H→ℕ) (next : Port H D→Option (Fin H))
    (dr : ∀v:Fin H,(mount lo pitch f B K H u l D prior) (depth.base+v.val)=(dep v:Word w))
    (nr : ∀p:Port H D,(mount lo pitch f B K H u l D prior) (peers.base+(slot H D p).val)=(target (next p):Word w)) :
    contents («k»:=u+l) (metadata (H:=H) (u:=u) (l:=l) (D:=D) lo depth peers) dep next f B K (mount lo pitch f B K H u l D prior) := by
  refine ⟨fun t=>?_,fun t=>?_,fun t=>?_,fun t=>?_,dr,nr⟩
  · simpa [metadata] using meta_read lo pitch f B K prior t 0
  · simpa [metadata] using meta_read lo pitch f B K prior t 1
  · simpa [metadata] using meta_read lo pitch f B K prior t 2
  · simpa [metadata] using meta_read lo pitch f B K prior t 3

theorem retained (lo pitch f B K : ℕ) (live sites flows depth peers : Bank)
    (prior now : Memory w) (dep : Fin H→ℕ) (next : Port H D→Option (Fin H))
    (literal : ∀a,lo≤a → a<lo+words H u l D → now a=mount lo pitch f B K H u l D prior a)
    (dr : ∀v:Fin H,now (depth.base+v.val)=(dep v:Word w))
    (nr : ∀p:Port H D,now (peers.base+(slot H D p).val)=(target (next p):Word w)) :
    contents («k»:=u+l) (metadata (H:=H) (u:=u) (l:=l) (D:=D) lo depth peers) dep next f B K now ∧
      Public (gather (H:=H) (u:=u) (l:=l) (D:=D) lo live sites flows) pitch H u l D now := by
  have mread (t:R) (j:Fin 4) :=meta_read lo pitch f B K prior t j
  have readM (t:R) (j:Fin 4) :
      now (lo+j.val*N+(ord t).val)=
        ((if j.val=0 then tag t else if j.val=1 then (owner t).val else if j.val=2 then arg t else tariff f B K t):Word w) := by
    have hi:=(ord t).isLt
    have h : j.val*N+(ord t).val<4*N := (column_lt hi).2 j.isLt
    exact (literal (lo+j.val*N+(ord t).val) (by omega) (by dsimp only [words]; omega)).trans (mread t j)
  have readD (t:R) (p:Cube u) (j:Fin 3) :
      now (lo+4*N+j.val*(N*2^u)+(DescentPackedWalsh.row (ord t) p).val)=
        ((if j.val=0 then (ord t).val else if j.val=1 then tag t else offset (H:=H) (u:=u) (l:=l) (D:=D) pitch t p):Word w) := by
    have hi:=(DescentPackedWalsh.row (ord t) p).isLt
    have h : j.val*(N*2^u)+(DescentPackedWalsh.row (ord t) p).val<3*(N*2^u) := (column_lt hi).2 j.isLt
    exact (literal (lo+4*N+j.val*(N*2^u)+(DescentPackedWalsh.row (ord t) p).val)
      (by omega) (by dsimp only [words]; omega)).trans (gather_read lo pitch f B K prior t p j)
  refine ⟨⟨fun t=>?_,fun t=>?_,fun t=>?_,fun t=>?_,dr,nr⟩,⟨fun t p=>?_,fun t p=>?_,fun t p=>?_⟩⟩
  · simpa [metadata] using readM t 0
  · simpa [metadata] using readM t 1
  · simpa [metadata] using readM t 2
  · simpa [metadata] using readM t 3
  · simpa [gather] using readD t p 0
  · simpa [gather] using readD t p 1
  · simpa [gather] using readD t p 2

end
end Hierarchy.DescentPackedRectangle

end OAI
