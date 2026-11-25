import OAI.Hierarchy.DescentTerminalPortPartners
import OAI.Hierarchy.DescentTerminalPaidRows

namespace OAI
/-! # Contiguous paid bits for each true unordered pair of terminal homes -/
namespace Hierarchy.DescentTerminalCableOrder
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

theorem digit_lt {a b i j stride : ℕ} (hi : i<stride) (hj : j<stride) :
    a*stride+i < b*stride+j ↔ a<b ∨ (a=b ∧ i<j) := by
  have sep {u v k : ℕ} (uBefore : u<v) (within : k<stride) : u*stride+k<v*stride := by
    have step:=Nat.mul_le_mul_right stride (Nat.succ_le_of_lt uBefore)
    rw [Nat.succ_mul] at step
    omega
  rcases lt_trichotomy a b with lt|eq|gt
  · have:=sep lt hi
    omega
  · subst b;omega
  · have:=sep gt hj
    omega

private theorem digit_inj {a b i j stride : ℕ} (hi : i<stride) (hj : j<stride)
    (h : a*stride+i=b*stride+j) : a=b ∧ i=j := by
  have left := digit_lt (a:=a) (b:=b) hi hj
  have right := digit_lt (a:=b) (b:=a) hj hi
  omega

section CableAddresses
variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S)

def pair (i j : Fin S) := min i.val j.val*S+max i.val j.val
theorem pair_swap (i j : Fin S) : pair i j=pair j i := by simp [pair,min_comm,max_comm]

theorem pair_iff (i j a b : Fin S) :
    pair i j=pair a b ↔ (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  constructor
  · intro eq
    have parts:=digit_inj (max_lt i.isLt j.isLt) (max_lt a.isLt b.isLt) eq
    simp only [Fin.ext_iff]
    omega
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · rfl
    · exact pair_swap ..

def pairIndex (e : N.Edge) := pair (home (N.src e)) (home (N.dst e))

variable (native : N.Edge ↪ Fin (Fintype.card N.Edge))

def edgeCode : N.Edge ↪ ℕ where
  toFun e:=pairIndex N home e*Fintype.card N.Edge+(native e).val
  inj' a b h:=native.injective (Fin.ext (digit_inj (native a).isLt (native b).isLt h).2)

omit [Fintype P] in
theorem edge_lt (e f : N.Edge) :
    edgeCode N home native e<edgeCode N home native f ↔
      pairIndex N home e<pairIndex N home f ∨ (pairIndex N home e=pairIndex N home f ∧ native e<native f) :=
  digit_lt (native e).isLt (native f).isLt

/-- Each earlier pair contributes exactly the widths of its cables. -/
def pairBase (i j : Fin S) :=
  ∑ e ∈ Finset.univ.filter (fun e=>pairIndex N home e<pair i j),N.width e

def pairMass (m : ℕ) :=
  ∑ e ∈ Finset.univ.filter (fun e=>pairIndex N home e=m),N.width e

def beforePair (m : ℕ) :=
  ∑ e ∈ Finset.univ.filter (fun e=>pairIndex N home e< m),N.width e

omit [Fintype P] in
theorem beforePair_succ (m : ℕ) :
    beforePair N home (m+1)=beforePair N home m+pairMass N home m := by
  unfold beforePair pairMass
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases early : pairIndex N home e< m
  · simp [early,Nat.lt_succ_of_lt early,Nat.ne_of_lt early]
  · by_cases now : pairIndex N home e=m
    · simp [now]
    · simp [early,now,show ¬pairIndex N home e< m+1 by omega]

omit [Fintype P] in
theorem pair_scan (m : ℕ) : beforePair N home m=∑ t ∈ Finset.range m,pairMass N home t := by
  induction m with
  | zero=>simp [beforePair]
  | succ m ih=> rw [beforePair_succ,ih,Finset.sum_range_succ]

omit [Fintype P] in
theorem pairBase_stream (i j : Fin S) :
    pairBase N home i j=∑ t ∈ Finset.range (pair i j),pairMass N home t := pair_scan N home _

omit [Fintype P] in
/-- Skipping any run of zero-volume pairs gives exactly the same next address. -/
theorem next_occupied {a b : ℕ} (less : a<b)
    (consecutive : ∀t,a<t → t<b → pairMass N home t=0) :
    beforePair N home b=beforePair N home a+pairMass N home a := by
  induction b with
  | zero=>omega
  | succ b ih=>
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ less) with eq|early
    · subst b;exact beforePair_succ N home a
    · rw [beforePair_succ,consecutive b early (Nat.lt_succ_self b),Nat.add_zero]
      exact ih early (fun t l h=>consecutive t l (Nat.lt_succ_of_lt h))

omit [Fintype P] in
theorem pairBase_swap (i j : Fin S) : pairBase N home i j=pairBase N home j i := by
  unfold pairBase
  rw [pair_swap i j]

def earlierCables (i j : Fin S) (e : N.Edge) :=
  ∑ f ∈ Finset.univ.filter (fun f=>pairIndex N home f=pair i j ∧ native f<native e),N.width f

omit [Fintype P] in
theorem edge_start (e : N.Edge) (i j : Fin S) (same : pairIndex N home e=pair i j) :
    ProtocolRAMPortRanks.prefix N.width (edgeCode N home native) e =
      pairBase N home i j+earlierCables N home native i j e := by
  classical
  unfold ProtocolRAMPortRanks.prefix pairBase earlierCables
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simp only [edge_lt N home native f e,same]
  by_cases a : pairIndex N home f<pair i j
  · simp [a,Nat.ne_of_lt a]
  · simp [a]

/-- The actual final piece can be shorter than a full p-bit word. -/
def pieceWidth (width p k : ℕ) := min p (width-k*p)

theorem piece_le (width p k : ℕ) : pieceWidth width p k≤p := Nat.min_le_left ..

theorem piece_before (width p k : ℕ) :
    ∑ t ∈ Finset.range k,pieceWidth width p t = min width (k*p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,ih,Nat.succ_mul]
    unfold pieceWidth
    omega

theorem piece_used {width p : ℕ} (hp : 0<p) (k : Fin (poolBatchCount width p)) : k.val*p<width := by
  have h:=k.isLt
  unfold poolBatchCount at h
  have hle:= (Nat.le_div_iff_mul_le hp).mp (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at hle
  omega

theorem whole_cable (width p : ℕ) (hp : 0<p) :
    ∑ t ∈ Finset.range (poolBatchCount width p),pieceWidth width p t=width := by
  rw [piece_before,Nat.min_eq_left]
  have re:=Nat.mod_lt (width+p-1) hp
  have div:=Nat.mod_add_div (width+p-1) p
  unfold poolBatchCount
  rw [Nat.mul_comm p _] at div
  omega

omit [Fintype P] in
theorem dense_piece {rows word : ℕ} (room : (∑e,N.width e)≤rows*word) (hp : 0<p)
    (i j : Fin S) (e : N.Edge) (same : pairIndex N home e=pair i j)
    (k : Fin (poolBatchCount (N.width e) p)) (bit : Fin (pieceWidth (N.width e) p k.val)) :
    let start:=k.val*p
    let b : Fin (N.width e):=⟨start+bit.val,by
      have early:=piece_used hp k
      have last:=bit.isLt.trans_le (Nat.min_le_right p (N.width e-k.val*p))
      change k.val*p+bit.val<N.width e
      omega⟩
    (finProdFinEquiv (denseBits N (edgeCode N home native) room ⟨e,b⟩)).val=
      pairBase N home i j+earlierCables N home native i j e+
        (∑ t ∈ Finset.range k.val,pieceWidth (N.width e) p t)+bit.val := by
  dsimp only
  rw [denseBits_address,edge_start N home native e i j same,piece_before,
    Nat.min_eq_right (piece_used hp k).le]
  exact (Nat.add_assoc (pairBase N home i j + earlierCables N home native i j e)
    (k.val*p) bit.val).symm

end CableAddresses

section SliceOrder
variable {D S : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S)
    (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (p : ℕ)

/-- A common stride bounds every true piece number, including on exterior pins. -/
def stride := 1+(∑ e : N.Edge,poolBatchCount (N.width e) p)+(∑ z : P,poolBatchCount (bits z) p)

private theorem edge_piece_room (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) :
    k.val<stride N p := by
  have h:=Finset.single_le_sum (s:=Finset.univ) (f:=fun e=>poolBatchCount (N.width e) p)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)
  unfold stride; have:=k.isLt;omega

theorem pin_piece_room (z : P) (k : Fin (poolBatchCount (bits z) p)) :
    k.val<stride N p := by
  have h:=Finset.single_le_sum (s:=Finset.univ) (f:=fun z=>poolBatchCount (bits z) p)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ z)
  unfold stride; have:=k.isLt;omega

def wireRank (external : P ↪ ℕ) : Names N p ↪ ℕ where
  toFun
    | .inl ⟨e,k⟩=>2*(edgeCode N home native e*stride N p+k.val)
    | .inr ⟨z,k⟩=>2*(external z*stride N p+k.val)+1
  inj' := by
    rintro (⟨e,k⟩|⟨z,k⟩) (⟨f,l⟩|⟨a,l⟩) h
    · have h' : edgeCode N home native e*stride N p+k.val=edgeCode N home native f*stride N p+l.val := by dsimp at h;omega
      obtain ⟨code,bit⟩:=digit_inj (edge_piece_room N p e k) (edge_piece_room N p f l) h'
      have eq := (edgeCode N home native).injective code
      subst f
      obtain rfl:=Fin.ext bit
      rfl
    · dsimp at h;omega
    · dsimp at h;omega
    · have h' : external z*stride N p+k.val=external a*stride N p+l.val := by dsimp at h;omega
      obtain ⟨code,bit⟩:=digit_inj (pin_piece_room N p z k) (pin_piece_room N p a l) h'
      have eq:=external.injective code
      subst a
      obtain rfl:=Fin.ext bit
      rfl

variable (external : P ↪ ℕ)
theorem slice_lt (e f : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) (l : Fin (poolBatchCount (N.width f) p)) :
    wireRank N home native p external (.inl ⟨e,k⟩)<wireRank N home native p external (.inl ⟨f,l⟩) ↔
      edgeCode N home native e<edgeCode N home native f ∨ (e=f ∧ k.val<l.val) := by
  change 2*_ < 2*_ ↔ _
  rw [Nat.mul_lt_mul_left (by decide : 0<2),digit_lt (edge_piece_room N p e k) (edge_piece_room N p f l),
    (edgeCode N home native).injective.eq_iff]

def order (nodes : N.Site ↪ ℕ) (operands : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ) : Order N S p :=
  ⟨home,nodes,wireRank N home native p external,operands⟩

omit [Fintype P] in
theorem between_iff (L : Order N S p) (i j : Fin S) (e : N.Edge) (k : Fin (poolBatchCount (N.width e) p)) :
    Order.between L i j (.inl ⟨e,k⟩) ↔ pairIndex N L.home e=pair i j := by
  rw [Order.between_edge,pairIndex,pair_iff]
  tauto

end SliceOrder
end
end Hierarchy.DescentTerminalCableOrder

end OAI
