import OAI.Hierarchy.DescentPackedWalshReduction

namespace OAI
/-! # Public pointer columns, shift entries and addition ROM for one packed host reduction -/
namespace Hierarchy.DescentPackedWalshReduction
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Tile where
  hosts : ℕ
  chunks : ℕ
  subdivisions : ℕ
  lanes : ℕ
  digits : ℕ

namespace Tile
variable (S : Tile)
abbrev H := 2^S.hosts
abbrev K := 2^S.chunks
abbrev Z := 2^S.subdivisions
abbrev L := 2^S.lanes
def rows := S.H*S.K*S.Z
def inputRows := S.H*2*S.K
def payload := S.digits*(S.Z*S.L)
def keyBits := S.subdivisions+(S.digits+S.digits)*(S.Z*S.L)
def span := 3*S.rows+2^S.payload+2^S.keyBits

def banks (rom source : ℕ) : DescentPackedWalsh.Banks :=
  let ptr:=S.hosts+S.chunks+S.subdivisions
  ⟨⟨source,S.hosts+1+S.chunks⟩,⟨rom,ptr⟩,⟨rom+S.rows,ptr⟩,
    ⟨rom+2*S.rows,ptr⟩,⟨rom+3*S.rows,S.payload⟩,⟨rom+3*S.rows+2^S.payload,S.keyBits⟩⟩

theorem room {w rom src dst : ℕ} (stat : rom+S.span≤dst)
    (previous : src+S.inputRows≤dst) (finish : dst+S.rows<2^w) :
    Room (S.banks rom src) dst S.H S.K S.Z S.L S.digits S.subdivisions w := by
  have p : 0<S.rows:=by unfold rows;positivity
  have ip : 0<S.inputRows:=by unfold inputRows;positivity
  have cp:=Nat.two_pow_pos S.payload
  have rp:=Nat.two_pow_pos S.keyBits
  have ein : 2^(S.hosts+1+S.chunks)=S.inputRows:=by simp [inputRows,pow_add,H,K]
  have eout : 2^(S.hosts+S.chunks+S.subdivisions)=S.rows:=by simp [rows,pow_add,H,K,Z]
  change rom+(3*S.rows+2^S.payload+2^S.keyBits)≤dst at stat
  constructor <;> try simp only [banks,Bank.Fits,Bank.size,ein,eout]
  · exact ⟨ip,by omega,previous⟩
  · exact ⟨p,by omega,by omega⟩
  · exact ⟨p,by omega,by omega⟩
  · exact ⟨p,by omega,by omega⟩
  · exact ⟨cp,by omega,by omega⟩
  · exact ⟨rp,by omega,by omega⟩
  all_goals first | exact le_rfl | exact finish

private def segment {α : Type*} {n : ℕ} (f : Fin n→α) (tail : ℕ→α) (j : ℕ) :=
  if atRow : j<n then f ⟨j,atRow⟩ else tail (j-n)

private theorem first {α : Type*} {n : ℕ} (f : Fin n→α) (tail : ℕ→α) (j : Fin n) :
    segment f tail j.val=f j := dite_eq_left j.isLt

private theorem later {α : Type*} {n : ℕ} (f : Fin n→α) (tail : ℕ→α) (j : ℕ) :
    segment f tail (n+j)=tail j := by simp [segment]

private def positions (j : Fin S.rows) : (Fin S.H×Fin S.K)×Fin S.Z :=
  let q:=finProdFinEquiv.symm j
  (finProdFinEquiv.symm q.1,q.2)

private theorem positions_read (v : Fin S.H) (i : Fin S.K) (z : Fin S.Z) :
    S.positions (rightRow v i z)=((v,i),z) := by simp [positions,rightRow]

/-- Each predecessor row number is computed from the row and subdivision index;
only the column indexed by the pair of packed predecessor words performs arithmetic. -/
def word {w : ℕ} : ℕ→Word w :=
  segment (fun j : Fin S.rows=>let p:=S.positions j; ((leftRow p.1.1 false p.1.2).val:Word w)) <|
  segment (fun j : Fin S.rows=>let p:=S.positions j; ((leftRow p.1.1 true p.1.2).val:Word w)) <|
  segment (fun j : Fin S.rows=> ((2^((S.digits+S.digits)*(S.Z*S.L))*(S.positions j).2.val:ℕ):Word w)) <|
  segment (fun j : Cell S.payload=> ((2^S.payload*j.val:ℕ):Word w)) <|
  segment (fun j : Cell S.keyBits=> ((lut (b:=S.digits) (c:=S.digits+1) (Z:=S.Z)
    (L:=S.L) (idx:=S.subdivisions) j).val:Word w)) (fun _=>0)

/-- The previous data page is outside the finite read-only header. -/
def mount {w : ℕ} (rom : ℕ) (m : Memory w) (a : ℕ) : Word w :=
  if rom≤a ∧ a<rom+S.span then S.word (a-rom) else m a

theorem before {w : ℕ} (rom : ℕ) (m : Memory w) {a : ℕ} (h : a<rom) : S.mount rom m a=m a := by
  simp [mount,show ¬(rom≤a ∧ a<rom+S.span) by omega]
theorem beyond {w : ℕ} (rom : ℕ) (m : Memory w) {a : ℕ} (h : rom+S.span≤a) : S.mount rom m a=m a := by
  simp [mount,show ¬(rom≤a ∧ a<rom+S.span) by omega]

theorem mounted_at {w : ℕ} (rom : ℕ) (m : Memory w) (j : ℕ) (inside : j<S.span) :
    S.mount rom m (rom+j)=S.word j := by simp [mount,inside]

theorem headerAt {w rom src : ℕ} {m : Memory w}
    (read : ∀j<S.span,m (rom+j)=S.word j) :
    Header (S.banks rom src) S.H S.K S.Z S.L S.digits (S.digits+1) S.subdivisions m := by
  have a := Nat.two_pow_pos S.payload
  have b := Nat.two_pow_pos S.keyBits
  constructor
  · intro v i z
    let n:=rightRow v i z
    have nlt : n.val<S.rows:=n.isLt
    apply (read _ (by unfold span;omega : n.val<S.span)).trans
    unfold word
    rw [segment,dite_eq_left nlt]
    change ((leftRow (S.positions n).1.1 false (S.positions n).1.2).val:Word w)=_
    rw [S.positions_read]
  · intro v i z
    let n:=rightRow v i z
    have nlt : n.val<S.rows:=n.isLt
    change m (rom+S.rows+n.val)=_
    rw [Nat.add_assoc,read _ (by unfold span;omega)]
    simp only [word,later]
    rw [segment,dite_eq_left nlt]
    change ((leftRow (S.positions n).1.1 true (S.positions n).1.2).val:Word w)=_
    rw [S.positions_read]
  · intro v i z
    let n:=rightRow v i z
    have nlt : n.val<S.rows:=n.isLt
    change m (rom+2*S.rows+n.val)=_
    rw [show rom+2*S.rows+n.val=rom+(S.rows+(S.rows+n.val)) by omega,read _ (by unfold span;omega)]
    simp only [word,later]
    rw [segment,dite_eq_left nlt]
    change ((2^((S.digits+S.digits)*(S.Z*S.L))*(S.positions n).2.val:ℕ):Word w)=_
    rw [S.positions_read]
  · intro j
    have hj : j.val<2^S.payload:=j.isLt
    change m (rom+3*S.rows+j.val)=_
    rw [show rom+3*S.rows+j.val=rom+(S.rows+(S.rows+(S.rows+j.val))) by omega,read _ (by unfold span;omega)]
    simp [word,later,first,payload]
  · intro j
    have hj : j.val<2^S.keyBits:=j.isLt
    change m (rom+3*S.rows+2^S.payload+j.val)=_
    rw [show rom+3*S.rows+2^S.payload+j.val=rom+(S.rows+(S.rows+(S.rows+(2^S.payload+j.val)))) by omega,
      read _ (by unfold span;omega)]
    simp only [word,later]
    rw [segment,dite_eq_left hj]
    rfl

theorem header {w : ℕ} (rom src : ℕ) (m : Memory w) :
    Header (S.banks rom src) S.H S.K S.Z S.L S.digits (S.digits+1) S.subdivisions (S.mount rom m) :=
  S.headerAt (S.mounted_at rom m)
end Tile
end
end Hierarchy.DescentPackedWalshReduction

end OAI
