import OAI.Hierarchy.DescentGoodBaseMatrix
import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Actual scheduled rotor roles from the traffic matrix and layer count -/
namespace Hierarchy.DescentPackedResetRotorRoles
open DescentResetGates DescentRotor DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
noncomputable section
local notation "Y" n:arg => (2^n:ℕ)

def roleBits (n : ℕ) := n*Y n+n+3
def rotorNumber {n : ℕ} (image : Fin (Y n)→Fin (Y n)) (v : Fin (Y n)) :=
  6+(finProdFinEquiv (encode n (Y n) image,v)).val

theorem number_lt {n : ℕ} (image : Fin (Y n)→Fin (Y n)) (v : Fin (Y n)) : rotorNumber image v<2^(roleBits n) := by
  let key := finProdFinEquiv (encode n (Y n) image, v)
  have bound : key.val < 2^(n*Y n+n) := calc
    key.val < 2^(n*Y n)*(2^n) := key.isLt
    _ = _ := (pow_add (2 : ℕ) (n*Y n) n).symm
  have room : 2^(roleBits n) = 2^(n*Y n+n)*8 :=
    pow_add (2 : ℕ) (n*Y n+n) 3
  have pos := Nat.two_pow_pos (n*Y n+n)
  change 6 + key.val < 2^(roleBits n)
  rw [room]
  omega

def short : Bool⊕(Bool⊕Unit)→ℕ
  | .inl false=>1
  | .inl true=>2
  | .inr (.inl false)=>3
  | .inr (.inl true)=>4
  | .inr (.inr ())=>5

theorem short_lt (b : Bool⊕(Bool⊕Unit)) : short b<6 := by
  rcases b with b | b | b <;> cases b <;> decide

theorem short_injective : Function.Injective short := by
  intro a b eqn
  rcases a with a | a | a <;> cases a <;> rcases b with b | b | b <;> cases b <;>
    first | rfl | norm_num [short] at eqn

def role {n : ℕ} : CanonicalTag (Y n)→ℕ
  | .inl (π,v)=>rotorNumber π v
  | .inr s=>short s

theorem role_injective (n : ℕ) : Function.Injective (role (n:=n)) := by
  rintro (⟨π,v⟩|s) (⟨ρ,t⟩|s') eqn
  · change 6+_=6+_ at eqn
    have pair:=finProdFinEquiv.injective (Fin.ext (Nat.add_left_cancel eqn))
    have fst:π=ρ:=Equiv.ext (fun i=>congrFun ((encode n (Y n)).injective (congrArg Prod.fst pair)) i)
    have snd : v = t := congrArg (fun q : Cell (n*Y n) × Fin (Y n) => q.2) pair
    exact congrArg Sum.inl (Prod.ext fst snd)
  · have:=short_lt s'
    change 6+_=short s' at eqn
    omega
  · have:=short_lt s
    change short s=6+_ at eqn
    omega
  · exact congrArg Sum.inr (short_injective eqn)

def matrix (n b : ℕ) (a : Cell (b*(Y n*Y n))) (i j : Fin (Y n)) := ((encode b (Y n*Y n)).symm a (finProdFinEquiv (i,j))).val

def book (n b layerBits packet m cap : ℕ) (v : Fin (Y n)) (a : Cell (b*(Y n*Y n))) (levels : Cell layerBits) :
    Cell (roleBits n*cap) :=
  encode (roleBits n) cap fun z=>
    let L:=levels.val/2
    if yes : z.val<levels.val*m ∧ z.val/m<2*L+1 then
      let turn:=Scheduler.rotate (Scheduler.matrixRun packet L (matrix n b a)) ⟨z.val/m,yes.2⟩
      ⟨rotorNumber turn v,number_lt turn v⟩
    else 0

open private DescentPacking.PackedMatch.Local.Gather.encode_zero from OAI.Hierarchy.DescentPackedFieldGather

@[simp] theorem book_zero (n b layers packet m cap : ℕ) (v : Fin (Y n)) :
    book n b layers packet m cap v 0 0=0 := by
  simp [book,DescentPacking.PackedMatch.Local.Gather.encode_zero]

variable {F E : Type} [Field F] [Fintype E] {n h C w u : ℕ} {hw : 0<w} {G : NonlinearExpanders.Graph n h}
variable {src dst : E→Fin (Y n)} {S : ℝ} (P : BaseCircuit F G C w u hw src dst S)

theorem actual {b layers m cap : ℕ} (v : Fin (Y n)) (a : Cell (b*(Y n*Y n))) (level : Cell layers)
    (counts : ∀i j,matrix n b a i j=DescentBaseProfile.matrixOfBundles src dst i j) (height : level.val=P.layers)
    (r : Fin P.layers) (batch : Fin m) (room : r.val*m+batch.val<cap) :
    digit (roleBits n) (r.val*m+batch.val) (book n b layers w m cap v a level).val=
      role (.inl (P.rotation r,v)) := by
  obtain ⟨L,scheduled,_,image⟩:=P.scheduled
  have period : level.val/2=L := by omega
  have positive : 0< m:=by have:=batch.isLt;omega
  have address : (r.val*m+batch.val)/m=r.val := by
    rw [Nat.add_comm (r.val*m) batch.val,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt batch.isLt,Nat.zero_add]
  have active : r.val*m+batch.val<level.val*m := by
    rw [height]
    have finish:=Nat.mul_le_mul_right m r.isLt
    rw [Nat.succ_mul] at finish
    have:=batch.isLt;omega
  have actualLayer : (r.val*m+batch.val)/m<2*(level.val/2)+1 := by rw [address,period,←scheduled];exact r.isLt
  have mat : matrix n b a=DescentBaseProfile.matrixOfBundles src dst :=
    funext (fun i=>funext (counts i))
  have turn (length : ℕ) (same : length=L) (index : Fin (2*length+1)) (ordinal : index.val=r.val) :
      Scheduler.rotate (Scheduler.matrixRun w length (matrix n b a)) index = ⇑(P.rotation r) := by
    subst length
    have indexEq : index=Fin.cast scheduled r := Fin.ext ordinal
    rw [indexEq,mat]
    funext j
    exact (image r j).symm
  let z : Fin cap:=⟨r.val*m+batch.val,room⟩
  have live : z.val<level.val*m ∧ z.val/m<2*(level.val/2)+1 := ⟨active,actualLayer⟩
  change digit (roleBits n) z.val _=_
  unfold book
  rw [digit_encode _ z]
  dsimp only
  rw [dite_eq_left live]
  exact congrArg (fun f : Fin (Y n)→Fin (Y n)=>rotorNumber f v)
    (turn _ period ⟨z.val/m,live.2⟩ address)

open scoped Fin.CommRing

/-- Two truly measured source words per good base. Padding and occupied zero-layer rows publish zero.
The finite ROM computes the scheduled permutation on the matrix rather than taking rotation IDs as input. -/
theorem issued {hosts groups M W n b layers packet m cap : ℕ} (v : Fin (Y n)) (T : Tables) (traffic height : Expr) (out : ℕ)
    (a : Fin hosts→Fin groups→Cell (b*(Y n*Y n))) (level : Fin hosts→Fin groups→Cell layers) (mem : Memory W)
    (fit : Fits T traffic height (b*(Y n*Y n)) layers M out W) (room : out+hosts*chunks groups M<2^W)
    (stat : Static T (book n b layers packet m cap v) M mem)
    (src : Source traffic a M mem) (hdr : Source height level M mem) :
    let dst:=ProtocolRAM.image out (hosts*chunks groups M) (T.read traffic height) mem
    (code T traffic height out hosts groups M W).Exec mem dst (4+hosts*chunks groups M*(2*(traffic.work+height.work+11)+4)) ∧
    ∀q : Row hosts groups M,dst (out+(row hosts groups M q).val)=
      ((data (fun h g=>book n b layers packet m cap v (a h g) (level h g)) q).val : Word W) := by
  have reads:=read_data T traffic height out fit _ (book_zero ..) mem stat a level src hdr
  have safe : (T.read traffic height).Fits W out := by
    simp [Tables.read,Expr.Fits,fit.left,fit.right,fit.shift,fit.apply]
  constructor
  · rw [←DescentPackedZip.work T traffic height]
    exact @scan_exec W out (hosts*chunks groups M) (T.read traffic height) mem safe room
  intro q
  exact (ProtocolRAMGeneratedWrite.read_image out (hosts*chunks groups M) (T.read traffic height)
    mem (row hosts groups M q)).trans (reads q)

/-- When all packed rotor roles fit in a machine word, the published row also recovers
its full natural value. -/
theorem issued_value {hosts groups M W n b layers packet m cap : ℕ} (v : Fin (Y n)) (T : Tables)
    (traffic height : Expr) (out : ℕ)
    (a : Fin hosts→Fin groups→Cell (b*(Y n*Y n))) (level : Fin hosts→Fin groups→Cell layers)
    (mem : Memory W) (fit : Fits T traffic height (b*(Y n*Y n)) layers M out W)
    (room : out+hosts*chunks groups M<2^W) (stat : Static T (book n b layers packet m cap v) M mem)
    (src : Source traffic a M mem) (hdr : Source height level M mem)
    (packed : roleBits n*cap*M≤W) (q : Row hosts groups M) :
    let dst:=ProtocolRAM.image out (hosts*chunks groups M) (T.read traffic height) mem
    (dst (out+(row hosts groups M q).val)).val =
      (data (fun h g=>book n b layers packet m cap v (a h g) (level h g)) q).val := by
  let cell := data (fun h g=>book n b layers packet m cap v (a h g) (level h g)) q
  have fitsWord : cell.val < 2^W :=
    cell.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) packed)
  exact (congrArg Fin.val ((issued v T traffic height out a level mem fit room stat src hdr).2 q)).trans
    (Fin.val_cast_of_lt fitsWord)

end
end Hierarchy.DescentPackedResetRotorRoles

end OAI
