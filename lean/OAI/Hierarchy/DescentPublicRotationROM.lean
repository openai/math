import OAI.Hierarchy.DescentExteriorReelPrograms

namespace OAI
/-! # The native exterior matrix tables for the entire public calendar -/
namespace Hierarchy.DescentExteriorMatrixUpdate
open DescentCompiler DescentSixParty.Chronology DescentColonies DescentPackedColony.Phase.Arena
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
namespace Calendar
variable (S : AtomSchedule) (k tail base : ℕ) (reset : ℕ→Bool)
local notation "dim" => S.groupWidth k tail 0+k

def stride := pages (S.groupWidth k tail 0+k) (S.groupWidth k tail 0+k)
def tableAt (i : ℕ) := base+i*stride S k tail
def stop := tableAt S k tail base S.length
def localBits (i : ℕ) := if reset i then S.groupWidth k tail i+k else k

private theorem width_le (i : ℕ) : S.groupWidth k tail i+k≤dim :=by
  unfold AtomSchedule.groupWidth
  simp only [Nat.sub_zero]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left k (Nat.sub_le ..)) tail) k

theorem page_room (i : ℕ) : pages dim (localBits S k tail reset i)≤ stride S k tail :=by
  have h : localBits S k tail reset i≤dim :=by
    unfold localBits
    split
    · exact width_le S k tail i
    · exact Nat.le_add_left ..
  unfold pages stride
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul h h))) _

def entry {w : ℕ} (i : ℕ) (alive : i<S.length) : Image w :=
  if reset i then tableSheet (tableAt S k tail base i) (resetMap S k tail i alive)
  else tableSheet (tableAt S k tail base i) (ordinaryMap S k tail i alive)

def sheet (w : ℕ) : Image w :=
  ⟨base,stop S k tail base,fun addr=>
    let i:=(addr-base)/stride S k tail
    if alive : i<S.length then (entry S k tail base reset (w:=w) i alive).value addr else 0⟩

theorem resident {w : ℕ} (m : Memory w) (whole : (sheet S k tail base reset w).Resident m)
    (i : ℕ) (alive : i<S.length) : (entry S k tail base reset i alive).Resident m :=by
  intro a lo hi
  let block:=stride S k tail
  have positive : 0<block :=by
    change 0<2^_+_
    exact Nat.add_pos_left (Nat.two_pow_pos _) _
  have start : base+i*block≤a :=by cases f:reset i <;> simpa [entry,f,tableSheet,tableAt,block] using lo
  have finish : a<base+i*block+pages dim (localBits S k tail reset i) :=by
    cases f:reset i <;> simpa [entry,f,localBits,tableSheet,tableAt,block] using hi
  have inside : a-(base+i*block)<block:=by
    have bound:=page_room S k tail reset i
    change pages dim (localBits S k tail reset i)≤block at bound
    omega
  have digit : a-base=i*block+(a-(base+i*block)):=by omega
  have quotient : (a-base)/block=i :=by
    have order : a-base=block*i+(a-(base+i*block)) :=
      digit.trans (congrArg (fun n=>n+(a-(base+i*block))) (Nat.mul_comm i block))
    rw [order,Nat.mul_add_div positive,Nat.div_eq_of_lt inside,Nat.add_zero]
  have upto : (i+1)*block≤S.length*block:=Nat.mul_le_mul_right _ alive
  have within : a<stop S k tail base :=by
    change a<base+S.length*block
    rw [Nat.succ_mul] at upto
    omega
  have val:=whole a (show base≤a by omega) within
  simpa only [sheet,show (a-base)/stride S k tail=i from quotient,dite_eq_left alive] using val

theorem issue {w : ℕ} (m : Memory w) (fits : stop S k tail base<2^w) :
    let I:=sheet S k tail base reset w
    I.program.Exec m (I.output m) (4+10*(S.length*stride S k tail)) ∧
      CheapCode I.program ∧ DescentStaticWordColumn.names I.program=15*(S.length*stride S k tail+1) ∧
      (∀i (alive : i<S.length),(entry S k tail base reset i alive).Resident (I.output m)) ∧
      ∀a,a<base ∨ stop S k tail base≤a → I.output m a=m a :=by
  intro I
  have size : I.length=S.length*stride S k tail:=by
    change (base+S.length*stride S k tail)-base=_
    omega
  obtain ⟨run,all,frame⟩:=I.issue m (by rw [size];exact fits)
  rw [size] at run
  exact ⟨run,I.hardware.1,I.hardware.2.trans (by rw [size]),fun i hi=>resident S k tail base reset _ all i hi,frame⟩

/-- A single accumulated matrix register per date follows the contiguous ROM.
The proposal determines only the values stored at the already chosen rotation addresses. -/
def reel (rotation : ℕ→ℕ) : Reel :=
  let fence:=stop S k tail base
  ⟨fun i=>fence+i,rotation,tableAt S k tail base,fun i=>fence+(i+1),localBits S k tail reset⟩

theorem room {w : ℕ} (rotation : ℕ→ℕ) (older : ∀i<S.length,rotation i<base)
    (space : stop S k tail base+S.length+2<2^w) :
    (reel S k tail base reset rotation).Room w dim S.length (stop S k tail base)
      (stop S k tail base+S.length+1) :=by
  have zero : base≤ stop S k tail base:=Nat.le_add_right ..
  refine ⟨by simp [reel],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> dsimp only [reel] at *
  · omega
  · omega
  · intro i hi;omega
  · intro i hi;have:=older i hi;omega
  · intro i hi
    have width:=page_room S k tail reset i
    have length:=Nat.mul_le_mul_right (stride S k tail) hi
    rw [Nat.succ_mul] at length
    change base+i*stride S k tail+pages dim (localBits S k tail reset i)≤(base+S.length*stride S k tail)+(i+1)
    omega
  · intro i hi;omega
  · intro i hi;omega
  · intro i hi;omega
  · intro i hi;rfl
  · omega

theorem room_at {w : ℕ} (rotation : ℕ→ℕ) (origin : ℕ)
    (older : ∀i<S.length,rotation i<base)
    (before : stop S k tail base+S.length<origin) (fits : origin+1<2^w) :
    (reel S k tail base reset rotation).Room w dim S.length (stop S k tail base) origin :=by
  have first:=room S k tail base reset rotation older (by omega : stop S k tail base+S.length+2<2^w)
  have grow : stop S k tail base+S.length+1≤origin:=by omega
  exact ⟨first.boot,first.startLow.trans_le grow,first.startFit,first.previous,first.rotation,first.table,
    first.fit,first.retained,fun i hi=>(first.high i hi).trans_le grow,first.join,first.address.trans_le grow⟩

end Calendar
end
end Hierarchy.DescentExteriorMatrixUpdate

end OAI
