import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.TaggedShorterEmitMachine
import OAI.ThreeFlat.RAM.EffectLocation

namespace OAI
/-! # Fixed-size overwrite scatter from genuine reached sparse header rows -/
namespace Hierarchy.DescentTerminalHeaderScatter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w n : ℕ}

/-- One actual record per bank write. The instruction stream alternates
address/value regardless of the branch. Both past endpoint views may point to
the same destination on a self-loop. -/
def stage (low high : Expr) (lane : Bank) : Expr :=
  .branch .eq (.lookup lane .row) (.lit 0) low high

def program (w src n : ℕ) (low high : Expr) (lane : Bank) :=
  (scan w src (2*n) (stage low high lane)).seq (EffectSeed.scatter w src n)

def cost (n : ℕ) (low high : Expr) (lane : Bank) :=
  (4+(2*(stage low high lane).work+4)*(2*n))+(4+6*n)

def turn (n : ℕ) := List.ofFn (fun i : Fin (2*n)=>i.val%2)
def ordinal (n : ℕ) := List.ofFn (fun i : Fin (2*n)=>i.val/2)

def field (i : Fin n) (j : Fin 2) : Fin (2*n) := ⟨2*i.val+j.val,by have:=i.isLt;have:=j.isLt;omega⟩

theorem lane_read (low high : Expr) (b : Bank) (m : Memory w) (i : Fin n) (j : Fin 2)
    (positive : 0<w) (read : b.read m ((field i j).val:Word w)=(j.val:Word w)) :
    (stage low high b).eval m ((field i j).val:Word w)=
      (if j=0 then low else high).eval m ((field i j).val:Word w) := by
  have bit : (1:Word w)≠0 := by
    intro e
    have zero := congrArg Fin.val e
    simp at zero
    omega
  simp only [stage,Expr.eval,Comparison.test,read]
  fin_cases j <;> simp [bit]

theorem emit (low high : Expr) (lane : Bank) (m : Memory w) (src : ℕ)
    (data : Fin n→EffectStream.Record w) (fit : (stage low high lane).Fits w src)
    (room : src+2*n<2^w)
    (safe : ∀i,(data i).1.val<src ∨ src+2*n≤(data i).1.val)
    (records : ∀i j,(stage low high lane).eval m ((field i j).val:Word w)=if j=0 then (data i).1 else (data i).2) :
    let es:=List.ofFn data
    let before:=image src (2*n) (stage low high lane) m
    (program w src n low high lane).Exec m (after before (EffectStream.events es)) (cost n low high lane) ∧
      CheapCode (program w src n low high lane) := by
  intro es before
  have writer : (scan w src (2*n) (stage low high lane)).Exec m before
      (4+(2*n)*(2*(stage low high lane).work+4)) := scan_exec src (2*n) (stage low high lane) m fit room
  have loaded : EffectStream.Loaded before src es := by
    apply (EffectStream.loaded_iff ..).2
    intro i
    let k : Fin n:=i.cast (List.length_ofFn)
    have «rec» : es.get i=data k := List.get_ofFn data i
    rw [«rec»]
    constructor
    · simpa [before,field,k] using (DescentTerminalChipRuntime.image_at m src _ (stage low high lane) (field k 0)).trans (records k 0)
    · simpa [before,field,k,Nat.add_assoc] using (DescentTerminalChipRuntime.image_at m src _ (stage low high lane) (field k 1)).trans (records k 1)
  have away : EffectStream.Safe src es := by
    rintro e he
    obtain ⟨k,rfl⟩:=List.mem_ofFn.mp he
    simpa [es] using safe k
  have run : (EffectSeed.scatter w src es.length).Exec before (after before (EffectStream.events es))
      (4+6*es.length) := Procedure.Spec.exec (EffectSeed.scatter_spec src es (by simpa [es] using room) away) before loaded
  have composed : ((scan w src (2*n) (stage low high lane)).seq (EffectSeed.scatter w src es.length)).Exec
      m (after before (EffectStream.events es))
      ((4+(2*n)*(2*(stage low high lane).work+4))+(4+6*es.length)) := Procedure.Exec.then writer run
  refine ⟨?_,@TaggedShorterEmitMachine.scanReplay_cheap w src (2*n) n (stage low high lane)⟩
  have len : es.length = n := List.length_ofFn
  rw [len] at composed
  unfold program cost
  rw [Nat.mul_comm (2*(stage low high lane).work+4) (2*n)]
  exact @composed

/-- Make the fixed write bank part of the instruction itself. Every
descriptor, including a rejected selector, can only write this bank. -/
def bounded (b : Bank) (address : Expr) : Expr :=
  .op .add (.lit b.base) (.op .mask (.op .sub address (.lit b.base)) (.lit (b.size-1)))

theorem bounded_val (b : Bank) (address : Expr) (m : Memory w) (i : Word w) {src : ℕ}
    (fit : b.Fits w src) (room : src<2^w) :
    ((bounded b address).eval m i).val=b.base+(address.eval m i-(b.base:Word w)).val%b.size := by
  obtain ⟨pos,small,last⟩:=fit
  let delta:Word w:=address.eval m i-(b.base:Word w)
  have bound : b.base+delta.val%b.size<2^w:=by have:=Nat.mod_lt delta.val pos;omega
  have mask : b.size-1<2^w:=by omega
  change (BinaryOp.add.eval (b.base:Word w) (BinaryOp.bitAnd.eval delta ((b.size-1:ℕ):Word w))).val=_
  simp only [BinaryOp.eval,Fin.val_cast_of_lt mask]
  rw [show delta.val &&& (b.size-1)=delta.val%b.size from Nat.and_two_pow_sub_one_eq_mod _ _]
  change ((b.base:Word w)+((delta.val%b.size:ℕ):Word w)).val=_
  rw [←Nat.cast_add,Fin.val_cast_of_lt bound]

theorem bounded_exact (b : Bank) (e : Expr) (m : Memory w) (i : Word w) {src off : ℕ}
    (fit : b.Fits w src) (room : src<2^w) (small : off<b.size)
    (value : e.eval m i=((b.base+off:ℕ):Word w)) :
    (bounded b e).eval m i=e.eval m i := by
  apply Fin.ext
  have ok : b.base+off<2^w:=by have:=fit.2.2;omega
  rw [bounded_val b e m i fit room,value,Fin.val_cast_of_lt ok,Nat.cast_add,add_sub_cancel_left,
    Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

def actual (low high : Expr) (m : Memory w) (i : Fin n) : EffectStream.Record w :=
  (low.eval m ((field i 0).val:Word w),high.eval m ((field i 1).val:Word w))
def imageAt (src n : ℕ) (low high : Expr) (lane : Bank) (m : Memory w) :=
  after (image src (2*n) (stage low high lane) m)
    (EffectStream.events (List.ofFn (actual (n:=n) low high m)))

theorem exec_any (b lane : Bank) (lo hi : Expr) (m : Memory w) (src : ℕ) (pos : 0<w)
    (fit : b.Fits w src) (ready : (stage (bounded b lo) hi lane).Fits w src)
    (room : src+2*n<2^w)
    (static : ∀(i : Fin n) (j:Fin 2),lane.read m ((field i j).val:Word w)=(j.val:Word w)) :
    (program w src n (bounded b lo) hi lane).Exec m (imageAt src n (bounded b lo) hi lane m)
      (cost n (bounded b lo) hi lane) ∧ CheapCode (program w src n (bounded b lo) hi lane) := by
  let addr:=bounded b lo
  apply emit addr hi lane m src (actual addr hi m) ready room
  · intro i
    apply Or.inl
    rw [show (actual addr hi m i).1=(bounded b lo).eval m ((field i 0).val:Word w) from rfl,bounded_val b lo _ _ fit (by omega)]
    have:=Nat.mod_lt (lo.eval m ((field i 0).val:Word w)-(b.base:Word w)).val fit.1
    have:=fit.2.2
    omega
  · intro i j
    rw [lane_read _ _ _ _ _ _ pos (static i j)]
    fin_cases j <;> rfl

/-- Support proof permits duplicate writes only when both assign the same
actual header. All untouched destinations retain their prescribed blank word. -/
theorem published (m : Memory w) (data : Fin n→EffectStream.Record w) (whereAt : ℕ) (v : Word w)
    (agree : ∀i,(data i).1.val=whereAt → (data i).2=v)
    (present : m whereAt=v ∨ ∃i,(data i).1.val=whereAt) :
    after m (EffectStream.events (List.ofFn data)) whereAt=v := by
  apply EffectStream.after_at
  · intro e mem
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp mem
    exact agree i
  · rcases present with init|⟨i,hi⟩
    · exact Or.inl init
    · exact Or.inr ⟨data i,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩

end
end Hierarchy.DescentTerminalHeaderScatter

end OAI
