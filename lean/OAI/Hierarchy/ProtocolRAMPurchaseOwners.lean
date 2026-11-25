import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProbeStageResident
import OAI.Hierarchy.ProtocolRAMPurchaseSuccessor

namespace OAI
/-! # Building the input-socket owner table for a native tile stage

A dense pass clears every active socket, then one sparse store per tile
writes its ordinal plus one. The group-stride and sampler columns depend only on
the stage dimensions and the sampler, respectively.
-/

namespace Hierarchy.ProtocolRAMPurchaseOwners

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProbeStage
open scoped Fin.CommRing

variable {n m groups w : ℕ} {G : Type*}

theorem portCode_word_eq_zero_iff {k : ℕ} (a : Option (Fin k)) (small : k < 2^w) :
    (portCode a : Word w)=0 ↔ a=none := by
  cases a with
  | none => simp [portCode]
  | some r =>
    have fit : r.val+1 < 2^w := Nat.lt_of_le_of_lt r.isLt small
    constructor
    · intro h
      have vals := congrArg Fin.val h
      change ((r.val+1:ℕ):Word w).val=(0:Word w).val at vals
      rw [Fin.val_cast_of_lt fit,Fin.val_zero] at vals
      omega
    · intro h
      cases h

theorem portCode_word_injective {k : ℕ} (small : k < 2^w) :
    Function.Injective (fun a : Option (Fin k) => (portCode a : Word w)) := by
  have room (a : Option (Fin k)) : portCode a < 2^w := by
    cases a with
    | none => exact Nat.two_pow_pos _
    | some i => exact Nat.lt_of_le_of_lt i.isLt small
  intro a b eq
  have vals := congrArg Fin.val eq
  change ((portCode a : Word w).val = (portCode b : Word w).val) at vals
  rw [Fin.val_cast_of_lt (room a),Fin.val_cast_of_lt (room b)] at vals
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => simp only [portCode] at vals; omega
  | some i =>
    cases b with
    | none => simp only [portCode] at vals; omega
    | some j => exact congrArg some (Fin.ext (Nat.add_right_cancel vals))

structure Columns where
  group : Bank
  input : Bank
  output : Bank
  stride : Bank
  owner : Bank

structure Loaded (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) : Prop where
  group : Native.Resident x.group mem (fun r => (encode (p.group r)).val)
  input : Native.Resident x.input mem (fun r => (p.input r).val)
  output : Native.Resident x.output mem (fun r => (p.output r).val)
  stride : Native.Resident x.stride mem (fun g : Fin groups => g.val*m)

structure Fits (x : Columns) (w n groups m scratch : ℕ) : Prop where
  group : x.group.Fits w x.owner.base
  input : x.input.Fits w x.owner.base
  output : x.output.Fits w x.owner.base
  stride : x.stride.Fits w x.owner.base
  count : groups*m ≤ x.owner.size
  owner : x.owner.Fits w scratch
  room : scratch+2*n < 2^w

def addressExpr (x : Columns) : Expr :=
  .op .add (.lit x.owner.base) (.op .add (.lookup x.stride (.lookup x.group .row))
    (.lookup x.input .row))

def rowCode : Expr := .op .add .row (.lit 1)

def program (w n groups m scratch : ℕ) (x : Columns) : Procedure w :=
  (scan w x.owner.base (groups*m) (.lit 0)).seq
    (ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (addressExpr x) rowCode)

def work (n groups m : ℕ) := 15+6*(groups*m)+70*n

def image (scratch : ℕ) (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) : Memory w :=
  ProtocolRAMGeneratedWrite.image scratch (scratch+n) (addressExpr x) rowCode
    (fun r => x.owner.base+socket (encode (p.group r)) (p.input r))
    (fun r => ((r.val+1 : ℕ) : Word w)) (ProtocolRAM.image x.owner.base (groups*m) (.lit 0) mem)

private theorem source_fits {scratch : ℕ} (x : Columns) (h : Fits x w n groups m scratch) :
    (addressExpr x).Fits w x.owner.base := ⟨trivial,⟨⟨h.stride,h.group,trivial⟩,h.input,trivial⟩⟩

private theorem bank_mono {b : Bank} {a z : ℕ} (h : b.Fits w a) (hz : a ≤ z) :
    b.Fits w z := ⟨h.1,h.2.1,h.2.2.trans hz⟩

theorem resident_frame {k cut : ℕ} {b : Bank} {f : Fin k → ℕ} {mem mem' : Memory w}
    (fit : b.Fits w cut) (same : ∀ a<cut, mem' a=mem a) (h : Native.Resident b mem f) :
    Native.Resident b mem' f := by
  intro i
  exact (same _ ((Nat.add_lt_add_left (Nat.mod_lt _ fit.1) b.base).trans_le fit.2.2)).trans (h i)

theorem run {scratch : ℕ} (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (h : Fits x w n groups m scratch) (load : Loaded x p encode mem) :
    (program w n groups m scratch x).Exec mem (image scratch x p encode mem) (work n groups m) := by
  let cleared := ProtocolRAM.image x.owner.base (groups*m) (.lit 0) mem
  have below : x.owner.base + groups*m ≤ scratch :=
    (Nat.add_le_add_left h.count _).trans h.owner.2.2
  have room := h.room
  have clear : (scan w x.owner.base (groups*m) (.lit 0)).Exec mem cleared
      (4+(groups*m)*(2*(Expr.lit 0).work+4)) :=
    scan_exec x.owner.base (groups*m) (.lit 0) mem trivial (by omega)
  have src : (addressExpr x).Fits w scratch :=
    ⟨trivial,⟨⟨bank_mono h.stride (by omega),bank_mono h.group (by omega),trivial⟩,
      bank_mono h.input (by omega),trivial⟩⟩
  have data (r : Fin n) : (addressExpr x).eval cleared (r.val:Word w)=
      ((x.owner.base+socket (encode (p.group r)) (p.input r):ℕ):Word w) := by
    rw [eval_below (addressExpr x) _ mem cleared (source_fits x h)
      (fun a ha => ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (.inl ha))]
    simp only [addressExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,load.group r,load.input r,
      load.stride (encode (p.group r)),socket_eq,Nat.cast_add]
  have bound (r : Fin n) := socket_lt (encode (p.group r)) (p.input r)
  have scatter : (ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (addressExpr x) rowCode).Exec
      cleared (image scratch x p encode mem) (ProtocolRAMGeneratedWrite.work n (addressExpr x) rowCode) :=
    ProtocolRAMGeneratedWrite.run scratch (scratch+n) (addressExpr x) rowCode
    (fun r => x.owner.base+socket (encode (p.group r)) (p.input r))
    (fun r => ((r.val+1 : ℕ) : Word w)) cleared src ⟨trivial,trivial⟩ (by omega) (by omega)
    data (fun r => by simp [rowCode,Expr.eval,RowOp.opcode,BinaryOp.eval])
    (fun r => by have := bound r; omega)
    (fun _ j => by have := bound j; omega) (fun _ j => by have := bound j; omega)
  have time : work n groups m = (4+(groups*m)*(2*(Expr.lit 0).work+4))+
      ProtocolRAMGeneratedWrite.work n (addressExpr x) rowCode := by
    simp only [work,ProtocolRAMGeneratedWrite.work,addressExpr,rowCode,Expr.work]
    ring
  rw [time]
  intro P R K M pc reg pub exit rom data cfg raw entry eq
  exact Procedure.Exec.then clear scatter M pc reg pub exit rom data cfg raw entry eq

theorem read_row (scratch : ℕ) (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (r : Fin n) :
    image scratch x p encode mem (x.owner.base+socket (encode (p.group r)) (p.input r))=
      ((r.val+1:ℕ):Word w) := by
  unfold image
  apply ProtocolRAMGeneratedWrite.read
  intro i j he
  obtain ⟨g,v⟩ := socket_inj (Nat.add_left_cancel he)
  exact p.input_inj (Prod.ext (encode.injective g) v)

theorem read_empty {scratch : ℕ} (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (h : Fits x w n groups m scratch) (g : Fin groups) (i : Fin m)
    (empty : ∀ r, ¬ (encode (p.group r)=g ∧ p.input r=i)) :
    image scratch x p encode mem (x.owner.base+socket g i)=0 := by
  have bound := socket_lt g i
  have low := (Nat.add_le_add_left h.count x.owner.base).trans h.owner.2.2
  have away (r : Fin n) : x.owner.base+socket g i≠x.owner.base+socket (encode (p.group r)) (p.input r) :=
    fun he => empty r (socket_inj (Nat.add_left_cancel he.symm))
  exact (ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ away (.inl (by omega))
    (.inl (by omega))).trans (ProtocolRAMGeneratedWrite.read_image _ _ _ _ ⟨_,bound⟩)

/-- Cells outside the owner range and its two scratch columns keep their former values. -/
theorem frame (scratch : ℕ) (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (a : ℕ) (out : a<x.owner.base ∨ x.owner.base+groups*m≤a)
    (temp : a<scratch ∨ scratch+2*n≤a) : image scratch x p encode mem a=mem a := by
  have away (r : Fin n) : a ≠ x.owner.base+socket (encode (p.group r)) (p.input r) := by
    have bound := socket_lt (encode (p.group r)) (p.input r)
    omega
  exact (ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ away (by omega) (by omega)).trans
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ out)

theorem below {scratch : ℕ} (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (h : Fits x w n groups m scratch) (a : ℕ) (ha : a<x.owner.base) :
    image scratch x p encode mem a=mem a := by
  exact frame scratch x p encode mem a (.inl ha) (.inl (by have lo := h.owner.2.2; omega))

theorem loaded_image {scratch : ℕ} (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (h : Fits x w n groups m scratch) (load : Loaded x p encode mem) :
    Loaded x p encode (image scratch x p encode mem) :=
  let same := below x p encode mem h
  ⟨resident_frame h.group same load.group,resident_frame h.input same load.input,
    resident_frame h.output same load.output,resident_frame h.stride same load.stride⟩

/-- All sockets, including unused sockets in encoded or unoccupied groups. -/
def Owners (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) : Prop :=
  ∀ g i, x.owner.read mem (socket g i:Word w)=(ownerValue p encode g i:Word w)

theorem owners_image {scratch : ℕ} (x : Columns) (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (mem : Memory w) (h : Fits x w n groups m scratch) : Owners x p encode (image scratch x p encode mem) := by
  intro g i
  have small := (socket_lt g i).trans_le h.count
  rw [Bank.read,Fin.val_cast_of_lt (small.trans h.owner.2.1),Nat.mod_eq_of_lt small,ownerValue]
  cases he : owner? p encode g i with
  | none =>
    apply read_empty x p encode mem h
    intro r hr
    have := (owner_some_iff p encode g i r).2 hr
    simp [he] at this
  | some r =>
    obtain ⟨eg,ei⟩ := (owner_some_iff p encode g i r).1 he
    rw [←eg,←ei]
    exact read_row scratch x p encode mem r

/-- A sampler lane encodes its optional output in the same one-based format as owners. -/
def nextWord (x : Columns) (choice : Bank) (rowExpr : Expr) : Expr :=
  let q := Expr.lookup choice (.lookup x.output rowExpr)
  .branch .eq q (.lit 0) (.lit 0) (.lookup x.owner (.op .add
    (.lookup x.stride (.lookup x.group rowExpr)) (.op .sub q (.lit 1))))

theorem nextWord_fits {out : ℕ} (x : Columns) (choice : Bank) (rowExpr : Expr)
    (ho : x.output.Fits w out) (hg : x.group.Fits w out) (hs : x.stride.Fits w out)
    (hc : choice.Fits w out) (hw : x.owner.Fits w out) (hr : rowExpr.Fits w out) :
    (nextWord x choice rowExpr).Fits w out :=
  ⟨⟨hc,ho,hr⟩,trivial,trivial,hw,⟨hs,hg,hr⟩,⟨hc,ho,hr⟩,trivial⟩

theorem nextWord_work (x : Columns) (choice : Bank) (rowExpr : Expr) :
    (nextWord x choice rowExpr).work=3*rowExpr.work+41 := by
  simp only [nextWord,Expr.work]
  omega

theorem nextWord_eval (x : Columns) (choice : Bank) (rowExpr : Expr) (p : Tiles (Fin n) G m)
    (encode : G ↪ Fin groups) (select : Fin m → Option (Fin m)) (mem : Memory w)
    (load : Loaded x p encode mem) (owners : Owners x p encode mem)
    (hc : Native.Resident choice mem (fun o => portCode (select o)))
    (hm : m < 2^w) (a : Word w) (r : Fin n) (hr : rowExpr.eval mem a=(r.val:Word w)) :
    (nextWord x choice rowExpr).eval mem a=(nextRow p encode select r:Word w) := by
  simp only [nextWord,Expr.eval,hr,load.output r,hc (p.output r),load.group r,
    load.stride (encode (p.group r)),RowOp.opcode,BinaryOp.eval,Comparison.test,nextRow]
  cases e : select (p.output r) with
  | none => simp [portCode]
  | some i =>
    have small : i.val+1<2^w := Nat.lt_of_le_of_lt i.isLt hm
    have nonzero : ((i.val+1:ℕ):Word w)≠0 := by
      intro eq
      have vals := congrArg Fin.val eq
      rw [Fin.val_cast_of_lt small,Fin.val_zero] at vals
      omega
    have sub : ((portCode (some i) : ℕ) : Word w) - 1 = (i.val:Word w) := by
      simp [portCode,Nat.cast_add]
    have lookup := owners (encode (p.group r)) i
    rw [socket_eq] at lookup
    simpa only [Option.bind_some, Nat.cast_zero, Nat.cast_one, beq_iff_eq,
      show (portCode (some i):Word w)≠0 from nonzero, ite_false, sub, ← Nat.cast_add,
      ownerValue] using lookup

theorem nextWord_image {scratch : ℕ} (x : Columns) (choice : Bank) (rowExpr : Expr)
    (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups) (select : Fin m → Option (Fin m))
    (mem : Memory w) (h : Fits x w n groups m scratch) (load : Loaded x p encode mem)
    (hc : Native.Resident choice mem (fun o => portCode (select o))) (cf : choice.Fits w x.owner.base)
    (a : Word w) (r : Fin n) (hr : rowExpr.eval (image scratch x p encode mem) a=(r.val:Word w)) :
    (nextWord x choice rowExpr).eval (image scratch x p encode mem) a=(nextRow p encode select r:Word w) := by
  have hg := (encode (p.group r)).isLt
  have cap : m ≤ groups*m := by
    simpa using Nat.mul_le_mul_right m (show 1≤groups by omega)
  exact nextWord_eval x choice rowExpr p encode select _ (loaded_image x p encode mem h load)
    (owners_image x p encode mem h) (resident_frame cf (below x p encode mem h) hc)
    ((cap.trans h.count).trans_lt h.owner.2.1) a r hr


end Hierarchy.ProtocolRAMPurchaseOwners

end OAI
