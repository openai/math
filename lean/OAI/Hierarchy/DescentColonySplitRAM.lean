import OAI.Hierarchy.DescentColonyScan
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # A physical RAM pass for a site row of propagated colony splits

Each lane reads occurrence weights and flags of previously computed layers from the
old tape. The known incoming graph and dyadic intervals determine the addresses and
comparison instructions. Absent depth rows denote the initial zero buffer.
-/

namespace Hierarchy.DescentColonies.SplitRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

variable {H k w out : ℕ}

def total {α : Type*} (field : α → Expr) : List α → Expr
  | [] => .lit 0
  | i :: is => .op .add (field i) (total field is)

def anyFlag {α : Type*} (field : α → Expr) : List α → Expr
  | [] => .lit 0
  | i :: is => .branch .eq (field i) (.lit 0) (anyFlag field is) (.lit 1)

private theorem eval_total {α : Type*} (field : α → Expr) (value : α → ℕ)
    (m : Memory w) (r : Word w) (source : ∀ i, (field i).eval m r = (value i : Word w))
    (xs : List α) : (total field xs).eval m r = ((xs.map value).sum : Word w) := by
  induction xs with
  | nil => simp [total,Expr.eval]
  | cons i is ih => simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,source,ih]

private theorem eval_anyFlag {α : Type*} (field : α → Expr) (value : α → Bool)
    (m : Memory w) (r : Word w) (one : (1 : Word w) ≠ 0)
    (source : ∀ i, (field i).eval m r = ((value i).toNat : Word w)) (xs : List α) :
    (anyFlag field xs).eval m r = (((xs.map value).any id).toNat : Word w) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
    cases h : value i <;> simp [anyFlag,Expr.eval,Comparison.test,source,ih,h,one]

theorem fits_total {α : Type*} (field : α → Expr) (fits : ∀ i, (field i).Fits w out)
    (xs : List α) : (total field xs).Fits w out := by
  induction xs with
  | nil => trivial
  | cons i is ih => exact ⟨fits i, ih⟩

theorem fits_anyFlag {α : Type*} (field : α → Expr) (fits : ∀ i, (field i).Fits w out)
    (xs : List α) : (anyFlag field xs).Fits w out := by
  induction xs with
  | nil => trivial
  | cons i is ih => exact ⟨fits i, trivial, ih, trivial⟩

theorem work_total {α : Type*} (field : α → Expr) (U : ℕ)
    (bound : ∀ i, (field i).work ≤ U) (xs : List α) :
    (total field xs).work ≤ 1 + xs.length * (U+1) := by
  induction xs with
  | nil => simp [total,Expr.work]
  | cons i is ih =>
    have h := bound i
    simp only [total,Expr.work,List.length_cons,Nat.succ_mul]
    omega

theorem work_anyFlag {α : Type*} (field : α → Expr) (U : ℕ)
    (bound : ∀ i, (field i).work ≤ U) (xs : List α) :
    (anyFlag field xs).work ≤ 1 + xs.length * (U+3) := by
  induction xs with
  | nil => simp [anyFlag,Expr.work]
  | cons i is ih =>
    have h := bound i
    simp only [anyFlag,Expr.work,List.length_cons,Nat.succ_mul]
    omega

theorem fits_choice (n start : ℕ) (f : Fin n → Expr) (fits : ∀ i, (f i).Fits w out) :
    (chooseField n start f .row).Fits w out := by
  induction n generalizing start with
  | zero => trivial
  | succ n ih => exact ⟨trivial,trivial,fits 0,ih _ _ (fun j => fits j.succ)⟩

theorem work_choice (n start U : ℕ) (f : Fin n → Expr) (bound : ∀ i, (f i).work ≤ U) :
    (chooseField n start f .row).work ≤ 1+n*(U+4) := by
  induction n generalizing start with
  | zero => simp [chooseField,Expr.work]
  | succ n ih =>
    have h := ih (start+1) (fun j => f j.succ) (fun j => bound j.succ)
    have z := bound 0
    simp only [chooseField,Expr.work,Nat.succ_mul]
    omega

def loadCell (base d : ℕ) (x y : Block k) : Expr :=
  if group d y = group d x then .lookup ⟨base,k⟩ (.lit y.val) else .lit 0

def flagCell (base : Option ℕ) (d : ℕ) (x y : Block k) : Expr :=
  match base with
  | none => .lit 0
  | some b => loadCell b d x y

/-- Direct interpretation of a possibly missing row on the preceding tape. -/
def flagWord (base : Option ℕ) (m : Memory w) (y : Block k) : Word w :=
  match base with
  | none => 0
  | some b => m (b+y.val)

def rows (incoming : Fin H → List (Fin H)) (D d : ℕ) (v : Fin H) :=
  (d+1,v) :: (incoming v).map (fun u => (d+D,u))

def lane (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ)
    (flagBase : ℕ → Fin H → Option ℕ) (D cap d : ℕ) (v : Fin H) (x : Block k) : Expr :=
  let ys := List.finRange (2^k)
  let weight := total (loadCell (loadBase v) d x) ys
  let marked := fun p : ℕ × Fin H => anyFlag (flagCell (flagBase p.1 p.2) d x) ys
  .branch .lt (.lit cap) weight (.lit 1) (anyFlag marked (rows incoming D d v))

/-- One native expression shared by the entire output column. -/
def expr (k : ℕ) (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ)
    (flagBase : ℕ → Fin H → Option ℕ) (D cap d : ℕ) (v : Fin H) : Expr :=
  chooseField (2^k) 0 (lane incoming loadBase flagBase D cap d v) .row

private theorem eval_loadCell (base d : ℕ) (x y : Block k) (m : Memory w) (r : Word w)
    (widthRoom : 2^k < 2^w) :
    (loadCell base d x y).eval m r = if group d y = group d x then m (base+y.val) else 0 := by
  by_cases h : group d y = group d x <;>
    simp [loadCell,h,Expr.eval,Bank.read,Bank.size,Fin.val_cast_of_lt (y.isLt.trans widthRoom),
      Nat.mod_eq_of_lt y.isLt]

theorem eval_flagCell (base : Option ℕ) (d : ℕ) (x y : Block k)
    (m : Memory w) (r : Word w) (widthRoom : 2^k < 2^w) :
    (flagCell base d x y).eval m r = if group d y = group d x then flagWord base m y else 0 := by
  cases base with
  | none => simp [flagCell,flagWord,Expr.eval]
  | some b => exact eval_loadCell b d x y m r widthRoom

theorem eval {incoming : Fin H → List (Fin H)} {loadBase : Fin H → ℕ}
    {flagBase : ℕ → Fin H → Option ℕ} {D cap d : ℕ} (v : Fin H) (m : Memory w)
    (load : Fin H → Block k → ℕ) (get : ℕ → Fin H → Block k → Bool)
    (widthRoom : 2^k < 2^w) (capRoom : cap < 2^w)
    (weights : ∀ y : Block k, m (loadBase v+y.val) = (load v y : Word w))
    (flags : ∀ z u (y : Block k), flagWord (flagBase z u) m y = ((get z u y).toNat : Word w))
    (x : Block k) (sumRoom : (Scan.readWeights load d v x).sum < 2^w) :
    (expr k incoming loadBase flagBase D cap d v).eval m (x.val : Word w) =
      ((Scan.rowValue incoming load get D cap d v x).toNat : Word w) := by
  have wide : 1 < 2^w := (show 1 ≤ 2^k from Nat.two_pow_pos k).trans_lt widthRoom
  have one : (1 : Word w) ≠ 0 := by
    intro h
    have value := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt wide] at value
  rw [expr,eval_chooseField _ _ _ _ _ _ x (by omega) (by
    simpa only [Expr.eval,Nat.zero_add] using Fin.val_cast_of_lt (x.isLt.trans widthRoom))]
  let r : Word w := x.val
  let ys := List.finRange (2^k)
  let q := fun y : Block k => if group d y=group d x then load v y else 0
  have massRead : (total (loadCell (loadBase v) d x) ys).eval m r =
      ((Scan.readWeights load d v x).sum : Word w) := by
    have hw (y : Block k) : (loadCell (loadBase v) d x y).eval m r = (q y : Word w) := by
      rw [eval_loadCell _ _ _ _ _ _ widthRoom]
      by_cases h : group d y=group d x <;> simp [q,h,weights]
    simpa only [ys,List.finRange,List.map_ofFn,Function.comp_def,id_eq,Scan.readWeights,q] using
      eval_total _ q m r hw ys
  let bit := fun (p : ℕ × Fin H) (y : Block k) => decide (group d y=group d x) && get p.1 p.2 y
  let marked := fun p : ℕ × Fin H => (List.ofFn (bit p)).any id
  have readRow (p : ℕ × Fin H) :
      (anyFlag (flagCell (flagBase p.1 p.2) d x) ys).eval m r = ((marked p).toNat : Word w) := by
    have hf (y : Block k) : (flagCell (flagBase p.1 p.2) d x y).eval m r = ((bit p y).toNat : Word w) := by
      rw [eval_flagCell _ _ _ _ _ _ widthRoom]
      by_cases h : group d y=group d x <;> simp [h,bit,flags]
    simpa only [marked,ys,List.finRange,List.map_ofFn,Function.comp_def,id_eq] using
      eval_anyFlag _ (bit p) m r one hf ys
  have readings : (rows incoming D d v).map marked = Scan.readRows incoming get D d v x := by
    simp only [rows,List.map_cons,List.map_map,Function.comp_def]; rfl
  have markRead := eval_anyFlag _ marked m r one readRow (rows incoming D d v)
  rw [readings] at markRead
  change (if Comparison.lt.test (cap : Word w) _ then (1 : Word w) else _) = _
  rw [show (total (loadCell (loadBase v) d x) ys).eval m (x.val : Word w) = _ from massRead,
    show (anyFlag _ (rows incoming D d v)).eval m (x.val : Word w) = _ from markRead]
  have cmp : Comparison.lt.test (cap:Word w) ((Scan.readWeights load d v x).sum:Word w)=
      decide (cap < (Scan.readWeights load d v x).sum) := by
    simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt capRoom,Fin.val_cast_of_lt sumRoom]
  rw [cmp]
  by_cases heavy : cap < (Scan.readWeights load d v x).sum <;> simp [Scan.rowValue,heavy]

theorem fits_loadCell (b d : ℕ) (x y : Block k) (fit : (Bank.mk b k).Fits w out) :
    (loadCell b d x y).Fits w out := by
  by_cases h : group d y=group d x <;> simp [loadCell,h,Expr.Fits,fit]

theorem fits {incoming : Fin H → List (Fin H)} {loadBase : Fin H → ℕ}
    {flagBase : ℕ → Fin H → Option ℕ} {D cap d : ℕ} (v : Fin H)
    (old : (Bank.mk (loadBase v) k).Fits w out)
    (deeper : ∀ z u b, flagBase z u = some b → (Bank.mk b k).Fits w out) :
    (expr k incoming loadBase flagBase D cap d v).Fits w out := by
  unfold expr
  apply fits_choice
  intro x
  refine ⟨trivial,fits_total _ (fun y => fits_loadCell _ _ x y old) _,trivial,?_⟩
  apply fits_anyFlag
  intro p
  apply fits_anyFlag
  intro y
  cases h : flagBase p.1 p.2 with
  | none => simp [flagCell,Expr.Fits]
  | some b => simpa [flagCell,h] using fits_loadCell b d x y (deeper _ _ b h)

theorem work_loadCell (b d : ℕ) (x y : Block k) : (loadCell b d x y).work ≤ 6 := by
  by_cases h : group d y=group d x <;> simp [loadCell,h,Expr.work]

/-- The checked instruction bound depends only on the number of blocks and the
number of incoming sites, including repeated mentions in the physical graph list. -/
def workBound (k deg : ℕ) :=
  let n := 2^k
  1 + n*((1+n*7) + (1+(deg+1)*((1+n*9)+3)) + 3 + 4)

theorem work (k : ℕ) (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ)
    (flagBase : ℕ → Fin H → Option ℕ) (D cap d : ℕ) (v : Fin H) :
    (expr k incoming loadBase flagBase D cap d v).work ≤ workBound k (incoming v).length := by
  unfold expr workBound
  apply work_choice
  intro x
  let ys := List.finRange (2^k)
  have weight := work_total _ 6 (work_loadCell (loadBase v) d x) ys
  have bit (p : ℕ × Fin H) (y : Block k) : (flagCell (flagBase p.1 p.2) d x y).work ≤ 6 := by
    cases h : flagBase p.1 p.2 with
    | none => simp [flagCell,Expr.work]
    | some b => simpa only [flagCell,h] using work_loadCell b d x y
  have marked (p : ℕ × Fin H) := work_anyFlag _ 6 (bit p) ys
  have all := work_anyFlag _ _ marked (rows incoming D d v)
  simp only [ys,List.length_finRange] at weight all
  simp only [rows,List.length_cons,List.length_map] at all
  dsimp only [lane,Expr.work]
  simp only [rows] at *
  simp only [show (6:ℕ)+3=9 by decide] at all
  omega

abbrev program (w out k : ℕ) (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ)
    (flagBase : ℕ → Fin H → Option ℕ) (D cap d : ℕ) (v : Fin H) :=
  scan w out (2^k) (expr k incoming loadBase flagBase D cap d v)

theorem run {incoming : Fin H → List (Fin H)} {loadBase : Fin H → ℕ}
    {flagBase : ℕ → Fin H → Option ℕ} {D cap d : ℕ} (v : Fin H) (m : Memory w)
    (old : (Bank.mk (loadBase v) k).Fits w out)
    (deeper : ∀ z u b, flagBase z u = some b → (Bank.mk b k).Fits w out)
    (room : out+2^k < 2^w) :
    (program w out k incoming loadBase flagBase D cap d v).Exec m
      (image out (2^k) (expr k incoming loadBase flagBase D cap d v) m)
      (4+2^k*(2*(expr k incoming loadBase flagBase D cap d v).work+4)) :=
  scan_exec out _ _ m (fits v old deeper) room

theorem clock_bound (k : ℕ) (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ)
    (flagBase : ℕ → Fin H → Option ℕ) (D cap d : ℕ) (v : Fin H) :
    4+2^k*(2*(expr k incoming loadBase flagBase D cap d v).work+4) ≤
      4+2^k*(2*workBound k (incoming v).length+4) := by
  have h := work k incoming loadBase flagBase D cap d v
  gcongr

/-- Read the actual word at any output offset. -/
theorem published {incoming : Fin H → List (Fin H)} {loadBase : Fin H → ℕ}
    {flagBase : ℕ → Fin H → Option ℕ} {D cap d : ℕ} (v : Fin H) (m : Memory w)
    (load : Fin H → Block k → ℕ) (get : ℕ → Fin H → Block k → Bool)
    (room : out+2^k < 2^w) (capRoom : cap < 2^w)
    (weights : ∀ y : Block k, m (loadBase v+y.val) = (load v y : Word w))
    (flags : ∀ z u (y : Block k), flagWord (flagBase z u) m y = ((get z u y).toNat : Word w))
    (x : Block k) (sumRoom : (Scan.readWeights load d v x).sum < 2^w) :
    image out (2^k) (expr k incoming loadBase flagBase D cap d v) m (out+x.val) =
      ((Scan.rowValue incoming load get D cap d v x).toNat : Word w) := by
  simpa [ProtocolRAM.image,fillSegment,Nat.add_lt_add_left x.isLt,Nat.cast_add] using
    eval (incoming:=incoming) (D:=D) v m load get (by omega : 2^k < 2^w) capRoom weights flags x sumRoom

end Hierarchy.DescentColonies.SplitRAM

end OAI
