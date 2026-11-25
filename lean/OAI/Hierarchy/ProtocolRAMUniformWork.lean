import OAI.Hierarchy.ProtocolRAMBatch

namespace OAI
/-! # Address- and width-independent size of the actual histogram controller -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr

/-- The syntax seen by the compiler's instruction counter. Replacing a literal,
comparison, column address or register-width mask leaves this tree unchanged. -/
inductive Expr.Form where
  | row
  | lit
  | load (i : Expr.Form)
  | op (x y : Expr.Form)
  | branch (x y a b : Expr.Form)

def Expr.form : Expr → Expr.Form
  | .row => .row
  | .lit _ => .lit
  | .lookup _ i => .load i.form
  | .op _ x y => .op x.form y.form
  | .branch _ x y a b => .branch x.form y.form a.form b.form

def Expr.Form.work : Expr.Form → ℕ
  | .row => 2
  | .lit => 1
  | .load i => i.work+5
  | .op x y => x.work+y.work+1
  | .branch x y a b => x.work+y.work+a.work+b.work+1

@[simp] theorem Expr.work_form (e : Expr) : e.form.work=e.work := by
  induction e <;> simp only [form,work,Form.work, *]

def Expr.Form.subst : Expr.Form → Expr.Form → Expr.Form
  | .row, i => i
  | .lit, _ => .lit
  | .load a, i => .load (a.subst i)
  | .op x y, i => .op (x.subst i) (y.subst i)
  | .branch x y a b, i => .branch (x.subst i) (y.subst i) (a.subst i) (b.subst i)

@[simp] theorem Expr.form_atRow (e i : Expr) : (e.atRow i).form=e.form.subst i.form := by
  induction e <;> simp only [atRow,form,Form.subst, *]

namespace UniformWork
def Same (e f : Expr) := e.form=f.form

theorem work {e f : Expr} (h : Same e f) : e.work=f.work := by
  simpa only [Expr.work_form] using congrArg Expr.Form.work h

theorem row : Same .row .row := rfl
theorem lit (u v : ℕ) : Same (.lit u) (.lit v) := rfl
theorem load {i j : Expr} (a b : Bank) (h : Same i j) : Same (.lookup a i) (.lookup b j) :=
  congrArg Expr.Form.load h
theorem op {x y a b : Expr} (t s : RowOp) (h : Same x a) (h' : Same y b) :
    Same (.op t x y) (.op s a b) := by
  simp only [Same,Expr.form] at *
  rw [h,h']
theorem branch {x y a b x' y' a' b' : Expr} (t s : Comparison) (hx : Same x x')
    (hy : Same y y') (ha : Same a a') (hb : Same b b') :
    Same (.branch t x y a b) (.branch s x' y' a' b') := by
  simp only [Same,Expr.form] at *
  rw [hx,hy,ha,hb]

theorem indexed {x y i j : Expr} (h : Same x y) (hi : Same i j) :
    Same (x.atRow i) (y.atRow j) := by
  unfold Same at *
  simp only [Expr.form_atRow,h,hi]

theorem fieldChoice {n : ℕ} (off off' : ℕ) (f g : Fin n→Expr) {i j : Expr}
    (h : ∀a,Same (f a) (g a)) (hi : Same i j) :
    Same (chooseField n off f i) (chooseField n off' g j) := by
  induction n generalizing off off' with
  | zero => rfl
  | succ _ ih =>
    exact branch _ _ hi (lit _ _) (h 0) (ih _ _ _ _ (fun a=>h a.succ))

theorem totals {n : ℕ} (f g : Fin n→Expr) (h : ∀j,Same (f j) (g j)) :
    Same (ProtocolRAM.totals n f) (ProtocolRAM.totals n g) := by
  induction n with
  | zero => rfl
  | succ n ih => exact op _ _ (h 0) (ih _ _ (fun j=>h j.succ))

theorem enough {n : ℕ} (f g a b : Fin n→Expr) {u u' v v' : Expr}
    (hf : ∀j,Same (f j) (g j)) (ha : ∀j,Same (a j) (b j)) (hu : Same u u') (hv : Same v v') :
    Same (ifEnough n f a u v) (ifEnough n g b u' v') := by
  induction n with
  | zero => exact hu
  | succ n ih => exact branch _ _ (ha 0) (hf 0) hv (ih _ _ _ _ (fun j=>hf j.succ) (fun j=>ha j.succ))

theorem histogram {n : ℕ} (t s : ℕ) (f g : Fin n→Expr) {u u' v v' : Expr}
    (hf : ∀j,Same (f j) (g j)) (hu : Same u u') (hv : Same v v') :
    Same (ifHistogram n t f u v) (ifHistogram n s g u' v') :=
  enough _ _ _ _ hf (fun _=>lit t s) (branch _ _ (totals _ _ hf) (lit t s) hu hv) hv

theorem scale (n : ℕ) {x y : Expr} (h : Same x y) : Same (ProtocolRAM.scale n x) (ProtocolRAM.scale n y) := by
  induction n with
  | zero => rfl
  | succ _ ih => exact op _ _ h ih

theorem times (n : ℕ) {x y a b : Expr} (h : Same x y) (hc : Same a b) :
    Same (boundedMul n x a) (boundedMul n y b) := by
  induction n with
  | zero => rfl
  | succ _ ih => exact branch _ _ hc (lit _ _) (scale _ h) ih

theorem menu (r : ℕ) {xs ys : List Expr} (h : List.Forall₂ Same xs ys) :
    Same (menuKey r xs) (menuKey r ys) := by
  induction h with
  | nil => rfl
  | cons first _ ih => exact op _ _ first (scale _ ih)

variable {q d : ℕ}

/-- The production source changes the batch size and the bit widths and addresses
of all its banks as the height increases. Only the fixed finite template catalogue
and the skeletons of the native row computations enter the bytecode size. -/
structure BatchForm (b c : Batch q d) : Prop where
  radix : b.radix=c.radix
  coefficients : b.maxWidth=c.maxWidth
  digits : List.Forall₂ Same b.quotes c.quotes
  owner : Same b.owner c.owner
  fields : ∀j,Same (b.field j) (c.field j)
  stocks : ∀j,Same (b.stock j) (c.stock j)
  prices : ∀j,Same (b.perCopy j) (c.perCopy j)

variable {b c : Batch q d}

theorem packet (h : BatchForm b c) : Same b.packet c.packet := by
  unfold Batch.packet menuLookup
  rw [h.radix]
  exact load _ _ (menu _ h.digits)

theorem need (h : BatchForm b c) (j : Fin d) : Same (b.need j) (c.need j) := by
  unfold Batch.need
  rw [h.coefficients]
  exact times _ (lit _ _) (h.prices j)

theorem selected (h : BatchForm b c) {u u' v v' : Expr} (hu : Same u u') (hv : Same v v') :
    Same (b.ifSelected u v) (c.ifSelected u' v') :=
  branch _ _ (load _ _ h.owner) (lit _ _) hv
    (branch _ _ (packet h) (lit _ _) hv (enough _ _ _ _ (need h) h.stocks hu hv))

theorem packetCheck (h : BatchForm b c) {u u' v v' : Expr} (hu : Same u u') (hv : Same v v') :
    Same (b.ifPacket u v) (c.ifPacket u' v') :=
  enough _ _ _ _ h.fields (fun _=>branch _ _ (lit _ _) (load _ _ (packet h)) (lit _ _) (lit _ _))
    (histogram _ _ _ _ h.fields hu hv) hv

theorem admission (h : BatchForm b c) {u u' v v' : Expr} (hu : Same u u') (hv : Same v v') :
    (b.ifAdmitted u v).work=(c.ifAdmitted u' v').work :=
  work (selected h (packetCheck h hu hv) (histogram _ _ _ _ h.fields hu hv))

theorem width (h : BatchForm b c) (f g : Fin q→Expr) (hf : ∀j,Same (f j) (g j)) :
    Same (b.wire f) (c.wire g) := by
  apply selected h _ (lit _ _)
  apply packetCheck h _ (lit _ _)
  unfold installed
  rw [h.coefficients]
  exact totals _ _ (fun j=>times _ (h.fields j) (hf j))

theorem update (h : BatchForm b c) (i : Fin d) {v v' : Expr} (hv : Same v v') :
    Same (b.nextStock i v) (c.nextStock i v') :=
  selected h (packetCheck h (op _ _ (op _ _ (h.stocks i) (need h i)) hv) (h.stocks i)) (h.stocks i)

theorem reportFields (h : BatchForm b c) (l l' : Link) (f g : Fin q→Expr)
    (hg : Same l.group l'.group) (he : Same l.endpoint l'.endpoint) (ho : Same l.opposite l'.opposite)
    (hl : Same l.lengthCode l'.lengthCode) (hf : ∀j,Same (f j) (g j)) (i : Fin 7) :
    Same (l.fields b f i) (l'.fields c g i) := by
  fin_cases i
  · exact hg
  · exact he
  · exact ho
  · exact op _ _ (lit _ _) row
  · exact width h f g hf
  · exact hl
  · exact selected h (packetCheck h (packet h) (lit _ _)) (lit _ _)

end UniformWork
end Hierarchy.ProtocolRAM

end OAI
