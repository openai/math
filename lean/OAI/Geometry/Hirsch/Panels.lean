import OAI.Geometry.Hirsch.Scene

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

structure Line where
  slope : ℝ
  offset : ℝ

instance : CoeFun Line (fun _ => ℝ → ℝ) := ⟨fun f x => f.slope * x + f.offset⟩

namespace Line

def const (a : ℝ) : Line := ⟨0,a⟩
instance : Add Line := ⟨fun f g => ⟨f.slope+g.slope,f.offset+g.offset⟩⟩
instance : SMul ℝ Line := ⟨fun a f => ⟨a*f.slope,a*f.offset⟩⟩

@[simp] theorem const_apply (a x : ℝ) : const a x = a := by change 0*x+a=a; ring
@[simp] theorem add_apply (f g : Line) (x : ℝ) : (f+g) x = f x + g x := by
  change (f.slope+g.slope)*x+(f.offset+g.offset) = (f.slope*x+f.offset)+(g.slope*x+g.offset)
  ring
@[simp] theorem smul_apply (a : ℝ) (f : Line) (x : ℝ) : (a • f) x = a * f x := by
  change (a*f.slope)*x+a*f.offset = a*(f.slope*x+f.offset)
  ring

end Line

variable {I : Type} {L V h B N : ℕ} {code : Bundles L V}

abbrev Probe (N B : ℕ) := Fin N × Fin B

structure Panel (I : Type) (B V : ℕ) (i : I) where
  Row : Type
  [finite : Fintype Row]
  coeff : Row → Form I B V
  rhs : Row → Line
  mono : ∀ r, Monotone (coeff r)
  pos : ∀ r, 0 < coeff r 1
  individual : ∀ role pos, ∃ r, coeff r = LinearMap.proj (i,role,pos)
  localizes : ∀ r, ∃ b : Fin B, ∀ x, (∀ pos, x (i,none,pos) = 0 ∧ x (i,some b,pos) = 0) →
    coeff r x = 0

attribute [instance] Panel.finite

namespace Panel

variable {i : I} (panel : Panel I B V i)

def Feasible (time : ℝ) (x : Space I B V) : Prop := ∀ r, panel.rhs r time ≤ panel.coeff r x
def Stops (time : ℝ) (x dir : Space I B V) : Prop :=
  ∀ r, panel.coeff r x = panel.rhs r time → panel.coeff r dir = 0

theorem silent {time : ℝ} {x dir : Space I B V} (hs : Silent dir i) : panel.Stops time x dir := by
  intro r _
  obtain ⟨b,hb⟩ := panel.localizes r
  exact hb _ (fun pos => ⟨hs none pos,hs (some b) pos⟩)

def Leaf (time shift : ℝ) (b : Fin B) : Prop :=
  ∀ x, panel.Feasible time x →
    (∀ pos d, d ≠ b → 1 < terminal i d pos x - shift) ∧
    ((∀ pos, shift ≤ terminal i b pos x) → ∀ f, panel.Stops time x (impulse i b 0 0 f 0))

def Internal {par : Parameters code} (time shift : ℝ) (b : Fin B) (data : SampleData par) : Prop :=
  ∀ x, panel.Feasible time x →
    let z := fun l => W i l x - shift/2 - data.shift
    let p := fun l => P i l x - shift
    let value := fun pos d => base i pos x + terminal i d pos x - shift
    data.Prices z p ∧
    (∀ l d, d ≠ b → z l ≤ value (false,l) d) ∧
    (∀ l d, d ≠ b → par.eps * (data.cost p l + par.lam) ≤ value (true,l) d) ∧
    ((∀ pos, 0 < value pos b) → ∀ w v f g, data.Motion z p w v f g →
      panel.Stops time x (impulse i b w v f g))

end Panel

structure Plan (tree : Forest I (Fin V) h) (code : Bundles L V) (ep : Episodes N) (B C : ℕ) where
  time : Probe N B → ℝ
  interior : ∀ t, time t ∈ Ioo (ep.left t.1) (ep.right t.1)
  panel : ∀ i, Panel I B V i
  rows : ∀ i, Fintype.card (panel i).Row ≤ C*N*B^2
  par : I → Parameters code
  shift : I → Probe N B → ℝ
  tangent : I → Probe N B → Line
  touches : ∀ i t, tangent i t (time t) = shift i t
  below : ∀ i s t, tangent i s (time t) ≤ shift i t
  root : ∀ i, tree.depth i = 0 → ∀ t, shift i t = 0
  margin : ∀ i j l, tree.path i = (j,l) :: tree.path j →
    10*(par j).delta < if tree.depth i < h then (par i).allow else 1/2
  data : ∀ i, tree.depth i < h → Probe N B → SampleData (par i)
  child : ∀ i j l (he : tree.path i = (j,l) :: tree.path j) t,
    (data j (Network.parent_bound he) t).child = shift i t
  leaf : ∀ i, ¬tree.depth i < h → ∀ t, (panel i).Leaf (time t) (shift i t) t.2
  internal : ∀ i hi t, (panel i).Internal (time t) (shift i t) t.2 (data i hi t)

namespace Plan

variable {tree : Forest I (Fin V) h} {ep : Episodes N} {C : ℕ} (plan : Plan tree code ep B C)

def size (i : I) := if tree.depth i < h then (plan.par i).allow else (1/2 : ℝ)
theorem size_pos (i : I) : 0 < plan.size i := by
  unfold size
  split
  · exact (plan.par i).allow_pos
  · norm_num

def price (t : Probe N B) (x : Space I B V) (i : I) (l : Fin V) := P i l x - plan.shift i t

def net (t : Probe N B) (x : Space I B V) : Network tree code where
  par := plan.par
  cost i := if hi : tree.depth i < h then (plan.data i hi t).cost (plan.price t x i) else 0
  size := plan.size
  positive := plan.size_pos
  internal i hi := by simp [size,hi]
  margin := plan.margin

def eps (i : I) := (plan.par i).eps

def gap (i : I) (pos : Position V) (k : ℕ) :=
  if k = 0 then if tree.depth i < h then
    if pos.1 then (plan.par i).allow else (plan.par i).mu
    else 1
  else plan.eps (tree.node i k) * (plan.par (tree.node i k)).delta

theorem gap_low (i : I) (pos : Position V) {k : ℕ} (hk : k ≤ tree.depth i) :
    plan.size (tree.node i k) ≤ plan.gap i pos k := by
  cases k with
  | zero =>
    change plan.size i ≤ plan.gap i pos 0
    by_cases hi : tree.depth i < h
    · simp only [gap,size,hi,↓reduceIte]
      split
      · rfl
      · exact (plan.par i).floorSmall
    · norm_num [gap,size,hi]
  | succ k =>
    have hi := Network.parent_bound (tree.step_node i hk)
    simp only [size,gap,hi,Nat.succ_ne_zero,↓reduceIte,eps,Parameters.allow,mul_div_assoc]
    let par := plan.par (tree.node i (k+1))
    exact mul_le_mul_of_nonneg_left (by linarith [par.lsmall,par.dpos] : par.lam/4 ≤ par.delta) par.epos.le

end Plan
end OAI.Geometry.Hirsch.Layer
