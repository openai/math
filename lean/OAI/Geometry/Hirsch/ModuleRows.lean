import OAI.Geometry.Hirsch.Panels

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {L V h B N C : ℕ} {code : Bundles L V}
  {tree : Forest I (Fin V) h} {ep : Episodes N}

theorem output_positive (eps : I → ℝ) (he : ∀ i, 0 < eps i) (i : I) (pos : Position V)
    (b : Fin B) (k : ℕ) : Monotone (output tree eps i pos b k) ∧ 0 < output tree eps i pos b k 1 := by
  induction k with
  | zero =>
    simp only [output,quick,base]
    split
    · split
      · exact ⟨fun _ _ hh => add_le_add (add_le_add (hh _) (hh _)) (hh _),by norm_num [P,W,terminal]⟩
      · exact ⟨fun _ _ hh => add_le_add (hh _) (hh _),by norm_num [W,terminal]⟩
    · rw [zero_add]
      exact ⟨fun _ _ hh => hh _,one_pos⟩
  | succ k ih =>
    rw [output]
    split
    · exact ⟨fun _ _ hh => add_le_add (add_le_add (hh _) (hh _))
        (mul_le_mul_of_nonneg_left (ih.1 hh) (he _).le),
        add_pos (add_pos one_pos one_pos) (mul_pos (he _) ih.2)⟩
    · exact ih

namespace Plan

variable (plan : Plan tree code ep B C)

abbrev Red (I : Type) (B V : ℕ) := I × Position V × Fin B
abbrev Pairs (tree : Forest I (Fin V) h) (N B : ℕ) :=
  Σ i, Position V × Fin (tree.depth i + 1) × Probe N B × Fin B × Fin B

abbrev Rows := (Σ i, (plan.panel i).Row) ⊕ Red I B V ⊕ Pairs tree N B

def red (i : I) (pos : Position V) (b : Fin B) : plan.Rows := .inr (.inl (i,pos,b))

def pair (i : I) (pos : Position V) (k : Fin (tree.depth i + 1)) (t : Probe N B) (b d : Fin B) :
    plan.Rows := .inr (.inr ⟨i,pos,k,t,b,d⟩)

def coeff : plan.Rows → Form I B V
  | .inl ⟨i,r⟩ => (plan.panel i).coeff r
  | .inr (.inl (i,pos,b)) => output tree plan.eps i pos b (tree.depth i)
  | .inr (.inr ⟨i,pos,k,_,b,d⟩) =>
    if b = d then output tree plan.eps i pos b k
    else output tree plan.eps i pos b k + output tree plan.eps i pos d k

def line (i : I) (k : ℕ) (t : Probe N B) :=
  if k = tree.depth i then Line.const 0 else plan.tangent (tree.node i k) t

theorem root_shift (i : I) (t : Probe N B) : plan.shift (tree.node i (tree.depth i)) t = 0 :=
  plan.root _ (by rw [tree.depth_node i le_rfl,Nat.sub_self]) _

theorem line_touch (i : I) (k : ℕ) (t : Probe N B) :
    plan.line i k t (plan.time t) = plan.shift (tree.node i k) t := by
  unfold line
  split
  · subst k; simp [plan.root_shift]
  · exact plan.touches ..

theorem line_below (i : I) (k : ℕ) (s t : Probe N B) :
    plan.line i k s (plan.time t) ≤ plan.shift (tree.node i k) t := by
  unfold line
  split
  · subst k; simp [plan.root_shift]
  · exact plan.below ..

def rhs : plan.Rows → Line
  | .inl ⟨i,r⟩ => (plan.panel i).rhs r
  | .inr (.inl _) => Line.const 0
  | .inr (.inr ⟨i,pos,k,t,b,d⟩) =>
    if b = d then plan.line i k t else (2 : ℝ) • plan.line i k t + Line.const (plan.gap i pos k)

def color : plan.Rows → Option (Fin B × I)
  | .inr (.inl (i,_,b)) => some (b,i)
  | _ => none

theorem coeff_pos (r : plan.Rows) : Monotone (plan.coeff r) ∧ 0 < plan.coeff r 1 := by
  have hout := output_positive (tree := tree) (B := B) plan.eps (fun i => (plan.par i).epos)
  rcases r with ⟨i,r⟩ | ⟨i,pos,b⟩ | ⟨i,pos,k,t,b,d⟩
  · exact ⟨(plan.panel i).mono r,(plan.panel i).pos r⟩
  · exact hout ..
  · simp only [coeff]
    split
    · exact hout ..
    · exact ⟨fun _ _ hh => add_le_add ((hout ..).1 hh) ((hout ..).1 hh),add_pos (hout ..).2 (hout ..).2⟩

theorem ordinary (x : Port I B V) : ∃ r, ∃ w : ℝ, plan.color r = none ∧
    0 < w ∧ plan.coeff r = w • LinearMap.proj x := by
  obtain ⟨i,role,pos⟩ := x
  obtain ⟨r,hr⟩ := (plan.panel i).individual role pos
  exact ⟨.inl ⟨i,r⟩,1,rfl,one_pos,by simpa [coeff] using hr⟩

def block : Blocking (Port I B V) plan.Rows where
  coeff := plan.coeff
  slope r := (plan.rhs r).slope
  offset r := (plan.rhs r).offset
  monotone r := (plan.coeff_pos r).1
  positive r := (plan.coeff_pos r).2
  individual x := by obtain ⟨r,w,_,hw⟩ := plan.ordinary x; exact ⟨r,w,hw⟩

def raised (t : Probe N B) (a : Red I B V → ℝ) : plan.Rows → ℝ
  | .inr (.inl r) => a r
  | r => plan.rhs r (plan.time t)

def value (t : Probe N B) (x : Space I B V) (i : I) (pos : Position V) (k : ℕ) (b : Fin B) :=
  output tree plan.eps i pos b k x - plan.shift (tree.node i k) t

theorem value_root (t : Probe N B) (x : Space I B V) (i : I) (pos : Position V) (b : Fin B) :
    plan.value t x i pos (tree.depth i) b = plan.coeff (plan.red i pos b) x := by
  simp [value,plan.root_shift,coeff,red]

theorem value_internal (t : Probe N B) (x : Space I B V) (i : I) (hi : tree.depth i < h)
    (pos : Position V) (b : Fin B) :
    plan.value t x i pos 0 b = base i pos x + terminal i b pos x - plan.shift i t := by
  simp [value,output,quick,hi,Forest.node]

theorem value_leaf (t : Probe N B) (x : Space I B V) (i : I) (hi : ¬tree.depth i < h)
    (pos : Position V) (b : Fin B) :
    plan.value t x i pos 0 b = terminal i b pos x - plan.shift i t := by
  simp [value,output,quick,hi,Forest.node]

theorem value_step (t : Probe N B) (x : Space I B V) (i : I) (pos : Position V) (k : ℕ)
    (hk : k < tree.depth i) (b : Fin B) :
    let j := tree.node i (k+1)
    plan.value t x i pos (k+1) b =
      plan.eps j * ((plan.net t x).cost j (tree.path i)[k].2 + plan.value t x i pos k b) := by
  have edge := tree.step_node i hk
  have hi := Network.parent_bound edge
  simp only [value,output_next _ _ _ _ _ hk,net,hi,↓reduceDIte,SampleData.cost,plan.child _ _ _ edge,
    price,eps]
  field_simp [(plan.par (tree.node i (k+1))).epos.ne']
  ring

end Plan
end OAI.Geometry.Hirsch.Layer
