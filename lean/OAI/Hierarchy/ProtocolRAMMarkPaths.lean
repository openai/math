import OAI.Hierarchy.ProtocolRAMMarkTape
import OAI.Hierarchy.ProbePathScan

namespace OAI
/-! # The native mark-scan tape for the ordered sampler paths -/

namespace Hierarchy.ProtocolRAM.MarkTape
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical

def both (a b tmp dst : ℕ) : List Gate := [⟨a,b,tmp⟩,⟨tmp,tmp,dst⟩]

def test (work tile : ℕ) := both (work+1) (work+4+tile) (work+2) (work+1)

def clear (work tile : ℕ) := both (work+3) (work+4+tile) (work+2) (work+4+tile)

def compilePath (tiles work i : ℕ) (p : List (Fin tiles)) : List Gate :=
  ((([⟨work,work,work+1⟩] ++ p.flatMap (fun v=>test work v.val)) ++
    [⟨work+1,work+1,work+3⟩]) ++ p.flatMap (fun v=>clear work v.val)) ++
    [⟨work+3,work+3,work+4+tiles+i⟩]

def compilePaths (tiles work : ℕ) : ℕ → List (List (Fin tiles)) → List Gate
  | _,[] => []
  | first,p::ps => compilePath tiles work first p ++ compilePaths tiles work (first+1) ps

theorem compilePath_size (tiles work i : ℕ) (p : List (Fin tiles)) :
    (compilePath tiles work i p).length=4*p.length+3 := by
  have tests : (p.flatMap (fun v=>test work v.val)).length=2*p.length := by
    induction p with
    | nil => rfl
    | cons v vs ih => simp [test,both,Nat.mul_add]; omega
  have clears : (p.flatMap (fun v=>clear work v.val)).length=2*p.length := by
    induction p with
    | nil => rfl
    | cons v vs ih => simp [clear,both,Nat.mul_add]; omega
  simp only [compilePath,List.length_append,List.length_singleton,tests,clears]
  omega

theorem compilePaths_size (tiles work first : ℕ) (ps : List (List (Fin tiles))) (H : ℕ)
    (fixed : ∀ p∈ps,p.length=H) : (compilePaths tiles work first ps).length=ps.length*(4*H+3) := by
  induction ps generalizing first with
  | nil => simp [compilePaths]
  | cons p ps ih =>
    simp only [compilePaths,List.length_append,compilePath_size,List.length_cons,Nat.succ_mul]
    rw [fixed p (List.mem_cons_self ..),ih (first+1) (fun q h=>fixed q (List.mem_cons_of_mem p h))]
    ring

def Gate.boolStep (g : Gate) (m : ℕ→Bool) : ℕ→Bool :=
  Function.update m g.dst (!(m g.lhs && m g.rhs))

def boolean (gs : List Gate) (m : ℕ→Bool) := gs.foldl (fun a g=>g.boolStep a) m

@[simp] theorem boolean_append (xs ys : List Gate) (m : ℕ→Bool) :
    boolean (xs++ys) m=boolean ys (boolean xs m) := List.foldl_append ..

theorem both_step (a b tmp dst : ℕ) (m : ℕ→Bool) :
    boolean (both a b tmp dst) m =
      Function.update (Function.update m tmp (!(m a && m b))) dst (m a && m b) := by
  simp [both,boolean,Gate.boolStep]

def Holds {tiles : ℕ} (work : ℕ) (m : ℕ→Bool) (left : Finset (Fin tiles)) : Prop :=
  ∀ v, m (work+4+v.val)=decide (v∈left)

private theorem test_holds {tiles : ℕ} (work : ℕ) (v : Fin tiles) {m : ℕ→Bool}
    {left : Finset (Fin tiles)} (h : Holds work m left) :
    Holds work (boolean (test work v.val) m) left := by
  intro j
  rw [test,both_step,Function.update_of_ne (by omega : work+4+j.val≠work+1),
    Function.update_of_ne (by omega : work+4+j.val≠work+2),h]

private theorem test_pass {tiles : ℕ} (work : ℕ) (p : List (Fin tiles)) (m : ℕ→Bool)
    (left : Finset (Fin tiles)) (h : Holds work m left) :
    let out := boolean (p.flatMap (fun v=>test work v.val)) m
    Holds work out left ∧ out (work+1)=(m (work+1) && decide (p.toFinset⊆left)) := by
  induction p generalizing m with
  | nil => simp [boolean,h]
  | cons v vs ih =>
    rw [List.flatMap_cons,boolean_append]
    obtain ⟨keep,pass⟩ := ih (boolean (test work v.val) m) (test_holds _ _ h)
    refine ⟨keep,?_⟩
    rw [pass,test,both_step,Function.update_self,h v]
    simp [Bool.and_assoc,Finset.insert_subset_iff]

private theorem clear_pass {tiles : ℕ} (work : ℕ) (p : List (Fin tiles)) (m : ℕ→Bool) :
    let out := boolean (p.flatMap (fun v=>clear work v.val)) m
    out (work+3)=m (work+3) ∧ ∀ j : Fin tiles,
      out (work+4+j.val)=((m (work+4+j.val)) && (decide (j∉p) || m (work+3))) := by
  induction p generalizing m with
  | nil => simp [boolean]
  | cons v vs ih =>
    rw [List.flatMap_cons,boolean_append]
    let next := boolean (clear work v.val) m
    obtain ⟨keep,states⟩ := ih next
    have neg : next (work+3)=m (work+3) := by
      simp [next,clear,both_step,Function.update_of_ne (by omega : work+3≠work+4+v.val)]
    refine ⟨keep.trans neg,?_⟩
    intro j
    rw [states,neg]
    by_cases same : j=v
    · subst j
      simp [next,clear,both_step,Bool.and_assoc];
        cases m (work+3) <;> simp_all
    · have away : work+4+j.val ≠ work+4+v.val := by
        intro he
        exact same (Fin.ext (by omega))
      simp [next,clear,both_step,Function.update_of_ne away,Function.update_of_ne (by omega : work+4+j.val≠work+2),same]

private theorem boolean_frame (gs : List Gate) (m : ℕ→Bool) (a : ℕ) (s : ∀g∈gs,a≠g.dst) :
    boolean gs m a=m a := by
  induction gs generalizing m with
  | nil => rfl
  | cons g gs ih =>
    exact (ih (g.boolStep m) (fun c hc=>s c (List.mem_cons_of_mem g hc))).trans
      (Function.update_of_ne (s g (List.mem_cons_self ..)) ..)

theorem path_frame (tiles work i : ℕ) (p : List (Fin tiles)) (m : ℕ→Bool) (a : ℕ)
    (out : a≠work+4+tiles+i) (away : a=work ∨ work+4+tiles≤a) :
    boolean (compilePath tiles work i p) m a=m a := by
  apply boolean_frame
  intro g hg
  simp only [compilePath,List.mem_append,List.mem_singleton,List.mem_flatMap] at hg
  rcases hg with (((root|⟨v,_,step⟩)|last)|⟨v,_,step⟩)|destination
  · subst g; simp; omega
  · simp only [test,both,List.mem_cons,List.not_mem_nil,or_false] at step
    rcases step with rfl|rfl <;> simp <;> omega
  · subst g; simp; omega
  · simp only [clear,both,List.mem_cons,List.not_mem_nil,or_false] at step
    rcases step with rfl|rfl <;> simp <;> have := v.isLt <;> omega
  · subst g; exact out

/-- One candidate writes its purchase bit and simultaneously removes all its tiles if
the real pre-purchase tile bank covered the complete path. Repeated addresses are safe. -/
theorem path_semantics (tiles work i : ℕ) (p : List (Fin tiles)) (m : ℕ→Bool)
    (left : Finset (Fin tiles)) (zero : m work=false) (loaded : Holds work m left) :
    let out := boolean (compilePath tiles work i p) m
    out (work+4+tiles+i)=decide (p.toFinset⊆left) ∧
      Holds work out (if p.toFinset⊆left then left\p.toFinset else left) := by
  let start := Function.update m (work+1) true
  let tested := boolean (p.flatMap (fun v=>test work v.val)) start
  let neg := Function.update tested (work+3) (!(tested (work+1)))
  let cleared := boolean (p.flatMap (fun v=>clear work v.val)) neg
  have hstart : Holds work start left := fun v=>by
    simp [start,Function.update_of_ne (by omega : work+4+v.val≠work+1),loaded v]
  obtain ⟨htest,flag⟩ := test_pass work p start left hstart
  change tested (work+1)=_ at flag
  simp only [start,Function.update_self,Bool.true_and] at flag
  have hneg : Holds work neg left := fun v=>by
    change Function.update tested (work+3) _ (work+4+v.val)=_
    rw [Function.update_of_ne (by omega : work+4+v.val≠work+3)]
    exact htest v
  obtain ⟨f,data⟩ := clear_pass work p neg
  change cleared (work+3)=neg (work+3) at f
  have eqn : cleared (work+3)= !(decide (p.toFinset⊆left)) := by simpa [neg,flag] using f
  have result : boolean (compilePath tiles work i p) m =
      Function.update cleared (work+4+tiles+i) (decide (p.toFinset⊆left)) := by
    have setFlag : boolean [⟨work,work,work+1⟩] m = start := by
      simp [boolean,Gate.boolStep,start,zero]
    have setNeg : boolean [⟨work+1,work+1,work+3⟩] tested = neg := by
      simp [boolean,Gate.boolStep,neg]
    simp only [compilePath,boolean_append,setFlag]
    change boolean [_] (boolean _ (boolean [_] tested))=_
    rw [setNeg]
    change Function.update cleared _ (!(cleared (work+3) && cleared (work+3)))=_
    simp [eqn]
  rw [result]
  refine ⟨Function.update_self ..,?_⟩
  intro v
  have lt := v.isLt
  rw [Function.update_of_ne (by omega : work+4+v.val≠work+4+tiles+i)]
  change boolean _ neg _=_
  rw [data,hneg,show neg (work+3)= !(decide (p.toFinset⊆left)) from by simp [neg,flag]]
  by_cases take : p.toFinset⊆left <;> simp [take,Bool.and_comm]

def decisions {tiles : ℕ} : List (List (Fin tiles)) → Finset (Fin tiles) → List Bool
  | [],_ => []
  | p::ps,left =>
    decide (p.toFinset⊆left) :: decisions ps (if p.toFinset⊆left then left\p.toFinset else left)

@[simp] theorem decisions_length {tiles : ℕ} (ps : List (List (Fin tiles))) (left : Finset (Fin tiles)) :
    (decisions ps left).length=ps.length := by
  induction ps generalizing left <;> simp_all [decisions]

theorem decisions_selected {tiles : ℕ} (ps : List (List (Fin tiles))) (left : Finset (Fin tiles)) :
    ((ps.zip (decisions ps left)).filterMap (fun row=>if row.2 then some row.1 else none)) =
      (AdaptiveProbe.scanPaths ps left).1 := by
  induction ps generalizing left with
  | nil => rfl
  | cons p ps ih =>
    by_cases use : p.toFinset⊆left <;> simp [decisions,AdaptiveProbe.scanPaths,use,ih]

theorem decisions_count {tiles : ℕ} (ps : List (List (Fin tiles))) (left : Finset (Fin tiles)) :
    (decisions ps left).count true=(AdaptiveProbe.scanPaths ps left).1.length := by
  induction ps generalizing left with
  | nil => rfl
  | cons p ps ih =>
    by_cases use : p.toFinset⊆left <;> simp [decisions,AdaptiveProbe.scanPaths,use,ih]

theorem keep_old (tiles work first : ℕ) (ps : List (List (Fin tiles))) (m : ℕ→Bool) (a : ℕ)
    (low : a=work ∨ (work+4+tiles≤a ∧ a<work+4+tiles+first)) :
    boolean (compilePaths tiles work first ps) m a=m a := by
  induction ps generalizing m first with
  | nil => rfl
  | cons p ps ih =>
    rw [compilePaths,boolean_append,ih (first+1) _ (by rcases low with z|hi; exact Or.inl z; right; omega)]
    exact path_frame _ _ _ _ _ _ (by omega) (by omega)

/-- Read back every selected candidate and the exact remaining live tiles. -/
theorem paths_semantics (tiles work first : ℕ) (ps : List (List (Fin tiles))) (m : ℕ→Bool)
    (left : Finset (Fin tiles)) (zero : m work=false) (loaded : Holds work m left) :
    let out := boolean (compilePaths tiles work first ps) m
    Holds work out (AdaptiveProbe.scanPaths ps left).2 ∧
      ∀ (i : ℕ) (hi : i<ps.length), out (work+4+tiles+first+i) =
        (decisions ps left)[i]'(by simpa using hi) := by
  induction ps generalizing left m first with
  | nil => exact ⟨loaded,by simp⟩
  | cons p ps ih =>
    let mid := boolean (compilePath tiles work first p) m
    let rest := if p.toFinset⊆left then left\p.toFinset else left
    obtain ⟨flag,holds⟩ := path_semantics tiles work first p m left zero loaded
    have midZero : mid work=false := (path_frame _ _ _ _ _ _ (by omega) (Or.inl rfl)).trans zero
    obtain ⟨leftover,purchases⟩ := ih (first+1) mid rest midZero holds
    simp only [compilePaths,boolean_append]
    refine ⟨?_,?_⟩
    · by_cases used : p.toFinset⊆left <;> simpa [AdaptiveProbe.scanPaths,rest,used] using leftover
    · intro i hi
      cases i with
      | zero =>
        simpa only [Nat.add_zero,decisions,List.getElem_cons_zero] using
          (keep_old tiles work (first+1) ps mid (work+4+tiles+first) (Or.inr (by omega))).trans flag
      | succ i =>
        simpa [decisions,rest,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using purchases i (by simpa using hi)

def encode (w : ℕ) (b : Bool) : Word w := if b then 1 else 0

theorem encode_nand (w : ℕ) (a b : Bool) :
    1-BinaryOp.bitAnd.eval (encode w a) (encode w b) = encode w (!(a&&b)) := by
  cases a <;> cases b <;> simp [encode,BinaryOp.eval]
  change (1 : Word w)-((1 : Word w).val : Word w)=0
  rw [Fin.cast_val_eq_self,sub_self]

/-- The actual native live-word memory agrees with Boolean simulation everywhere in
the addressed region. Outside this region the program may store arbitrary addresses. -/
theorem eval_bits {w : ℕ} (gs : List Gate) (m : Memory w) (bits : ℕ→Bool) (region : ℕ→Prop)
    (loaded : ∀ a,region a → m a=encode w (bits a))
    (reads : ∀ g∈gs,region g.lhs ∧ region g.rhs) :
    ∀ a,region a → eval gs m a=encode w (boolean gs bits a) := by
  induction gs generalizing m bits with
  | nil => exact loaded
  | cons g gs ih =>
    apply ih (g.apply m) (g.boolStep bits) _ (fun v hv=>reads v (List.mem_cons_of_mem g hv))
    intro a ha
    obtain ⟨x,y⟩ := reads g (List.mem_cons_self ..)
    by_cases eqn : a=g.dst
    · subst a
      simp only [Gate.apply,Gate.boolStep,Function.update_self,loaded _ x,loaded _ y,encode_nand]
    · simpa [Gate.apply,Gate.boolStep,Function.update_of_ne eqn] using loaded a ha


end Hierarchy.ProtocolRAM.MarkTape

end OAI
