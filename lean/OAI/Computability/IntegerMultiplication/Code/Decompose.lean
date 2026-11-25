import OAI.Computability.IntegerMultiplication.Spindle.Mint

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Strip
variable (D : ℕ) (d : 2 ≤ D)
abbrev Finger (D : ℕ) := Fin D
def begin0 : Finger D := ⟨0,by omega⟩
def shiftc (_ : Unit) (v : Finger D) : Finger D × Tally :=
  if e : v.val+1 < D then (⟨v.val+1,e⟩,[]) else (begin0 D d,[()])
def catalog (u : Tally) : Tally × Finger D :=
  machine (shiftc D d) (u,begin0 D d)
theorem easy_catalog : Easy (catalog D d) :=
  Easy.machine (Easy.pair easy_id (Easy.const _))

theorem len_catalog (s : Tally) :
    s.length = D*(catalog D d s).1.length + (catalog D d s).2.val := by
  have e (l : Tally) (v : Finger D) :
      let c := machine (shiftc D d) (l,v)
      l.length+v.val=D*c.1.length+c.2.val := by
    dsimp only
    induction l generalizing v with
    | nil => simp [machine_nil]
    | cons u l ih =>
      rw [List.length_cons,machine_cons,shiftc]
      by_cases h : v.val+1 < D
      · rw [dite_eq_left h]
        specialize ih ⟨_,h⟩

        generalize hm : machine (shiftc D d) (l,(⟨_,h⟩:Fin D)) = p at ih ⊢
        obtain ⟨a,b⟩ := p
        dsimp at *
        rw [hm]; dsimp only
        omega
      · rw [dite_eq_right h]
        specialize ih (begin0 D d)
        generalize hm : machine (shiftc D d) (l,begin0 D d) = p at *
        obtain ⟨a,b⟩ := p
        dsimp [begin0] at *
        simp [Nat.mul_add]
        have := v.isLt
        rw [hm]; dsimp only
        omega
  simpa only [begin0,Nat.add_zero,catalog] using e s (begin0 D d)
-- state begins with supply e, degree 0. peel rem, promote.
abbrev Bank (_D : ℕ) := Tally × Tally × List Tally
def deposit (z : Finger D × Tally) := List.replicate z.1.val z.2
def stroke (z : Bank D) : Bank D :=
  let y := catalog D d z.1
  (y.1, ()::z.2.1, (deposit D (y.2,z.2.1)) ++ z.2.2)
private theorem easy_deposit : Easy (deposit D) := by
  let u := fun z : Finger D × Tally => tally z.1.val
  let v := fun z : Finger D × Tally => List.replicate D z.2
  have h : Easy u := Easy.fst.compose (Easy.finite (fun i : Finger D => tally i.val))
  have a : Easy v := by
    suffices hz : ∀ n:ℕ, Easy (fun z : Finger D × Tally => List.replicate n z.2) from hz D
    intro n ; induction n with
    | zero => exact Easy.const _
    | succ n ih => simp [List.replicate_succ]; fun_prop
  suffices dep : deposit D = fun z => (cutLists (u z,v z)).1 by
    rw [dep]; exact (easy_cut (h.pair a)).fstCompose
  ext z : 1
  have e := z.1.isLt
  simp [deposit,cutLists,u,v]
private theorem easy_stroke : Easy (stroke D d) := by
  have h := easy_deposit D
  have v := easy_catalog D d
  unfold stroke
  fun_prop

def crank (u : Bank D) (_ : Unit) := stroke D d u
def hashPlan (l : Tally) : List Tally :=
  (l.foldl (crank D d) (l,[],[])).2.2

private def rate (u : Bank D) := (u.1.length,u.2.1.length,u.2.2.length)
-- crude polynomial bound for fold. D constant. Bound encoding direct via per-step additive.
theorem size_stroke (u : Bank D) :
    size (stroke D d u) ≤ size u + (D*(2*u.2.1.length+2)+2) := by
  have h1 := len_catalog D d u.1
  have e := (catalog D d u.1).2.isLt
  have h0 : (catalog D d u.1).1.length ≤ u.1.length := by
    have := Nat.le_mul_of_pos_left ((catalog D d u.1).1.length) (by omega : 0 < D)
    omega
  simp only [stroke,size_prod,size_cons,size_tally, show size ()=1 from rfl]
  have app := size_append_right (deposit D ((catalog D d u.1).2,u.2.1)) u.2.2
  have h (l:Tally) (j) : size (List.replicate j l)=(size l+1)*j+1 := by
    induction j with
    | zero => simp
    | succ i ih => rw [List.replicate_succ,size_cons,ih,Nat.mul_add,Nat.mul_one]; omega
  unfold deposit at app
  rw [h,size_tally] at app
  -- size (deposit...) occurrences? term LHS stroke keeps deposit
  simp only [deposit]
  have hz := Nat.mul_le_mul_left (2*u.2.1.length+2) e.le
  rw [Nat.mul_comm D]
  dsimp only at app
  simp only [Nat.add_assoc, show 1+1=2 from rfl] at app
  omega

theorem poly_plan : Poly (hashPlan D d) := by
  have e := Poly.fold_left (f:=fun x : Bank D × Unit => crank D d x.1 x.2)
    (Easy.fst.compose (easy_stroke D d) |>.poly) (8*(D+1)) 3 (fun s l h => ?_)
  exact ((Easy.pair easy_id (Easy.pair easy_id (Easy.const _))).poly.compose e).sndCompose.sndCompose
  change size (l.foldl (crank D d) s.2) ≤ _
  have len (l:Tally) (u : Bank D) :
      size (l.foldl (crank D d) u) ≤ size u + (D*(2*u.2.1.length+2*l.length)+2)*l.length := by
    induction l generalizing u with
    | nil => simp
    | cons a l ih =>
      rw [List.foldl_cons,List.length_cons]
      obtain t := ih (crank D d u a)
      have hs := size_stroke D d u
      unfold crank at *
      rw [show ((stroke D d u).2.1).length = u.2.1.length+1 from rfl] at t
      apply t.trans
      rw [Nat.mul_add _ l.length, Nat.mul_one]
      have r : 2*(u.2.1.length+1)+2*l.length=2*u.2.1.length+2*(l.length+1) := by ring
      rw [r]
      have re := Nat.mul_le_mul_left D (show 2*u.2.1.length+2 ≤ 2*u.2.1.length+2*(l.length+1) by omega)
      omega
  let p := size s
  have a : l.length ≤ p := by
    unfold p
    rw [size_prod,size_tally]
    have := List.IsPrefix.length_le h
    omega
  have t : size s.2 ≤ p := by unfold p; exact (by change size s.2 ≤ size (s.1,s.2); simp only [size_prod]; omega)
  have j : s.2.2.1.length ≤ p := by
    change size (s.2.1,s.2.2.1,s.2.2.2) ≤ _ at t
    simp only [size_prod,size_tally] at t
    omega
  apply (len ..).trans
  calc
   _ ≤ p+ (D*(2*p+2*p)+2)*p := by gcongr
   _ ≤ 8*(D+1)*(p+1)^3 := by
    rw [← Nat.add_zero p] -- remove
    nlinarith [Nat.zero_le (p*p*p), Nat.zero_le (D*p*p*p)]

-- math
def volume (l : List Tally) := (l.map fun s => D^s.length).sum
theorem volume_cat (l g) : volume D (l++g)=volume D l+volume D g := by simp [volume]
theorem volume_rep (v:Tally) (i) :
    volume D (List.replicate i v)=i*D^v.length := by
  induction i with
  | zero => simp [volume]
  | succ i ih => simp only [List.replicate_succ,volume,List.map_cons,List.sum_cons] at *; rw [ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def stackValue (u : Bank D) :=
  u.1.length * D^u.2.1.length + volume D u.2.2
-- preserved in stroke
theorem stroke_eq (u) : stackValue D (stroke D d u)=stackValue D u := by
  have h := len_catalog D d u.1
  simp only [stackValue, stroke,List.length_cons,pow_succ, volume_cat,deposit,volume_rep]
  conv_rhs => rw [h] -- occurrences u.1.length inside h? expression only one
  ring

abbrev valid (u : Bank D) :=
  (∀ t∈u.2.2,t.length<u.2.1.length) ∧ ∀ x,u.2.2.count x<D
-- by proof that copied remain below only, length k strictly greater
theorem stroke_valid {u} (h : valid D u) : valid D (stroke D d u) := by
  constructor
  · intro t v
    simp only [stroke,deposit,List.mem_append,List.mem_replicate] at v
    rcases v with t|t
    · simp [stroke,t.2] -- name
    change _ < u.2.1.length+1
    have := h.1 _ t; omega
  intro i
  simp only [stroke,deposit,List.count_append,List.count_replicate] -- beq?
  by_cases e : i=u.2.1
  · subst i
    have hz : u.2.1∉u.2.2 := by intro e; have := h.1 _ e; omega
    simpa only [beq_self_eq_true, ↓reduceIte, List.count_eq_zero.mpr hz,
      add_zero] using ((catalog D d u.1).2.isLt)
  have hb : (u.2.1 == i) = false := beq_eq_false_iff_ne.mpr (Ne.symm e)
  simp only [hb, Bool.false_eq_true, ite_false, zero_add]
  exact h.2 i

theorem safePlan (l : Tally) :
    volume D (hashPlan D d l)=l.length ∧ ∀ i, (hashPlan D d l).count i < D := by
  have e (v:Tally) (u : Bank D) (h : valid D u) :
      let p := v.foldl (crank D d) u
      stackValue D p=stackValue D u ∧ p.2.1.length=v.length+u.2.1.length ∧ valid D p := by
    dsimp only; induction v generalizing u with
    | nil => simp; exact h
    | cons x v ih =>
      simp only [List.length_cons,List.foldl_cons,crank]
      specialize ih (stroke D d u) (stroke_valid D d h)
      simp only [stroke_eq] at ih
      refine ⟨ih.1, ?_, ih.2.2⟩
      have hz := ih.2.1
      rw [show (stroke D d u).2.1.length = u.2.1.length+1 from rfl, show v.length+(u.2.1.length+1) = v.length+1+u.2.1.length by omega] at hz
      exact hz
  obtain ⟨u,y,_,c⟩ := e l (l,[],[]) ⟨(by simp),fun _ => by simp; omega⟩
  let b := l.foldl (crank D d) (l,[],[])
  change stackValue D b = _ at u
  unfold stackValue at u
  change b.2.1.length=l.length+0 at y
  simp only [List.length_nil,pow_zero,Nat.mul_one,volume,List.map_nil,List.sum_nil,Nat.add_zero] at u
  change b.1.length * D^b.2.1.length+volume D (hashPlan D d l)=_ at u
  rw [y, Nat.add_zero] at u
  suffices v : b.1.length=0 from ⟨by rw [v,Nat.zero_mul,Nat.zero_add] at u; exact u,c⟩
  have h0 : ∀ n:ℕ,n+1 ≤ D^n := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; have := Nat.mul_le_mul ih d; omega
  have z := h0 l.length
  by_contra q
  have := Nat.le_mul_of_pos_left (D^l.length) (by omega : 0<b.1.length)
  omega
end Code

end IntegerMultiplication
end Computability
end OAI
