import OAI.Computability.IntegerMultiplication.Toom.Evaluate
import OAI.Computability.IntegerMultiplication.Code.Children

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Toom
open Code Bits Finset

variable {K : ℕ} [NeZero K]

def fetch (k : ℕ) (l : List Word) : Word := l[k]?.getD []

@[fun_prop] theorem easy_fetch {X : Type*} (k : ℕ) [Codec X] {f : X → List Word} (h : Easy f) :
    Easy (fun x => fetch k (f x)) := by
  apply h.compose
  induction k with
  | zero =>
    have h := Easy.listCase (X := Word) [] Easy.fst
    convert h
    rename_i i; cases i <;> rfl
  | succ k ih =>
    have h := Easy.listCase [] (Easy.snd.compose (show Easy (fetch k) from ih))
    convert h
    rename_i i; cases i <;> rfl

def mulR (n : ℕ) (r : Tally) : Tally :=
  match n with
  | 0 => []
  | k+1 => r ++ mulR k r

@[simp] theorem mulR_length (n r) : (mulR n r).length=n*r.length := by induction n <;> simp_all [mulR,add_mul,Nat.add_comm]

@[fun_prop] theorem easy_mulR {X : Type*} (n) [Codec X] {f : X → Tally} (h : Easy f) :
    Easy (fun x => mulR n (f x)) := by
  induction n
  · exact Easy.const _
  · unfold mulR; fun_prop

noncomputable def gather (n : ℕ) (c : ℤ → ℕ) (q : List Word × Tally) : Word :=
  sumbits (List.ofFn fun j : Fin n => shift (mulR j.val q.2,
    sumbits (List.ofFn fun i : Fin n =>
      scale (c (numer n j i)) (fetch i.val q.1))))

@[fun_prop] theorem easy_gather {X : Type*} (n c) [Codec X] {f : X→List Word × Tally} (h : Easy f) :
    Easy (fun i => gather n c (f i)) := by
  unfold gather
  apply easy_big_sum (n:=n)
  intro j
  apply easy_shift
  apply Easy.pair (easy_mulR _ h.sndCompose)
  apply easy_big_sum (n:=n)
  intro k
  exact easy_scale _ (easy_fetch _ h.fstCompose)

theorem gather_spec (n c q) :
    value (gather n c q) = combine c n (2^q.2.length) (fun i => value (fetch i.val q.1)) := by
  unfold gather combine
  simp [List.map_ofFn,List.sum_ofFn,Function.comp_def,scale_exact,pow_mul,Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  rw [← pow_mul, ← pow_mul,Nat.mul_comm j.val]
  ring

noncomputable def joiner (K : ℕ) (q : List Word × Tally) :=
  let z := (sub (gather (2*K) positive q,gather (2*K) negative q)).1
  have : NeZero (denom (2*K)) := ⟨Nat.ne_of_gt denom_pos⟩
  qword (p := denom (2*K)) z

@[fun_prop] theorem easy_joiner {X : Type*} (K) [Codec X] {f : X→List Word × Tally} (h : Easy f) :
    Easy (fun i => joiner K (f i)) := by
  have : NeZero (denom (2*K)) := ⟨Nat.ne_of_gt denom_pos⟩
  unfold joiner
  apply easy_qword
  apply Easy.fstCompose
  apply easy_sub
  fun_prop

omit [NeZero K] in
theorem joiner_spec (f g : Fin K → ℕ) (r : Tally) (l : Fin (2*K) → Word)
    (h : ∀ i, value (l i)=weigh i.val f*weigh i.val g) :
    value (joiner K (List.ofFn l,r))= weigh (2^r.length) f * weigh (2^r.length) g := by
  have : NeZero (denom (2*K)) := ⟨Nat.ne_of_gt denom_pos⟩
  let a := gather (2*K) positive (List.ofFn l,r)
  let b := gather (2*K) negative (List.ofFn l,r)
  have he := recover_sub f g (2^r.length)
  have eq (c) : value (gather (2*K) c (List.ofFn l,r)) =
      combine c (2*K) (2^r.length) (fun i : Fin (2*K) => weigh i.val f*weigh i.val g) := by
    rw [gather_spec]; congr 1
    funext i; simp [fetch,h]
  have hpos := eq positive
  have hneg := eq negative
  change value a = _ at hpos
  change value b = _ at hneg
  rw [joiner,qword_value]
  change value (sub (a,b)).1/denom (2*K)=_
  have hw : value a = denom (2*K) * weigh (2^r.length) f * weigh (2^r.length) g + value b := by rw [hpos,hneg]; exact he
  rw [sub_val_le _ _ (by omega),hw,Nat.add_sub_cancel,Nat.mul_assoc,Nat.mul_div_cancel_left _ denom_pos]

-- Input described by a pair of words. Calls use equal operand widths.
abbrev IW := Word × Word

def recQuery (K : ℕ) [NeZero K] (x : IW) : List IW :=
  let t := piece K (ruler x.1)
  List.ofFn fun i : Fin (2*K) => (tiny K i.val (t,x.1), tiny K i.val (t,x.2))

@[fun_prop] theorem easy_recQuery {X : Type*} [Codec X] {f : X → IW} (h : Easy f) :
    Easy (fun i => recQuery K (f i)) := by
  unfold recQuery
  apply easy_ofFn (n:=2*K)
  intro j
  apply Easy.pair <;> apply easy_tiny _ _ <;>
    apply Easy.pair (easy_piece (K:=K) _) <;> fun_prop

private theorem get_tiny (x : IW) (i : Fin (2*K)) :
    (recQuery K x)[i.val]'(by simp [recQuery]) =
    (tiny K i.val (piece K (ruler x.1),x.1),tiny K i.val (piece K (ruler x.1),x.2)) := by simp [recQuery]

theorem eqSize_queries (x : IW) :
    ∀ v∈recQuery K x, v.1.length = v.2.length := by
  simp only [recQuery, List.mem_ofFn]
  intro _ ⟨i,e⟩
  subst_vars
  simp [tiny_length]

theorem rec_bound (x : IW) :
    ∀ v∈recQuery K x, v.1.length*K < x.1.length + K + allowance K*K := by
  intro _ hu
  simp only [recQuery, List.mem_ofFn] at hu
  obtain ⟨i,e⟩ := hu
  subst_vars
  rw [tiny_length, Nat.add_mul]
  have hp := (piece_bounds (K:=K) (ruler x.1)).2
  rw [ruler_length] at hp
  omega

def reply (x : IW) : Word :=
  short (x.1.length+x.2.length) (value x.1*value x.2)

@[simp] theorem reply_val (x : IW) :
    value (reply x)=value x.1*value x.2 := by
  simp only [reply,value_short]
  apply Nat.mod_eq_of_lt
  rw [pow_add]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (value_lt _).le (value_lt _) (Nat.zero_le _) (by positivity)

@[simp] theorem reply_len (x) : (reply x).length=x.1.length+x.2.length := short_length _ _

noncomputable def useChildren (K : ℕ) [NeZero K] (i : List Word × IW) : Word :=
  resize (ruler i.2.1 ++ ruler i.2.2, joiner K (i.1,piece K (ruler i.2.1)))

@[fun_prop]
theorem easy_use {X : Type*} [Codec X] {f : X → List Word × IW} (h : Easy f) :
    Easy (fun i => useChildren K (f i)) := by
  unfold useChildren
  apply easy_resize
  apply Easy.pair
  · fun_prop
  apply easy_joiner K
  apply Easy.pair h.fstCompose
  apply easy_piece (K:=K)
  fun_prop

theorem kids_work (x : IW) (h : x.1.length=x.2.length) :
    useChildren K ((recQuery K x).map reply,x) = reply x := by
  let r := piece K (ruler x.1)
  let f (w : Word) (i : Fin K) := value (chunk i.val (r,w))
  let Q (w : Word) (i : Fin (2*K)) := tiny K i.val (r,w)
  have he : (recQuery K x).map reply = List.ofFn (fun i => reply (Q x.1 i,Q x.2 i)) :=
    List.map_ofFn ..
  have hv := joiner_spec (f x.1) (f x.2) r _ (fun i : Fin (2*K) => show value (reply (Q x.1 i,Q x.2 i))=_ from by
    simp [Q,tiny_exact i.isLt,f])
  have hw := (piece_bounds (K:=K) (ruler x.1)).1
  rw [ruler_length] at hw
  change x.1.length ≤ r.length*K at hw
  dsimp only [f] at hv
  rw [chunks hw,chunks (x:=x.2) (by rwa [← h])] at hv
  have ht : ruler x.1 ++ ruler x.2 = tally (x.1.length+x.2.length) := by
    have e (l : Tally) : l=tally l.length := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        rw [List.length_cons,tally_succ]; cases a; exact congrArg (() :: ·) ih
    simpa only [List.length_append,ruler_length] using e (ruler x.1++ruler x.2)
  apply word_inject
  · simp only [useChildren,ht,reply_len]; exact sized_length _ _
  unfold useChildren
  dsimp only
  rw [ht,← sized,sized_low,he,hv]
  simp only [reply,value_short]

end Toom

end IntegerMultiplication
end Computability
end OAI
