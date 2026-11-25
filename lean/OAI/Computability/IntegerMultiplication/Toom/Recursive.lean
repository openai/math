import OAI.Computability.IntegerMultiplication.Toom.Use
import OAI.Computability.IntegerMultiplication.Code.Static

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Toom
open Bits Code

/- Number of parts, height scale (cutoff fixedK). -/
variable (fixedK : ℕ) [NeZero fixedK]

noncomputable def cutoff (n : ℕ) : ℕ := n*(1+allowance n)

/-- All scheduling budgets for this lemma use the ghost class: inputs ≤2^j.
This avoids any continuity assumptions about running time. The ghost is never
used by the computation. -/
structure Job where
  j : ℕ
  x : IW
  sameSize : x.1.length=x.2.length
  bound : x.1.length≤2^j

class Accord (n : ℕ) : Prop where
   k : n=2^128

variable [hk : Accord fixedK]
include hk
omit [NeZero fixedK] in
theorem k_eq : fixedK = 2*2^127 := hk.k.trans (pow_succ' 2 127)

omit [NeZero fixedK] in
theorem level (z : Job) (h : (cutoff fixedK) < z.x.1.length) : 128 ≤ z.j := by
  by_contra! e
  have hh : 2^z.j < fixedK := hk.k.symm ▸ pow_right_strictMono₀ (by decide) e
  have hz : fixedK ≤ (cutoff fixedK) := Nat.le_mul_of_pos_right fixedK (by omega) -- inspect
  have := z.bound
  omega

private theorem shrinks (z : Job) (h : (cutoff fixedK) < z.x.1.length) {v}
    (hv : v ∈ recQuery fixedK z.x) : v.1.length≤2^(z.j-127) := by
  have he := rec_bound z.x v hv
  have hz := z.bound
  have hl := level fixedK z h
  have hc : fixedK + allowance fixedK * fixedK = (cutoff fixedK) := by unfold cutoff; ring
  have htwo : 2*(2^z.j) = 2^(z.j-127)*fixedK := by
    rw [k_eq fixedK, show (2:ℕ)^ (z.j-127)*(2*2^127) = 2*(2^(z.j-127)*2^127) by ring,← pow_add,Nat.sub_add_cancel (by omega)]
  have := lt_of_lt_of_le h hz
  have hlength : v.1.length * fixedK ≤ 2^(z.j-127)*fixedK := by omega
  have hk : 0<fixedK := Nat.pos_of_ne_zero (NeZero.ne fixedK)
  exact Nat.le_of_mul_le_mul_right hlength hk

noncomputable def sons (fixedK : ℕ) [NeZero fixedK] [Accord fixedK] (z : Job) : List Job :=
  if h : (cutoff fixedK) < z.x.1.length then
    ((recQuery fixedK z.x).attach).map
      fun v => { j := z.j-127, x:=v.val, sameSize := eqSize_queries z.x v.val v.property, bound := shrinks fixedK z h v.property }
  else []

@[simp]
theorem sons_arguments (z : Job) : (sons fixedK z).map Job.x =
    if (cutoff fixedK) < z.x.1.length then recQuery fixedK z.x else [] := by
  simp only [sons]
  split <;> simp [* ,List.map_map,Function.comp_def]
  exact List.unattach_attach

theorem sons_count (z : Job) : (sons fixedK z).length =
    if (cutoff fixedK) < z.x.1.length then 2*fixedK else 0 := by
  have h := congrArg List.length (sons_arguments fixedK z)
  simp only [List.length_map] at h
  split <;> rename_i hp <;> simp_all [-sons_arguments,recQuery]

theorem sons_height {z v : Job} (hv : v ∈ sons fixedK z) : v.j=z.j-127 := by
  unfold sons at hv
  split at hv
  · obtain ⟨_,_,e⟩ := List.mem_map.mp hv
    subst_vars; rfl
  · simp at hv

omit hk in
-- Cutoff guard, uniform in the supplied data. C is a fixed constant.
private theorem dropEasy {X : Type*} [Codec X] (c : ℕ) :
    Easy (fun l : List X => l.drop c) := by
  have hh := easy_cut (g := fun i : List X => (tally c,i))
    (show Easy (fun i : List X => (tally c,i)) by fun_prop)
  simpa [cutLists] using hh.sndCompose

omit hk in
private theorem emptyEasy {X : Type*} [Codec X] :
    Easy (fun i : List X => i.isEmpty) := by
  convert Easy.listCase (X:=X) true (f:=fun _ => false) (Easy.const false)
  rename_i x; cases x <;> rfl

noncomputable def needed (fixedK : ℕ) [NeZero fixedK] (x : IW) :=
  bif (x.1.drop (cutoff fixedK)).isEmpty then [] else recQuery fixedK x

theorem needed_eq (z) : needed fixedK z.x = (sons fixedK z).map Job.x := by
  rw [sons_arguments]
  unfold needed
  split
  · next e =>
    rw [show (z.x.1.drop (cutoff fixedK)).isEmpty=false from List.isEmpty_eq_false_iff.mpr (fun h => by
      have heq := congrArg List.length h
      simp only [List.length_drop,List.length_nil] at heq
      omega)]
    rfl
  · next e =>
    simp [List.drop_eq_nil_of_le (show z.x.1.length ≤ cutoff fixedK from by omega)]

omit hk in
protected theorem needed_easy : Easy (needed fixedK) := by
  let h : IW → Bool := fun x : IW => (x.1.drop (cutoff fixedK)).isEmpty
  have hh : Easy h := Easy.fst.compose ((dropEasy ..).compose emptyEasy)
  exact (hh.pair Easy.identity).compose
    (Easy.ifst (easy_recQuery (K:=fixedK) Easy.identity) (Easy.const []))

private def q (z : Job) := send z.x
private def w (z : Job) := send (reply z.x)
private def gc (z : Job) := size z.x
private noncomputable def mc (fixedK : ℕ) [NeZero fixedK] [Accord fixedK] (z : Job) : ℕ :=
  (Tree.fork (Task.forest w (sons fixedK z)) (q z)).count -- noncomputable?

theorem generate :
    Task gc q fun i => .fork (Task.forest q (sons fixedK i)) (q i) := by
  have h := Task.on ((IntegerMultiplication.Toom.needed_easy fixedK).pair Easy.identity) Job.x
  refine h.conform (fun i => rfl) (fun i => rfl) fun i => ?_
  rw [send_prod]; dsimp only
  rw [needed_eq fixedK i]
  rw [← Task.forest_send,Task.forest_map]; rfl

omit hk in
private theorem identify {l s : Word} (e : send l=send s) : l=s := by
  induction l generalizing s with
  | nil => cases s <;> simp_all
  | cons x l ih =>
    cases s with
    | nil => simp_all
    | cons v s =>
      simp only [send_cons,Tree.fork.injEq] at e
      have hh := FiniteState.identify e.1
      rw [hh, ih e.2]

theorem process :
    Task (mc fixedK) (fun i => .fork (Task.forest w (sons fixedK i)) (q i)) w := by
  apply Task.byForest
  · apply Task.restricted _ _ _ (4*(cutoff fixedK)+3) (4*(cutoff fixedK)+1)
    · intro x
      have h : ¬(cutoff fixedK)<x.val.x.1.length := by
        intro hp
        have hh := sons_count fixedK x.val
        rw [x.property,List.length_nil,ite_eq_left hp] at hh
        have hf : 0 < fixedK := Nat.pos_of_ne_zero (NeZero.ne fixedK)
        omega
      dsimp only [q]
      rw [← size,size_prod,size_word,size_word]
      have := x.val.sameSize
      omega
    · intro x
      rw [w,← size,size_word,reply_len]
      have hs := x.val.sameSize
      have hf : 0 < fixedK := Nat.pos_of_ne_zero (NeZero.ne fixedK)
      have hh := sons_count fixedK x.val
      rw [x.property,List.length_nil] at hh
      split at hh <;> omega
    · intro a b he
      apply congrArg (fun p : IW => send (reply p))
      exact Prod.ext (identify (Tree.fork.inj he).1) (identify (Tree.fork.inj he).2)
  · -- nonempty: use ordinary child outputs in their list order
    have hw := Task.on (easy_use (K:=fixedK) Easy.identity)
      (fun i : {i // sons fixedK i≠[]} => ((sons fixedK i.val).map (reply ∘ Job.x),i.val.x))
    refine hw.conform (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · dsimp only [mc,q,w]
      rw [size_prod]
      dsimp only
      unfold size
      rw [Tree.count, ← Task.forest_send (List.map _ _),Task.forest_map]
      rfl
    · simp only [send_prod]; dsimp only [q,w]
      rw [← Task.forest_send (List.map _ _),Task.forest_map]; rfl
    · dsimp only
      rw [← List.map_map, sons_arguments]
      split
      · exact congrArg send (kids_work _ i.val.sameSize)
      · next h => have := i.property; simp [sons,h] at this


def budget (j) := (2:ℕ)^j*8^(j/127)

omit hk in
theorem budget_ge (j) : 2^j ≤ budget j := by
  apply Nat.le_mul_of_pos_right
  exact Nat.pow_pos (by decide)

omit [NeZero fixedK] in
theorem budget_down (z : ℕ) (e : 127≤z) :
    2*(2*fixedK)*budget (z-127)=budget z := by
  unfold budget
  rw [k_eq fixedK]
  have h : z - 127 + 127 = z := by omega
  have hdiv : z/127=(z-127)/127+1 := by omega
  conv_rhs =>
    arg 1
    rw [← h,pow_add]
  rw [hdiv,pow_succ]
  ring

-- Diminishing-returns proof: exact coefficient on recursive calls. Include enough
-- fixed linear volume for both side and child packet processing.
theorem multiplier_equal :
    Task (fun i : Job => budget i.j) q w := by
  let D := 100*(fixedK+1)
  refine (Task.children (a := fun i : Job => D * budget i.j) (sons fixedK) q
    (generate fixedK) (process fixedK) ?_).bound D (fun x => ?_)
  · intro z
    have hgc (i : Job) : gc i ≤ 7*budget i.j := by
      change size i.x ≤ _
      simp only [size_prod,size_word,i.sameSize]
      have hi := i.sameSize
      have hh := budget_ge i.j -- implicit fixedK?
      have hz := i.bound
      have ht := Nat.pow_pos (n := i.j) (by decide : 0 < (2:ℕ))
      omega
    have hw (i : Job) : (w i).count ≤ 7*budget i.j := by
      change size (reply i.x) ≤ _
      rw [size_word,reply_len]
      have hs := i.sameSize
      have hh := budget_ge i.j
      have hz := i.bound
      have ht := Nat.pow_pos (n:=i.j) (by decide : 0 < (2:ℕ))
      omega
    have he := budget_ge z.j
    have hn := sons_count fixedK z
    have hbb : budget z.j ≥ 1 :=
      (show 1 ≤ (2:ℕ)^z.j from Nat.pow_pos (by decide)).trans he
    change gc z + mc fixedK z + _ + _ + _ ≤ _
    by_cases ha : cutoff fixedK < z.x.1.length
    · rw [ite_eq_left ha] at hn
      have hlevel := level fixedK z ha
      have hvol := budget_down fixedK z.j (by omega)
      have eqi (g : ℕ → ℕ) :
          costSum (fun i => g (budget i.j)) (sons fixedK z) = 2*fixedK*g (budget (z.j-127)) := by
        unfold costSum
        have he : List.map (fun i => g (budget i.j)) (sons fixedK z) =
          List.map (fun _ => g (budget (z.j-127))) (sons fixedK z) :=
          List.map_congr_left (fun i e => by rw [sons_height fixedK e])
        rw [he,List.map_const',List.sum_replicate,hn,smul_eq_mul]
      have hu : costSum (fun i => (w i).count) (sons fixedK z) ≤ 2*fixedK*(7*budget (z.j-127)) :=
        (costSum_le (fun i _ => hw i)).trans (eqi (fun n => 7*n)).le
      have hr := hgc z
      dsimp only [mc]
      rw [Tree.count,Task.forest_count,hn, show (q z).count= gc z from rfl,eqi (fun n => D*n)]
      have hh := mul_le_mul_of_nonneg_left hbb (show 0≤fixedK from Nat.zero_le _)
      simp only [D]
      nlinarith [Nat.zero_le (budget (z.j-127)), Nat.zero_le (fixedK), congrArg (fixedK * ·) hvol]
    · have hz : sons fixedK z=[] := by simp [sons,ha]
      dsimp only [mc]
      rw [hz]
      have hr := hgc z
      simp only [Task.forest_nil,costSum_nil,Tree.count,D, show (q z).count=gc z from rfl]
      nlinarith
  rw [Nat.mul_add]
  unfold D at *
  omega

/-- The short multiplier accepts any equal length coding. j (analysis height, NOT an
instruction or a descriptor) can be picked in any application. No computable cutoff
size required by API; all cutoffs and tables compiled in. -/
theorem equal_mul :
    Task (fun i : {v : IW × ℕ // v.1.1.length=v.1.2.length ∧ v.1.1.length≤2^v.2} =>
        budget i.val.2)
      (fun i => send i.val.1)
      (fun i => send (reply i.val.1)) := by
  -- specialize once we prove without fixedK args as corollary later
  exact (multiplier_equal fixedK).on fun i : {v : IW × ℕ // v.1.1.length=v.1.2.length ∧ v.1.1.length≤2^v.2} => ⟨i.val.2,i.val.1,i.property.1,i.property.2⟩

end Toom

end IntegerMultiplication
end Computability
end OAI
