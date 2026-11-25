import OAI.Computability.IntegerMultiplication.Bits.Add
import OAI.Computability.IntegerMultiplication.Code.Children
import OAI.Computability.IntegerMultiplication.Code.Iter

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- Count a unary tape to minimal binary in linear time. Avoid assumed counters at startup. -/
namespace Carry
open Code Bits

def parity (n:ℕ):Bool:= decide (n%2=1)

theorem parity_d (n:ℕ) : digit (parity n)=n%2 := by
  unfold parity; have z := Nat.mod_lt n (by decide : 0<2)
  by_cases a:n%2=1 <;> simp [a]; omega

def flop (_:Unit) (b:Bool) : Bool × List Unit :=
  bif b then (false,[()]) else (true,[])
def half (t:Tally) : Tally × Bool :=
  machine flop (t,false)

@[fun_prop] theorem halfCost : Easy half := by unfold half; fun_prop
theorem half_v (t:Tally) :
    half t=(tally (t.length/2),parity t.length) := by
  rw [← Code.recover_tally t] -- rewrites everywhere?
  suffices e : ∀ n, half (tally n)=(tally (n/2),parity n) from by rw [e]; simp [tally_length]
  intro n
  induction n using Nat.twoStepInduction with
  | zero=>rfl
  | one=>rfl
  | more n ih _ =>
    rw [tally_succ,tally_succ,half,machine_cons]
    simp only [flop,Bool.cond_false]
    rw [machine_cons]
    simp only [flop, Bool.cond_true]
    unfold half at ih; rw [ih]
    dsimp only
    rw [show (n+2)/2=n/2+1 by omega]
    unfold parity; rw [show (n+2)%2=n%2 by omega]; rfl -- cons appended order

/-- Extensional minimal bits -/
def born (n:ℕ) : Word :=
  if h:n=0 then []
  else parity n::born (n/2)
termination_by n
decreasing_by have := Nat.div_lt_self (by omega : 0<n) (by decide : 1<2); omega
attribute [local simp] half_v
@[simp] theorem born0 : born 0=[] := by rw [born]; rfl
theorem birth {n} (h:0<n) : born n=parity n::born (n/2) := by rw [born,dite_eq_right (by omega)]
theorem birthValue (n) : value (born n)=n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl|e
    · simp
    rw [birth e,value_cons,parity_d,ih (n/2) (Nat.div_lt_self e (by decide))]
    omega
theorem birthLen (n) : (born n).length≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih => rcases Nat.eq_zero_or_pos n with rfl|e
              · simp
              rw [birth e,List.length_cons]
              have u := ih (n/2) (Nat.div_lt_self e (by decide))
              omega

theorem condition {X:Type*} [Codec X] {Y} [Codec Y] (p : X→Bool) (f g : X→Y)
    (h:Easy p) (q:Easy f) (r:Easy g) : Easy (fun x=> bif p x then f x else g x) :=
  (h.pair (r.pair q)).compose ((Easy.ifst Easy.fst Easy.snd))

def brood (i : Tally) : List Tally :=
  bif i.isEmpty then [] else [(half i).1]
def initial (p : Tally) := (brood p,(half p).2)
def end_ (x : List Word × Bool) : Word :=
  bif x.1.isEmpty then [] else x.2:: (x.1.headD [])
theorem vacant (X : Type*) [Codec X] : Easy (fun i : List X=> i.isEmpty) := by
  have h (x : List X) : x.isEmpty=List.casesOn (motive:=fun _=>Bool) x true (fun _ _=> false) := by cases x <;> rfl
  simp only [h]; apply Easy.listCase true (f:=fun (_ : X × List X)=>false) (by fun_prop)
  -- by defeq?
@[fun_prop] private theorem start_ : Easy initial := by
  unfold initial
  apply Easy.pair _ halfCost.sndCompose
  unfold brood
  exact condition _ _ _ (vacant _) (Easy.const _) (by fun_prop)
@[fun_prop] private theorem returns : Easy end_ := by
  unfold end_
  apply condition
  · exact Easy.fst.compose (vacant _)
  · fun_prop
  have v : Easy (fun i:List Word × Bool=>i.1.headD []) := Easy.fst.compose (Iter.leader ([]:Word))
  exact (Easy.snd.pair v).compose Easy.cons

/-- ordinary constructor recovery includes linear scanning costs for the result of a child. -/
@[fun_prop] theorem easy_chart : Easy (fun s:Tally=>born s.length) := by
  let z s := send (X:=Word) (born (s:Tally).length)
  let v (s:Tally) := send (X:=Bool) (half s).2
  have j (s : Tally) : (Task.forest z (brood s)).count ≤ size s+4 := by
    let n := s.length
    cases h:s.isEmpty with
    | false=>
      simp only [brood,h,Bool.cond_false,Task.forest_cons,Task.forest_nil,Tree.count]
      change size (born (half s).1.length)+1+1 ≤ _
      rw [size_word,half_v,size_tally]
      dsimp only; rw [tally_length]
      have t := birthLen (s.length/2); omega
    | true=> simp [brood,h,Tree.count]
  let q (s:Tally) := size s+4
  have g := Task.children (p:=send) (q:=z) (a:=fun s=> 32*(size s)) (g:=size)
    (h:=fun s=> q s+2) brood v
    (start_.conform (fun _=>rfl) (fun _=>rfl) (fun x=> by simp only [initial,send_prod,v,Task.forest_send]))
    (show Task _ _ _ from ?_)
    (fun s=> by
      unfold q
      specialize j s
      cases h:s.isEmpty with
      | true=>
        rw [show brood s=[] by simp [brood,h],costSum_nil]
        simp only [Task.forest_nil,Tree.count]
        have v := size_pos s; omega
      | false=>
        have v : 0<s.length := by
          cases s <;> simp at *
        simp only [brood,h,Bool.cond_false,costSum_cons,costSum_nil,half_v] at j ⊢
        simp_rw [size_tally, tally_length] at *
        omega)
  · exact g.bound 33 (by intro x; omega) -- bound C*(size+1)
  -- map to end_, matches
  let Q (x:Tally) := ((brood x).map fun s=> born s.length,(half x).2)
  have e := (returns).on Q
  have t (x:Tally) : Task.forest z (brood x) = send (Q x).1 := by
    unfold Q z; dsimp only; rw [← Task.forest_send, Task.forest_map]
  refine (e.conform (fun x=>rfl) (fun x=> by rw [t]; exact Code.send_prod ..) ?_).mono ?_
  · intro s
    cases s with
    | nil=> simp [Q,z,brood,end_,List.isEmpty]
    | cons b s=> simp [Q,z,brood,end_,List.isEmpty,birth (Nat.zero_lt_succ _)]
  intro x
  rw [size_prod,show size (Q x).2=1 from rfl]
  have u := j x
  rw [t] at u; change size (Q x).1≤ _ at u
  unfold q; omega
end Carry

end IntegerMultiplication
end Computability
end OAI
