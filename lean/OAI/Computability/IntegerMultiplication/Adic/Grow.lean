import OAI.Computability.IntegerMultiplication.Adic.Affine
import OAI.Computability.IntegerMultiplication.Code.Fold

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Strip Strip.Dims IntegerMultiplication.Port Code Code.Task
variable {p : ℕ}
def shoots (p : ℕ) (v : Tally) : List (Raw p) :=
  (layout (field p v.length)).tab most

def stretch (l : List (Fin p)) (x : List (Raw p)) :=
  (l.map fun d => x.map fun i => d::i).flatten

theorem easy_expand (l : List (Fin p)) :
    Easy (fun (x : List (Raw p)) => stretch l x) := by
  induction l with
  | nil => exact Easy.const _
  | cons i l ih =>
    simp only [stretch,List.map_cons,List.flatten_cons]
    change Easy (fun x : List (Raw p) => x.map (fun j => i::j) ++ stretch l x)
    fun_prop -- may fail stretch folded

@[simp]
theorem boots (p : ℕ) : shoots p []=[[]] := rfl
theorem shoots_cons (p : ℕ) (h : Unit) (v : Tally) :
    shoots p (h::v) = stretch (List.finRange p) (shoots p v) := by
  unfold shoots
  change (layout (p::field p v.length)).tab (@most p (v.length+1)) = _
  refine (tab_cons (a:=p) (s:=field p v.length)
    (f:=fun x : Pin (p :: field p v.length) => most (p:=p) (l:=v.length+1) x)).trans ?_
  unfold stretch Series.tab
  congr 1
  simp [Series.natural,Series.fixed]
  intros; rfl

@[simp] theorem shoots_length (p) (v) : (shoots p v).length=p^v.length := by
  simp only [shoots,Series.card,Series.total]
  exact count

-- crude size
private theorem ceiling (p : ℕ) :
    ∃ C : ℕ, ∀ d : Fin p, size d + 1 ≤ C := by
  exact ⟨∑ i : Fin p, (size i+1),fun d => Finset.single_le_sum (f:=fun i : Fin p => size i+1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)⟩
theorem raw_size (p C : ℕ) (i : ∀ d : Fin p, size d + 1 ≤ C) (x : Raw p) :
    size x ≤ C*x.length+1 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    have := i b
    simp only [size_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
theorem tally_bound (p C : ℕ) (i : ∀ d : Fin p,size d + 1 ≤ C) (v : Tally) :
    size (shoots p v) ≤ (C*v.length+2)*p^v.length+1 := by
  unfold shoots
  rw [← costSum_le_length_size,Series.card, Series.total]
  rw [population, ← space, Series.total]
  rw [show Fintype.card (Pin (field p v.length))=p^v.length from count]
  have h := Code.costSum_le (t:=size) (u:=fun _ => C*v.length+1)
    (s:=shoots p v) (by intro x hx
                        rcases (Series.elements ..).mp hx with ⟨w,rfl⟩
                        simpa using raw_size p C i (most w))
  have e (l : List (Raw p)) : costSum (fun (_:Raw p) => C*v.length+1) l = (C*v.length+1)*l.length := by
    induction l with
    | nil => simp
    | cons y l ih => simp [ih,Nat.mul_add,add_comm]
  rw [e,shoots_length,Nat.add_mul,Nat.one_mul] at h
  change p^v.length+costSum size (shoots p v)+_≤_
  rw [Nat.add_mul]
  omega

/-- Time proportional to #addresses times unary width. -/
theorem generate (p : ℕ) (hp : 2 ≤ p) :
    Computes (fun (v:Tally) => (v.length+1)*p^v.length) (shoots p) := by
  obtain ⟨M,m⟩ := ceiling p
  have hbody := Code.Task.foldRight (X:=Unit) (D:=fun (_:Tally) (_:Unit) => True) (fun _ _ _ _ => trivial)
    (b:=fun _ => 0) (p:= fun _ => send) (f:=fun l _ => send (shoots p l))
    (seed:=fun _ => send (shoots p [])) Code.Task.self
    (a:=fun _ l _ => (M*l.length+2)*p^l.length+1)
    (by
      let X := {s:Unit × Tally × Unit // True}
      have e := Code.Task.on (Easy.snd.compose (easy_expand (List.finRange p)))
        (fun s : X => (s.val.1, shoots p s.val.2.1))
      -- use conform then bound
      simp_rw [shoots_cons]
      refine (e.bound (b':=fun s:X => (M*s.val.2.1.length+2)*p^s.val.2.1.length+1) 4 (fun i => ?_)).conform (by simp) (by simp) (by simp)
      simp only [size_prod, show ∀ x:Unit,size x=1 from fun _ => rfl]
      have := tally_bound p M m i.val.2.1
      omega)
  have u := (Task.supply (send (shoots p [])) (send (X:=Tally))).compose
    (Task.exchange (fun _ => send (shoots p [])) send)
  have v := hbody.on (fun x : Tally => ⟨(x,()),by simp⟩)
  simp_rw [forest_send] at v
  refine (u.compose v).bound (2*M+30) (fun x => ?_)
  have s : (send (shoots p [])).count=3 := rfl
  have z (k : Tally) :
      foldCost (fun (d:Unit) (l:Tally) => ((M*l.length+2)*p^l.length+1)+(send d).count) k ≤
        (2*M+14)*(k.length+1)*p^k.length := by
    induction k with
    | nil => simp
             change 1≤_
             omega
    | cons y g ih =>
      rw [foldCost,List.length_cons,pow_succ]
      have e : (2*M+14)*(g.length+1)*(p^g.length)*2 ≤
          (2*M+14)*(g.length+1+1)*(p^g.length*p) := by
        rw [← mul_assoc] -- on RHS
        gcongr; omega
      have h : (M*g.length+2)*p^g.length+3 ≤
          (2*M+14)*(g.length+1)*(p^g.length) := by
        have hx := Nat.one_le_pow g.length p (by omega)
        have hn := Nat.mul_le_mul_right (p^g.length)
          (by
            rw [Nat.add_mul, Nat.mul_add (2*M), Nat.mul_one]
            have hx : 2*M*g.length=2*(M*g.length) := by ring
            omega : M*g.length+2+3 ≤ (2*M+14)*(g.length+1))
        rw [Nat.add_mul (M*g.length+2)] at hn
        omega
      change ((M*g.length+2)*p^g.length+1)+1+1+_ ≤ _
      omega
  simp only [s,Nat.zero_add, show (send x).count=size x from rfl, size_tally]
  have h := z x
  change 3+(2*x.length+1)+foldCost (fun (d:Unit) (l:Tally) => ((M*l.length+2)*p^l.length+1)+(send d).count) x+1 ≤ _
  -- include x.length additive, multiplied bound slack
  have hp0 := Nat.one_le_pow x.length p (by omega)
  have hh := Nat.le_mul_of_pos_right (x.length+1) (by omega : 0<p^x.length)
  have : (2*M+30)*((x.length+1)*p^x.length+1)=
      (2*M+14)*(x.length+1)*(p^x.length)+16*((x.length+1)*p^x.length)+(2*M+30) := by ring
  omega

end Adic

end IntegerMultiplication
end Computability
end OAI
