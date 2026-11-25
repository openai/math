import OAI.Computability.IntegerMultiplication.Adic.Roll

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Port Strip Strip.Dims Code
variable {p : ℕ} [NeZero p] (a b : Nug p)
noncomputable section
-- header pair each record : offset o first, then key x
abbrev Ins := Raw p × Raw p
def post (i : Ins (p:=p)) :=
  mark a b i.2 i.1 (ahead a b i.1 i.2)
def fetch (i : Ins (p:=p)) :=
  mark a b (ret a b i.1 i.2) i.1 i.2

@[fun_prop] theorem easy_post {G : Type} [Codec G] {q : G → Ins (p:=p)} (h : Easy q) :
    Easy (fun x => post a b (q x)) := by unfold post mark ahead; fun_prop
@[fun_prop] theorem easy_fetch {G : Type} [Codec G] {q : G → Ins (p:=p)} (h : Easy q) :
    Easy (fun x => fetch a b (q x)) := by unfold fetch mark ret; fun_prop

abbrev byword (j) (o : Raw p) : Block p j → Ins (p:=p) :=
  fun x => (o, least x)
theorem forward_post (j) (o : Raw p) (t : Tower p j) (e : Holds j o t) (x : Block p j) :
    flag a b t x=post a b (byword j o x) := by
  unfold flag post
  congr 2 -- ?
  · exact (Holds.stdRev _).single e
  apply (Holds.std _).single
  rw [arrive]; exact ahead_correct _ _ _ _ e (Holds.std x)

theorem back_post (j) (o : Raw p) (t : Tower p j) (e : Holds j o t) (x : Block p j) :
    flag a b t ((swift a b t).symm x) = fetch a b (byword j o x) := by
  rw [flag,Equiv.apply_symm_apply]
  congr 1 -- ?
  · apply (Holds.std _).single
    have eq : index p j ((swift a b t).symm x)=(roll a b t).symm (index p j x) := by
      simp only [swift,Equiv.symm_trans_apply,Equiv.apply_symm_apply,Equiv.symm_symm]
    rw [eq]; exact return_correct _ _ _ _ e (Holds.std x)
  exact (Holds.stdRev _).single e

/-- Linear-time application of nonnegative affine on completely arbitrary payload,
given offset and each address with LSD-first syntax. (Can alternatively pay for
generating the copy stripe, e.g., under fat allowance.) -/
theorem river {I : Type} (j : I→ℕ) (t : (i:I)→Tower p (j i)) (o : I→Raw p)
    (h : ∀ i,Holds (j i) (o i) (t i)) (v : (i:I)→Block p (j i)→Tree)
    {w : I→ℝ} {q : I→Tree}
    (l : Carries w q (stackRun (fun i => layout (field p (j i))) v))
    (g : Carries w q (stackRun (fun i => layout (field p (j i))) (fun i x => send (byword (j i) (o i) x)))) :
    Carries w q (stackRun (fun i => layout (field p (j i))) fun i x => v i ((swift a b (t i)).symm x)) := by
  apply classified_perm (fun x => admiral a b (t x)) _ l
  · unfold stackRun at *
    simp_rw [stripe_eq'] at *
    have e := g.chain (Carries.func g.budget g.out (List.map (post a b)) (by fun_prop))
    have C (i : I) : (flag a b (t i)) = fun x => post a b (byword (j i) (o i) x) := funext (fun _ => forward_post _ _ _ _ _ (h i) _)
    simpa [Series.map_tab,Function.comp_def,C] using e
  unfold stackRun at *
  simp_rw [Function.comp_def,stripe_eq'] at *
  have e := g.chain (Carries.func g.budget g.out (List.map (fetch a b)) (by fun_prop))
  simpa [Series.map_tab,Function.comp_def,back_post a b _ _ _ (h _)] using e

end
end Adic

end IntegerMultiplication
end Computability
end OAI
