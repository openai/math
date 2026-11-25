import OAI.Hierarchy.DescentHaloWalkRAM

namespace OAI
/-! # Reverse directed short paths in a reciprocal measured adjacency -/
namespace Hierarchy.DescentHaloWalkRAM
noncomputable section
variable {H D : ℕ} (R : Fin H→Fin D→Option (Fin H))

def runDigits : List (Fin (D+1))→Option (Fin H)→Option (Fin H)
  | [],u=>u
  | d::ds,u=>runDigits ds (step R u d)

private theorem no_path (ds : List (Fin (D+1))) : runDigits R ds none=none :=by
  induction ds with
  | nil=>rfl
  | cons i is ih=>simp [runDigits,step,ih]

private theorem append_path (ds es : List (Fin (D+1))) (u : Option (Fin H)) :
    runDigits R (ds++es) u=runDigits R es (runDigits R ds u) :=by
  induction ds generalizing u with | nil=>rfl | cons d ds ih=>exact ih _

private theorem digits_at (v : Fin H) (p : Path D) (t : ℕ) (ht : t≤4) :
    runDigits R (List.ofFn (fun j : Fin t=>p (j.castLE ht))) (some v)=walk R v p t :=by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [List.ofFn_succ_last,append_path]
    have prefixEq : (fun j : Fin t=>p (j.castSucc.castLE ht))=fun j=>p (j.castLE (by omega)):=rfl
    rw [prefixEq,ih (by omega)]
    simp [runDigits,walk,show t<4 by omega]
    exact congrArg (fun j=>step R (walk R v p t) (p j)) (Fin.ext (by simp))

private theorem reverse_digits (reciprocal : ∀v u i,R v i=some u→∃j,R u j=some v) (ds : List (Fin (D+1)))
    (v u : Fin H) (hit : runDigits R ds (some v)=some u) :
    ∃es : List (Fin (D+1)),es.length=ds.length ∧ runDigits R es (some u)=some v :=by
  induction ds generalizing v with
  | nil=>exact ⟨[],rfl,(Option.some.inj hit) ▸ rfl⟩
  | cons d ds ih=>
    cases move : step R (some v) d with
    | none=>simp only [runDigits,move,no_path] at hit;contradiction
    | some t=>
      have tail : runDigits R ds (some t)=some u:=by simpa only [runDigits,move] using hit
      obtain ⟨back,count,go⟩:=ih t tail
      have next : ∃s,step R (some t) s=some v:=by
        by_cases yes : d.val<D
        · have h : R v ⟨d.val,yes⟩=some t:=by simpa [step,yes] using move
          obtain ⟨j,hj⟩:=reciprocal v t _ h
          exact ⟨j.castSucc,by simpa [step,j.isLt] using hj⟩
        · have h : v=t:=Option.some.inj (by simpa [step,yes] using move)
          subst t;exact ⟨Fin.last D,by simp [step]⟩
      obtain ⟨s,atOld⟩:=next
      exact ⟨back++[s],by simp [count],by rw [append_path,go];exact atOld⟩

theorem reverse_path (reciprocal : ∀v u i,R v i=some u→∃j,R u j=some v) (p : Path D) (v u : Fin H)
    (hit : walk R v p 4=some u) : ∃q : Path D,walk R u q 4=some v :=by
  have far : runDigits R (List.ofFn p) (some v)=some u:=by
    rw [←hit];exact digits_at R v p 4 le_rfl
  obtain ⟨back,size,done⟩:=reverse_digits R reciprocal (List.ofFn p) v u far
  have size' : back.length=4:=by simpa using size
  let q : Path D:=fun i=>back.get (i.cast size'.symm)
  have same : List.ofFn q=back:=by
    rw [←back.ofFn_get];apply List.ext_getElem <;> simp [q,size']
  refine ⟨q,?_⟩;rw [←digits_at R u q 4 le_rfl]
  change runDigits R (List.ofFn q) (some u)=some v;rw [same];exact done

end
end Hierarchy.DescentHaloWalkRAM

end OAI
