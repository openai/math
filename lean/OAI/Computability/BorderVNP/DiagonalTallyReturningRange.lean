import OAI.Computability.BorderVNP.DiagonalTallyScatterGuards

/-! # Overflow rejection implies natural bounds on each actually returned operand stream -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyScatter

open VPVNP.BurstRAM RoutingISA
open private recordsAt_congr from OAI.Computability.BorderVNP.DiagonalTallyScatterLoop

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Every intermediate addition in a returning scatter passed its actual overflow
check. Consequently even a guessed stream that has not been authenticated elsewhere
has a genuinely bounded natural subtotal at every address whenever the loop returns. -/
theorem loop_return_guards (rs : List (ℕ × ℕ)) {s t : Bank w} {m mt : Memory w} {es}
    {base dim p stop : ℕ} (loaded : Loaded s base dim p stop)
    (span : p+2*rs.length=stop) (separate : Separate base dim p stop) (records : RecordsAt m p rs)
    (run : Runs pub mac (.whileLt 50 51 body) s m es t mt) :
    (∀ r ∈ rs, r.1<dim) ∧ ∀ a, (m a).val+incrementAt base a rs < 2^w := by
  induction rs generalizing s m p es with
  | nil => simp [incrementAt]
  | cons r rs ih =>
    rcases r with ⟨i,v⟩
    obtain ⟨coord,inc,tail⟩ := records
    obtain ⟨hb,hd,hp,he,one⟩ := loaded
    have hs : stop < 2^w := he ▸ (s 51).isLt
    have more : s 50 < s 51 := by
      change (s 50).val < (s 51).val
      simp only [List.length_cons] at span
      omega
    cases run with
    | atom bad _ _ => cases bad
    | whileDone done => exact (done more).elim
    | whileStep _ first rest =>
      have guards := body_guards first
      have ptr : (s 50+s 63).val=p+1 := by
        rw [Fin.val_add,hp,one,Nat.mod_eq_of_lt]
        simp only [List.length_cons] at span
        omega
      have bounded : base+i < 2^w := by simpa only [hb,hp,coord] using guards.2.2.1
      have addr : (s 48 + m (s 50).val).val=base+i := by rw [Fin.val_add,hp,hb,coord,Nat.mod_eq_of_lt bounded]
      have noWrap : (m (base+i)).val+v < 2^w := by simpa only [ptr,addr,inc] using guards.2.2.2
      have hi : i<dim := by
        have test : (m (s 50).val).val < (s 49).val := guards.2.1
        rwa [hp,hd,coord] at test
      have len : p+2+2*rs.length=stop := by simp only [List.length_cons] at span; omega
      obtain ⟨_,u,step,next,_,_⟩ := body_runs pub mac s m ⟨hb,hd,hp,he,one⟩ (by omega) hi bounded noWrap coord inc
      obtain ⟨_,eq,bank⟩ := first.unique_of_deterministic (by decide) step
      rw [eq,bank] at rest
      let m' := Function.update m (base+i) (m (base+i)+m (p+1))
      have intact : RecordsAt m' (p+2) rs := recordsAt_congr m m' rs _ tail (fun a lo top => by
        have off := separate i hi
        have other : a≠base+i := by omega
        simp [m',other])
      have continued : Separate base dim (p+2) stop := by
        intro j hj
        have off := separate j hj
        omega
      obtain ⟨remaining,total⟩ := ih next len continued intact rest
      refine ⟨?_,?_⟩
      · intro r mem
        rcases List.mem_cons.mp mem with rfl | later
        · exact hi
        · exact remaining r later
      intro a
      by_cases same : a=base+i
      · subst a
        have add : (m (base+i)+m (p+1)).val=(m (base+i)).val+v := by
          rw [Fin.val_add,inc,Nat.mod_eq_of_lt noWrap]
        simpa [m',incrementAt,add,Nat.add_assoc] using total (base+i)
      · simpa [m',incrementAt,same,Ne.symm same] using total a

/-- Returning through the whole scatter includes a returning guarded loop. -/
theorem scatter_return_guards (rs : List (ℕ × ℕ)) {s t : Bank w} {m mt : Memory w} {es}
    {base dim p stop : ℕ} (loaded : Loaded s base dim p stop)
    (span : p+2*rs.length=stop) (separate : Separate base dim p stop) (records : RecordsAt m p rs)
    (run : Runs pub mac scatter s m es t mt) :
    (∀ r ∈ rs, r.1<dim) ∧ ∀ a, (m a).val+incrementAt base a rs < 2^w := by
  cases run with
  | atom bad _ _ => cases bad
  | seq first _ => exact loop_return_guards rs loaded span separate records first

end DiagonalTallyScatter

end BorderVNP
end Computability
end OAI
