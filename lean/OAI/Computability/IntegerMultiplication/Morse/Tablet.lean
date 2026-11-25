import OAI.Computability.IntegerMultiplication.Morse.Opus
import OAI.Computability.IntegerMultiplication.Scale.Stars

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Morse
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits
variable {k w t:ℕ} (p:ℕ)(q:Word)(b:ℕ→Grain w)
abbrev inflate (b:ℕ→Grain w) (n i:ℕ):=b (2^n*i)
private theorem reach_row (v:ℕ) (n:ℕ) (t:v<n) :
    (scroll p q b n)[v]'(by rwa [scroll_len])=
      rowT p q (inflate b v) (n-(v+1)) := by
  induction v generalizing b n with
  | zero=> cases n with
    | zero=> omega
    | succ r=>
      rw [show r+1-(0+1)=r by omega]
      simp only [scroll,List.getElem_cons_zero]
      congr 1
      funext z; simp [inflate]
  | succ m ih=>
    cases n with
    | zero=>omega
    | succ n=>
      have e:=ih (doubleBank b) n (by omega)
      change (scroll _ _ (doubleBank b) n)[m]'_ = _
      apply e.trans
      rw [show n+1-(m+1+1)=n-(m+1) by omega]
      congr 1
      funext z
      unfold inflate doubleBank
      rw [pow_succ]; congr 1; ring
abbrev sheet (n:ℕ)(v:Fin n):=
  rowT p q (inflate b v.val) (n-(v.val+1))
theorem alone (n:ℕ): scroll p q b n=List.ofFn (sheet p q b n):= by
  apply List.ext_getElem (by simp)
  intro i t g -- number args?
  rw [List.getElem_ofFn]; exact reach_row p q b i n (by simpa using g)
-- specialize q relation maybe supply condition q needs ≤ k but q of lastB reach. table -> Mark of function formula. rowVia
abbrev atom (k m:ℕ)(c:B) (a:ℕ): Orb:=
  (tally p,Dusk.mark (inflate b m ((Bits.value q*pin c*a)%2^(k+1))))
abbrev pebble (k m:ℕ)(v:Fin (2^k)): card₀ := (atom p q b k m 0 v.val,atom p q b k m 1 v.val)
theorem script (k m:ℕ):
    rowT p q (inflate b m) k=List.ofFn (pebble p q b k m):=
  phase_local  (pebble p q b k m)
end Morse

end IntegerMultiplication
end Computability
end OAI
