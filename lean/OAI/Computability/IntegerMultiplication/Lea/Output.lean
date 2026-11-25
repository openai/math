import OAI.Computability.IntegerMultiplication.Lea.Wintry
import OAI.Computability.IntegerMultiplication.Birch.Shell

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Lea
open Code Bits Dusk Cone Param Scale Bureau Birch Grid Strip Dune Staff Brief
variable {I:Type}(n:I→ℕ)(h:∀ i,Season (n i))
abbrev wx (n:ℕ):=Scale.F n-1
private theorem w1 (k):wx k+1=Scale.F k:= by unfold wx Scale.F; have e:=budget_p k; unfold Scale.P; omega
abbrev Layer :ℕ:=14000
variable (x:(i:I)→GrainV (n i))
abbrev ear (i:I)(j:Hint (n i)):Word:= roundedG (Code.tally (wx (n i)),Dusk.mark (x i j))
theorem layer_ok(i j): (ear n x i j).length ≤ Layer*P (n i) :=
  (range_ _ _).trans (by unfold wx Scale.W Layer Scale.F; have V:0<P (n i):=budget_p _; omega)
theorem gleaned (u:ℕ)(i j)(v:‖look (n i) (x i j)-(u:ℂ)‖<1/4):
    value (ear n x i j)=u:=
  rests _ _ _ (by rw [w1]; exact v.le)

-- width 2*n ruler disp.
abbrev OutPx (n:ℕ):=2*n
include h
omit h in
private theorem lengthT :
    Carries (token n) (cell n) (tokenP (OutPx ∘ n)):= by
  let g:=guide_city n
  have M:= (Carry.Figure.natural (r:=city n) 2).multiplied g.amount_
  -- may ≤2*ton n; actually 2n≤ton? load_above yields4n.
  apply Bureau.dispatchT _ M
  intro i
  let k:=n i
  change 2*k≤load k*P k
  have u:= Nat.mul_le_mul_right (P k) (load_above k)
  have q:=budget_times k
  unfold Scale.P at *
  nlinarith

abbrev emit (i:I): Word:= (sized (2*n i) (IntegerMultiplication.Lea.harvest Layer (List.ofFn (ear n x i),scale0 (boxes (n i)) (P (n i))))).reverse -- harvest ambiguous
abbrev spritz (i:Tally×Trigger):Word := (resize (i.1,IntegerMultiplication.Lea.harvest Layer i.2)).reverse
omit h in
theorem spritzE : Easy spritz:=
  (easy_resize (Easy.fst.pair (Easy.snd.compose (harvestE _)))).compose Easy.reverse

theorem leaf :
    Wood n (Lexi n x) (fun i=>send (emit n x i)):= by
  -- Dune.small_ requires Guild, supply sth separately via e(:close Lexi) or use # args. derive size here. parameter instead!
  have e0:close n (Lexi n x):= Dune.small_ n h x
  let p:=scoop e0
  have g:=guide_city n
  have v:= (Scale.birthday h).fraction n
  have c:Realizes (city n) (wx ∘ n):= v.minused (.fix 1)
  have w:=planT n h (wx ∘ n) (dispatch c) 4096 (fun i=> Nat.sub_le ..)
  let l i : List Dusk.Pair × List Tally:=(List.ofFn (Dusk.mark ∘ x i), List.replicate (boxes (n i)) (Code.tally (wx (n i))))
  have T₀: Wood n (Lexi n x) (send ∘ l):=(me e0).twice (p.chain w)
  let f(x:Dusk.Pair×Tally):=roundedG (x.2,x.1)
  have m:= T₀.chain (Carries.func T₀.budget (y:=l) T₀.out (lock f ([],[]) []) (easy_lock _ (Easy.exchange.compose fluent) _ _))
  have W i: lock f ([],[]) [] (l i)=List.ofFn (ear n x i):= maskLock _ _ f (mark ∘ x i) _
  simp_rw [W] at m
  have d:=tagP n
  have a:= p.chain ((planT n h _ d 1 (fun i=> Nat.le_mul_of_pos_left _ (le_refl 1))).twice d)
  let s i:=(Code.tally (2*n i),List.ofFn (ear n x i),scale0 (boxes (n i)) (P (n i)))
  have y:Wood n (Lexi n x) (send ∘ s):= (p.chain (lengthT n)).twice (m.twice a)
  exact y.chain (Carries.func y.budget y.out spritz spritzE)
end Lea

end IntegerMultiplication
end Computability
end OAI
