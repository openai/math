import OAI.Computability.IntegerMultiplication.Wave.Frame

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dune
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau Atoll Wave

def smother (x:Tally × List (List Bool)):List (List Bool) :=
  let v:= cutLists x
  v.1 ++ v.2.map (List.map (fun _=>false))
@[fun_prop] theorem smotherE:Easy smother:=
  (easy_cut Easy.identity).compose ((Easy.fst.pair (Easy.snd.compose (Easy.const false).mapping.mapping)).compose Easy.append)
private theorem memberN (x:Tally) (n:ℕ)(z:Fin n→List Bool):
    smother (x,List.ofFn z)= List.ofFn fun i:Fin n=> if i.val<x.length then z i else (z i).map (fun _=> false):= by
  unfold smother cutLists; dsimp
  apply List.ext_getElem
  · simp; omega
  intro i h v
  have p:i<n:=by simpa using v
  by_cases U:i<x.length
  · simp [List.getElem_append_left,p,U]
  rw [List.getElem_append_right (by simp;omega),List.getElem_map,List.getElem_drop,List.getElem_ofFn,List.getElem_ofFn]
  rw [ite_eq_right U]
  simp only [List.length_take,List.length_ofFn, Nat.min_eq_left (show x.length≤n by omega)]
  congr 3; omega

variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:∀ i,Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
abbrev markL (i:I):=Tri (n i)→Bool
variable (x:(i:I)→markL n i)
abbrev Mask := SpeakN n false x
abbrev assess (i:I)(a:Direction (n i))(x:markL n i)(j:Tri (n i)):Bool:=
  if (j a).val < modulus (n i) a then x j else false
abbrev Mask1 := SpeakB n a false x
include h
theorem sizeM : close n (Mask n x):=
  volts n h false (fun i a=> send (x i a)) 1 (fun i a=> (show (send (x i a)).count≤1 from le_refl _).trans (by rw [one_mul]; exact budget_p _)) -- order u after a? volts includes a?
omit h
private theorem readyW i l:
    smother (Code.tally (sZ n a i),SpeakS n a false x i l)=SpeakS n a false (fun i=> assess n i (a i) (x i)) i l:=by
  let z:= Card n a false x i l
  change smother (_,List.ofFn z)=_
  rw [memberN,Code.tally_length]
  change List.ofFn _=List.ofFn (Card n a false _ i l)
  apply congrArg List.ofFn; funext j
  unfold z Card
  let b (j:Fin (L0 n a i)) q:=offered (criterion (n i)) false (a i) l j q
  have g (q:tailS n a false i) :(b j q (a i))=j:= Wave.locS ..
  let s:=Y0 n a false i
  by_cases e:j.val<sZ n a i
  · rw [ite_eq_left e]
    apply congrArg (s.tab)
    funext k
    change _= if (b j k (a i)).val<_ then _ else _
    rw [g k,ite_eq_left e]
  rw [ite_eq_right e,Series.map_tab]
  apply congrArg (s.tab)
  funext k; change _= if (b j k (a i)).val<_ then _ else _; rw [g k,ite_eq_right e]; rfl
include h T A
theorem award :
    Mix n r (Mask n x) (Mask n (fun i=>assess n i (a i) (x i))):= by
  have M:= sizeM n h x
  have L:= Well.self T M
  have P:= toB n h a false T A _ L
  let R := RoomLine.sourceSize a (show RoomLine r n a from ⟨T.toCalendar,A⟩)
  let s:=X0 n a false
  let N:=ct s
  have C := Well.dispatchS T _ (chart n h a false T.guide A).1 (Moira.bounded.first ((atlas n h a false).pair))
  have D:Realizes r (sZ n a):=R
  have E:= ((IntegerMultiplication.Well.start_ T M).chain (C.twice (IntegerMultiplication.Well.source T D)))
  have V i : (s i).count*sZ n a i ≤ ton n i :=
    le_trans (Nat.mul_le_mul_left _ (Echo.pitch (h i) (a i))) (by
      have w:=(atlas n h a false).pair.out i
      change _*(Series.natural _).count ≤ _ at w; rw [Series.count_natural] at w; exact w)
  have H:= Strip.spread s (fun i=>send (Code.tally (sZ n a i))) E (by
    refine ⟨6,fun i=>?_⟩
    change (_:ℝ)*(size (Code.tally _):ℝ)≤_; rw [size_tally,tally_length]; unfold token; norm_cast
    have a: 1 ≤ sZ n a i:=Nat.pos_of_neZero _
    have p:(s i).count ≥ 1:= (atlas n h _ false).l i
    specialize V i
    nlinarith)
  let ticket i (p:headS n a false i):=(Code.tally (sZ n a i), SpeakS n a false x i p)
  have U: Mix n r (Mask n x) (stackRun s (fun i p=> send (ticket i p))):= coalesce s _ _ H P
  have H₁ {X:Type}[Codec X](f:(i:I)→headS n a false i→X):
      stackRun s (fun i y=>send (f i y))=(fun i=>send ((s i).tab (f i))) := funext fun i=>stripe_eq' ..
  rw [H₁] at U
  have y:= U.chain (Carries.func U.budget U.out (List.map smother) smotherE.mapping)
  apply Wave.toN n a false _
  unfold SpeakB; rw [H₁]
  simp only [Series.map_tab,Function.comp_def,ticket,readyW n a x] at y
  exact y
end Dune

end IntegerMultiplication
end Computability
end OAI
