import OAI.Computability.IntegerMultiplication.Dune.Mask
import OAI.Computability.IntegerMultiplication.Wave.Reel

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dune
open Param Scale Halo Strip Code Dims Cap Loom Staff Brief Carry Echo Well Moira Bureau Atoll Wave
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:∀ i,Season (n i))
include h
theorem samples(i:I):(bot (criterion (n i))).count=load (n i) := by
  rw [Series.total,Cap.card,show Cap.space (criterion (n i))=load _ from (h i).volume]
include T
variable {p:I→Tree}(U:close n p)
include U
private theorem baseM :
    Mix n r p (Mask n fun _ _=>true):= by
  let s i:=load (n i)
  have M:Figure r s := (Figure.natural 2).repeated (T.guide.exSize n)
  have v := dispatchS T s M (fun i=>Nat.le_mul_of_pos_right (s i) (budget_p _))
  have V:= (Well.start_ T U).chain v
  have G:=V.chain (Carries.func V.budget V.out (fill true) (easy_fill _ Easy.identity))
  unfold Mask
  rw [Wave.specs]
  change Mix n r p (fun i=>send ((bot (criterion (n i))).tab (fun a=>true)))
  have e(i):(bot (criterion (n i))).tab (fun _=> true)=fill true (Code.tally (s i)):= by
    unfold Series.tab; rw [List.map_const']; change List.replicate (bot (criterion (n i))).count true=_
    rw [samples n h i]; simp [fill]
    rfl
  simp_rw [e]; exact G
omit T U h
private theorem memB (i:I)(l:List (Direction (n i)))(j):
    (l.foldr (assess n i) (fun _=>true) j)=true ↔ ∀ a∈l,(j a).val < modulus (n i) a:= by
  induction l with
  | nil=>simp
  | cons a l ih=>
    simp only [List.foldr_cons,assess,List.forall_mem_cons]
    split
    next h=> simp only [h,true_and]; exact ih
    next h=> simp only [h, Bool.false_eq_true, false_and]
include T U h
theorem banner : Well.Mid n r (hue n) p (Mask n fun i=> Atoll.flag (modulus (n i)) (criterion (n i))) := by
  let k:=lanes ∘ n
  let V:=T.guide.spread n
  let t:=markL n
  let v:=Well.center k t
  let R:=Well.S0 k V t
  let e i (x:t i):= stripe (bot (criterion (n i))) (send ∘ x)
  let m:=n ∘ v
  let S:=Sigma t
  let g:= assess n
  have W:=sizeM (n ∘ (Sigma.fst:S→I)) (fun i=>h _) (fun i:S=>i.2)
  have X:= award m (Well.slid T k V t) (fun i=>h _) (fun i=>Dial.focus k i) (Well.spot k V t) (fun i=>i.val.value)
  let f (i:I):ℝ:=1
  have Q:=Well.sweep T (show ∀i,1≤f i from fun _=>le_rfl) k V t e g (fun i _=>true) W (Well.launch (show ∀ x, 1≤ f (v x) from fun _=>le_rfl) X)
  have L(i:I):
      (List.ofFn (id:Fin (k i)→Fin (k i))).foldr (g i) (fun _=>true) =
        Atoll.flag (modulus (n i)) (criterion (n i)):= by
    funext j
    apply Bool.eq_iff_iff.mpr
    rw [memB]
    simp only [Atoll.flag, Echo.Valid]
    constructor
    · intro hh
      exact decide_eq_true (fun a => hh a (List.mem_ofFn.mpr ⟨a, rfl⟩))
    · intro hh a _
      exact (of_decide_eq_true hh) a
  simp only [Well.result,f,one_mul] at Q
  have K:=Well.pipe (Well.launch (color_p n) (baseM n T h U)) (Wave.fameW n Q)
  suffices E: (fun i=> e i ((List.ofFn id).foldr (g i) (fun _=>true))) = Mask n (fun i=>Atoll.flag (modulus (n i)) (criterion (n i))) by rw [← E];exact K
  funext i; exact congrArg (e i) (L i)
end Dune

end IntegerMultiplication
end Computability
end OAI
