import OAI.Computability.IntegerMultiplication.Rivulet.Menu
import OAI.Computability.IntegerMultiplication.Morse.Buckle

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Rivulet
open Strip Code Dusk Grid Axon Net Net.Walsh
variable {I:Type}{T:I→Type}(z:(i:I)→Series (T i))(w p:I→ℕ)
variable (x:(i:I)→T i→Grain (w i))(b:(i:I)→ Grain (w i))
noncomputable section
abbrev Note := Morse.Seat × Orb
abbrev ins (i:I):Note:=((z i).tab (fun v=>Dusk.mark (x i v)),tally (p i),Dusk.mark (b i))
abbrev reading (i:I):ℝ:= ((z i).count+1:ℝ)* Grid.cost w i
abbrev flavor (i:I):Orb:=(tally (p i),Dusk.mark (b i))
abbrev fine (i:I)(a:T i):Grain (w i):=launch (x i a,flavor w p b i)
theorem rated (i) :1 ≤reading z w i:=
  one_le_mul_of_one_le_of_one_le (by simp) (cost_pos ..)
theorem buy_ (h:∀ i,p i≤w i+1)(i): size (flavor w p b i)≤12*(w i+1) := by
  rw [flavor,size_prod]; dsimp only; rw [size_tally,tally_length,Dusk.volume]
  specialize h i; omega
variable (h:∀ i,p i≤w i+1)
include h
theorem mini (i):
    size (ins z w p x b i)≤ 16*((z i).count+1)*(w i+1) := by
  have t: size ((z i).tab (fun v=>Dusk.mark (x i v)))≤ (z i).count*(8*(w i+1))+1 := by
    change (send _).count≤_
    rw [← stripe_eq']
    calc
      _ ≤ (z i).count*(7*(w i+1)+1)+1 := stripe_size _ _ (7*(w i+1)) (fun a=> by
        change size (Dusk.mark _)≤_
        rw [Dusk.volume]; omega)
      _ ≤ _:= by gcongr; omega
  rw [size_prod]; dsimp only
  have v:= buy_ w p b h i
  nlinarith

/-- Multiply all suffix entries by common weight. accepts empty rows too. -/
theorem purse :
    Carries (reading z w) (send ∘ ins z w p x b)
      (fun i=> send ((z i).tab (fun a=>Dusk.mark (fine w p x b i a)))) := by
  let Y i:=(z i).tab fun a=>Dusk.mark (x i a)
  let V:=flavor w p b
  let m i:=send (Y i,V i)
  have U : Volume (reading z w) m := by
    refine ⟨16,fun i=> le_trans (by exact_mod_cast mini z w p x b h i :
      (size (ins z w p x b i):ℝ)≤ 16*((z i).count+1)*(w i+1)) ?_⟩
    unfold reading Grid.cost
    push_cast
    have u:(1:ℝ)≤Grid.tax (w i):=by exact_mod_cast tax_pos ..
    have p : (0:ℝ)≤((z i).count+1:ℝ)*(w i+1):=by positivity
    nlinarith [mul_le_mul_of_nonneg_left u p]
  have v:= (Carries.idles (rated z w) U)
  let C0:Carries (reading z w) m (send ∘ Y):=
    v.chain (Carries.func v.budget v.out Prod.fst Easy.fst)
  have A: Carries (reading z w) m (send ∘ V):=
    v.chain (Carries.func v.budget v.out Prod.snd Easy.snd)
  have c:=C0.chain (Carries.func C0.budget C0.out ruler (Easy.ruler Easy.identity))
  have cnt i : ruler (Y i)=tally (z i).count:= by simp only [Y,ruler,List.map_const',tally,Series.card]
  change Carries _ _ (send ∘ ruler ∘ Y) at c
  simp only [Function.comp_def,cnt] at c
  have t:= Strip.spread z (fun i=>send (V i)) (c.twice A)
  have D: Carries (reading z w) m (stackRun z fun i a=>send (V i)) := t (by
    refine ⟨12,fun i=>?_⟩
    unfold reading Grid.cost
    have u : (1:ℝ)≤ Grid.tax (w i):=by exact_mod_cast tax_pos ..
    have g : (size (V i):ℝ)≤ 12*(w i+1):=by exact_mod_cast buy_ w p b h i
    change _*(size (V i):ℝ) ≤_
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left g (show 0≤((z i).count+1:ℝ) by positivity),
      mul_le_mul_of_nonneg_left u (show (0:ℝ)≤((z i).count+1:ℝ)*(w i+1) by positivity)])
  have P:= Strip.coalesce z (fun i a=> send (Dusk.mark (x i a))) (fun i _=>send (V i))
    (show Carries _ m _ from by unfold stackRun; simp_rw [stripe_eq']; exact C0) D
  let S(i:I) (a:T i):=send (Dusk.mark (fine w p x b i a))
  have G:= Grid.ferry (w ∘ (Sigma.fst : Sigma T→I)) (V ∘ Sigma.fst)
    (fun i:Sigma T=>x i.1 i.2) 12 (fun i=>buy_ w p b h _)
  let R(i:I)(a:T i):=send (Dusk.mark (x i a),V i)
  have L:= liftoff z R S (Grid.cost w) G
  have E:= P.chain (q:=stackRun z R) (L.larger (d:=reading z w) (by
    intro i; unfold reading; rw [add_mul,one_mul]; gcongr; exact cost_pos ..))
  unfold stackRun S at E
  simp_rw [stripe_eq'] at E
  exact E
end
end Rivulet

end IntegerMultiplication
end Computability
end OAI
