import OAI.Computability.IntegerMultiplication.Well.Stretch
import OAI.Computability.IntegerMultiplication.Rivulet.Market

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Dims Code
open Rivulet Dusk Grid Echo Cone Cap Brief Staff
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:(i:I)→Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (σ:(i:I)→Fin (axio n a i)→Fin (axio n a i))
variable (b:(i:I)→Fin (axio n a i)→ Cone.G (n i))
abbrev Cue:= Grid.Orb
abbrev Menu0:= Rivulet.Menu × List Cue
abbrev Story:= List Morse.Seat × Menu0
abbrev coupon (i:I)(j:Fin (axio n a i)):Cue:= (tally (Scale.F (n i)),Dusk.mark (b i j))
structure Standards (n:I→ℕ) (a:(i:I)→Direction (n i))
    (σ:(i:I)→Fin (axio n a i)→Fin (axio n a i))(b:(i:I)→Fin (axio n a i)→ Cone.G (n i))
    (m:I→ Rivulet.Menu)(f: List Morse.Seat × Rivulet.Menu→ List Morse.Seat) (r:Regime I):Prop where
  permit : r.Has (fun i=>(m i,List.ofFn (coupon n a b i)))
  room i: Code.size (m i) ≤ 50*(axio n a i)
  proc : Easy f
  tells i (x:Fin (axio n a i)→Morse.Seat):
    f (List.ofFn x,m i)=List.ofFn (x ∘ σ i)

noncomputable section
variable (m:I→Rivulet.Menu) (f:List Morse.Seat × Rivulet.Menu→ List Morse.Seat)
variable (C:Standards n a σ b m f r)
abbrev wages i:=(m i,List.ofFn (coupon n a b i))
abbrev leftG:=prefixL n h a
abbrev rightG:=suffixL n h a
abbrev turnG:=mid_ n a
abbrev L i:=Pin (vv n h a i).p
abbrev U i:=Pin (vv n h a i).q
abbrev M i:=Fin (axio n a i)
abbrev boundG i := (tax (Scale.W (n i)):ℝ)
include C
theorem cash (i:I): size (wages n a b m i)≤ 200000* Scale.P (n i)*axio n a i := by
  let y:=n i
  have Q (j:M n a i) : size (coupon n a b i j)≤120000*P y := by
    rw [coupon,size_prod]; dsimp only; rw [size_tally,tally_length,Dusk.volume]
    have e : F y≤Scale.W y+1:=by unfold F Scale.W; omega
    change _*(F y)+1+(4*(Scale.W y+1)+3)+1≤_
    have u:= near_ y; have d:1≤P y:=budget_p _; nlinarith
  have E: size (List.ofFn (coupon n a b i))≤(axio n a i)*(120000*P y+1)+1:= by
    let K := Series.natural (axio n a i)
    have t: send (List.ofFn (coupon n a b i))=stripe K (fun j=> send (coupon n a b i j)) := by
      rw [stripe_eq']; congr
      change _=List.map (coupon n a b i) (List.finRange _)
      simp [List.finRange,Function.comp_def]
    unfold size; rw [t]
    exact (stripe_size K _ _ Q).trans (le_of_eq (by unfold K; rw [Series.count_natural]))
  unfold wages
  rw [size_prod]; dsimp only; have W:= C.room i
  have p:1≤P y:=budget_p _
  have v:1≤axio n a i:=Nat.pos_of_ne_zero (NeZero.ne _)
  change _≤200000*P y* _
  nlinarith
include h T A
variable {p:I→Tree}
theorem weather (p0: Bureau.close n p):
    Mix n r p (stackRun (leftG n h a) (fun i _=>send (wages n a b m i))) := by
  let Y:=leftG n h a
  have t:= (passport n h a).pair
  have z:= know n T h a A -- replace
  have E:= dispatchS T _ z t.first -- dispatchS
  apply Strip.spread Y _ (((start_ T p0).chain E).twice (IntegerMultiplication.Well.start T p0 C.permit))
  refine ⟨200000*2,fun i=>?_⟩
  change _ * (size _:ℝ)≤ _
  have u:= (passport n h a).l i
  unfold ct at u
  have v : 0<ct (suffixL n h a) i:= (passport n h a).p i
  have Q: ((Y i).count+1)*size (wages n a b m i)≤200000*2*ton n i := by
    calc
     _ ≤ (2*(Y i).count)*(200000*P (n i)*axio n a i):=
      Nat.mul_le_mul (by unfold Y leftG; omega) (cash n a σ b m f C i)
     _ ≤ _ := by
      have A : (Y i).count*axio n a i ≤ load (n i) := (Nat.le_mul_of_pos_right _ v).trans (IntegerMultiplication.Well.volume n h a i).le
      have B:= Nat.mul_le_mul_left (2*200000*P (n i)) A
      unfold ton; nlinarith
  unfold token; exact_mod_cast Q
end
end Olive

end IntegerMultiplication
end Computability
end OAI
