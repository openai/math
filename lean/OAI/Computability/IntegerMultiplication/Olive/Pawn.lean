import OAI.Computability.IntegerMultiplication.Olive.Step
import OAI.Computability.IntegerMultiplication.Olive.Header

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code Rivulet Dusk Grid
open Echo Cone Cap Brief Staff IntegerMultiplication.Fourier
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (P:Faculty n)(B:P.release n r)
variable (o:I→ℤ)(H:Realizes r (fun i=>(wrap (modN n a i) (o i)).val))

private theorem planCost {s t:ℕ} (x:Fin t→Fin s)(h:∀ i,many x i≤2):
    size (plan x)≤ s*6+1:= by
  let q:=fun i=>Code.tally (many x i)
  have e: List.ofFn q=(Series.natural s).tab q:= by change List.ofFn q=List.map _ (List.finRange _); simp [List.finRange,Function.comp_def]
  unfold Rivulet.plan
  rw [e]
  change (send _).count≤_; rw [← stripe_eq']
  exact (stripe_size _ _ 5 (fun i=>by change size (q _)≤_; unfold q; rw [size_tally,Code.tally_length]; specialize h i; omega)).trans (le_of_eq (by rw [Series.count_natural]))

noncomputable section
variable (h:∀i,Season (n i))
abbrev menu0 i:= menuA (s:=modN n a i) (t:=axio n a i) (o i)
abbrev menu1 i:= menuB (Echo.pitch (h i) (a i)) (o i)
abbrev seln i:= Rivulet.p0 (Echo.pitch (h i) (a i)) (o i)
abbrev end_ i:= p1 (Echo.pitch (h i) (a i)) (o i)
include h
theorem health (i:I): axio n a i≤ 2*modN n a i:=
  Param.Margin.far ((h i).margin _ (a i).isLt) (lanes_pos _)
theorem u0(i:I) : Code.size (menu0 n a o i) ≤ 50*axio n a i := by
  let s:= modN n a i
  let t:= axio n a i
  unfold menu0 menuA
  rw [size_prod,size_prod]; -- second targets Tally? size_prod List Unit no
  dsimp only; rw [size_tally,size_tally,Code.tally_length,Code.tally_length]
  have d:= planCost (river (s:=s) (t:=t)) (m_f (health n a h i))
  have V : (wrap s (o i)).val<s:=Fin.isLt ..
  have W : s≤t:=pitch (h i) (a i)
  have Q : 0<t:=Nat.pos_of_ne_zero (NeZero.ne _)
  change 2*s+1+(2*(wrap s (o i)).val+1+size (plan (river (s:=s) (t:=t)))+1)+1≤_
  change _≤50*t
  omega
theorem u1(i:I) : Code.size (menu1 n a o h i) ≤ 50*axio n a i := by
  let s:= modN n a i; let t:=axio n a i
  let v:s≤t:=pitch (h i) (a i)
  have d:=planCost (pick s t v) (fun i=> (m_p v i).trans (by decide:1≤2))
  unfold menu1 menuB
  rw [size_prod,size_prod]; dsimp only; rw [size_tally,size_tally,Code.tally_length,Code.tally_length]
  have V := (wrap s (o i)).isLt
  have Q : 0<t:=Nat.pos_of_ne_zero (NeZero.ne _)
  change 2*s+1+(2*(wrap s (o i)).val+1+size (plan (pick s t v))+1)+1≤50*t
  omega
include T A B H
theorem oracleA : Standards n a (seln n a o h) (strokeA n a P o)
    (menu0 n a o) (ferryA ([]:Morse.Seat)) r :=
  let S:RoomLine r n a:=⟨T.toCalendar,A⟩
  ⟨(shippingA (modN n a) (axio n a) (S.sourceSize a) (S.targetSize a) o H).pair (vesselA n T a A P B o H),
    u0 n a o h,ferryA_E _,fun i _x=> trip0 _ _ _ _ (health n a h i)⟩
theorem oracleB (u:Bool): Standards n a (end_ n a o h) (strokeB n a P o u)
    (menu1 n a o h) (ferryB ([]:Morse.Seat)) r:=
  let S:RoomLine r n a:=⟨T.toCalendar,A⟩
  ⟨(shippingB (modN n a) (axio n a) (S.sourceSize a) (S.targetSize a) o H _).pair (vesselB n T a A P B o H u),
    u1 n a o h,ferryB_E _,fun _i _x=> trip1 ..⟩
end
end Olive

end IntegerMultiplication
end Computability
end OAI
