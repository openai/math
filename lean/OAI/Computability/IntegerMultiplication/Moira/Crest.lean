import OAI.Computability.IntegerMultiplication.Morse.Catalogue
import OAI.Computability.IntegerMultiplication.Bureau.Remark

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Net Net.Walsh Strip Loom Adic Dusk Grid Axon Finset Code Bits Staff Brief Carry
open Param Halo Morse Scale Echo
variable {I:Type} (n:I→ℕ) (h:∀ i,Season (n i))
variable (b:(i:I)→ℕ→ Cone.G (n i)) -- fix G0
variable (V:(city n).Has fun i=>Grid.telex (Scale.F (n i)) (ell (n i)) (b i))
abbrev r0 := reach ∘ n
abbrev r1 := ell ∘ n
abbrev r2 := Scale.F ∘ n
abbrev r3 := Scale.W ∘ n
abbrev q0 (i:I):=wordB (h i) 0
abbrev q1 (i:I):=wordC (h i) 0
abbrev β0 (i:I):=Halo.shortBank (b i)
noncomputable section
include h V
theorem q0_B :
    (city n).Has (fun i=>Morse.scroll (r2 n i) (q0 n h i) (β0 n b i) (r0 n i)) := by
  let r:=city n
  let T:= Scale.birthday h
  have P:Realizes r (r2 n):=T.fraction n
  have W:Realizes r (r1 n):=T.guide.tensorSize n
  have K:Realizes r (r0 n):=T.guide.reducedTensor n
  have Q:Realizes r (fun i=> 2^r1 n i):=T.localRoom
  have X:Realizes r (fun i=> 2^r0 n i):=cypress K (fun i=>by have e:=(h i).shortWidth; change reach _ ≤ ell _; omega) Q
  have M:Realizes r (fun i=>abbreviated (n i)):=T.guide.positions n
  have E:Realizes r (fun i=>modulus (n i) (near (h i))):=
    Scale.RoomLine.sourceSize _ (show Scale.RoomLine r n (fun i=>near (h i)) from ⟨T,M⟩)
  have L(i): value (q0 n h i)=modulus (n i) (near (h i)):=pricedN (h i) _ (near_s (h i))
  have G:Realizes r (value ∘ q0 n h):=by
    simp only [Function.comp_def,L]; exact E
  have B:r.Has (Morse.page (r1 n) (r3 n) b):=Morse.minister (r1 n) (r3 n) (r2 n) b V
  apply Morse.bib (r0 n) (r3 n) (r2 n) (q0 n h) (β0 n b) P K X G
  unfold Morse.page
  let f i:= 2^r0 n i
  apply harvest f X
  let R:=signal f X
  let o:= Staff.at_ f
  have U (m:I→ℕ)(z:Realizes r m):Realizes R (m ∘ o):= landing f X m z
  have A:R.Has (Morse.page ((r1 n) ∘ o) ((r3 n) ∘ o) (fun i=> b i.1)):= sendRoof f X _ B
  have Z:= T.guide.missing n
  have C:Realizes r (fun i=>2^slack (n i)):=cypress Z (fun i=>by have e:=(h i).shortWidth; change slack (n i)≤ell (n i); omega) Q
  exact Morse.position ((r1 n) ∘ o) ((r3 n) ∘ o) (fun i=>b i.1) A
    ((U _ C).times (floor_ f X))
    (by
      intro i
      let y:=n i.1
      change _ < 2^ell y
      rw [← (h i.1).shortWidth,pow_add,Nat.mul_comm (2^reach y)]
      exact Nat.mul_lt_mul_of_pos_left i.2.isLt (Nat.pow_pos (by decide:(0:ℕ)<2):0< (2:ℕ)^slack y))

theorem q1_B :
    (city n).Has (fun i=>Morse.scroll (r2 n i) (q1 n h i) (b i) (r1 n i)) := by
  let r:=city n; let T:= Scale.birthday h
  have P:Realizes r (r2 n):=T.fraction n
  have W:Realizes r (r1 n):=T.guide.tensorSize n
  have Q:Realizes r (fun i=> 2^r1 n i):=T.localRoom
  have M:Realizes r (fun i=>abbreviated (n i)+1):=(T.guide.positions n).plus (Realizes.fix 1)
  have E:Realizes r (fun i=>modulus (n i) (rear (h i))):=
    Scale.RoomLine.sourceSize _ (show Scale.RoomLine r n (fun i=>rear (h i)) from ⟨T,M⟩)
  have L(i): value (q1 n h i)=modulus (n i) (rear (h i)):=pricedN (h i) _ (rear_f (h i))
  have G:Realizes r (value ∘ q1 n h):=by simp only [Function.comp_def,L]; exact E
  have B:r.Has (Morse.page (r1 n) (r3 n) b):=Morse.minister (r1 n) (r3 n) (r2 n) b V
  exact bib (r1 n) (r3 n) (r2 n) (q1 n h) b P W Q G B
end
end Moira

end IntegerMultiplication
end Computability
end OAI
