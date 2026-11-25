import OAI.Computability.IntegerMultiplication.Cap.Inverse
import OAI.Computability.IntegerMultiplication.Scale.Stars

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cap
open Scale Staff Strip Code Carry Brief IntegerMultiplication.Fourier Param
-- use Signed.sums for Figure
variable {I:Type} {r:Regime I}
variable (n:I→ℕ) (u:Realizes r n)
variable (f:(i:I)→Fin (n i)→ℕ)
variable (h:Figure (signal n u) (fun i:Across n=>f i.1 i.2))
include h
theorem lists :
    Figure r (fun i=>∏ j,f i j) ∧ Figure r (fun i=> ∑ j,f i j) := by
  obtain ⟨H,P⟩:=Signed.sums (r:=r) n u (v:=fun i j=> ((f i j):ℤ)) (Signed.up h)
  have e1 (i:I) : (∏ j,((f i j):ℤ)).toNat=∏ j,f i j := by simp only [← Nat.cast_prod,Int.toNat_natCast]
  have e2 (i:I) : (∑ j,((f i j):ℤ)).toNat=∑ j,f i j := by simp only [← Nat.cast_sum,Int.toNat_natCast]
  exact ⟨by simpa only [e1] using P.toNat,by simpa only [e2] using H.toNat⟩
omit h
variable (q:Calendar r n)
variable (a:(i:I)→Direction (n i))
variable (p:Figure r (fun i=>(a i).val))
include q p
theorem calibration :
    Figure r (fun i=>inverse (moduli (n i) (a i)) (base (fun j:Direction (n i)=>moduli (n i) j.val) (a i))) := by
  let d:= lanes ∘ n
  let F i (j:Fin (d i)):=moduli (n i) j
  let D:=q.royalty n
  have t : Realizes r (fun i=>(a i).val) := p.pay
    ((diameter d D).mono (fun i=> (a i).isLt.le))
  let V : RoomLine r n a :=⟨q,t⟩
  let l:=fun i=>F i (a i)
  let M:Realizes r l:= V.sourceSize a
  let L i:=base (F i) (a i)
  have Z:Figure r L := by
    unfold L base
    refine (lists _ D _ ?_).1
    have g:= floor_ d D
    have H:= (q.levels n d D).guide.size_ (n ∘ (Sigma.fst: Across d→I)) g
    have e (i:Across d) : (if i.2< a i.1 then F i.1 i.2 else 1) =
        if i.2.val<(a i.1).val then F i.1 i.2 else 1 := by rfl
    -- simp with e (DecPred defeq)
    have x:= H.variant (.natural 1) ((Figure.of_spoken g).compare_ (Garden.ferryF d D p))
    exact x -- definitional Fin LT?
  unfold inverse
  refine (lists _ M _ ?_).2
  let P:= Garden.ferryF l M Z
  let S: Figure (signal l M) (fun i:Across l=>l i.1):=(Figure.of_spoken (landing l M l M))
  let X:=Figure.of_spoken (floor_ l M)
  exact X.variant (.natural 0) (Garden.ident ((P.multiplied X).modded S) (.natural 1))

omit p in
theorem sur (i:I):
    let s j:= moduli (n i) ((j:Direction (n i)).val)
    Nice s := by
  constructor
  · intro j
    have t: 2 ≤ (budget (n i)) :=
      (lane2 (n i)).trans (Nat.le_self_pow (by decide) _)
    exact t.trans ((q.shines i).budget_ _ j.isLt)
  intro v x h
  exact axis_separation _ v.isLt x.isLt fun e=>h (Fin.ext e)
omit p in
/-- Binary coefficient packed in a few polynomial bits for small directory header. -/
def angles (n:I→ℕ) (i:I) := List.ofFn (fun a:Direction (n i)=>
    Bits.short (P (n i)) (coefficient (d:=lanes (n i)) (fun j:Direction (n i)=>moduli (n i) j.val) a))
omit p
theorem issue_ :
    r.Has (angles n) := by
  let D:= q.royalty n
  apply harvest _ D
  let d:= lanes ∘ n
  let z:Across d→I:= Sigma.fst
  have P := calibration (n ∘ z) (q.levels n d D) (fun i=>i.2) (Figure.of_spoken (floor_ d D))
  exact P.write (landing d D _ (q.guide.fund n))
-- recover small length
theorem angles_read (i:I) (a:Direction (n i)):
    Bits.value (Bits.short (P (n i)) (coefficient (d:=lanes (n i)) (fun j:Direction (n i)=>moduli (n i) j.val) a))
      = coefficient (fun j:Direction (n i)=>moduli (n i) j.val) a := by
  let s j:=moduli (n i) ((j:Direction (n i)))
  have e := ((q.shines i).upper a)
  have v : coefficient s a < s a := (coefficient_use (sur n q i) a).1
  rw [Bits.value_short,Nat.mod_eq_of_lt]
  exact v.trans_le (e.1.trans e.2)

end Cap

end IntegerMultiplication
end Computability
end OAI
