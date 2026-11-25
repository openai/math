import OAI.Computability.IntegerMultiplication.Fix.Palace
import OAI.Computability.IntegerMultiplication.Strip.Index

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open _root_.OAI.Computability.IntegerMultiplication.Fix Code
variable {I A : Type} [Codec A] [FiniteState A] [Fintype A] [DecidableEq A]
variable {B X : I → Type} {s : (i:I)→Series (B i)} {t : (i:I)→Series (X i)}
variable [(i:I)→Fintype (B i)] [(i:I)→Fintype (X i)] [(i:I)→DecidableEq (B i)]
variable (g : (i:I)→File (s i) A (t i)) (f : A≃A)
variable {r : Regime I} {n : I→ℕ}
variable (q : (i:I)→B i→Tree) (hq : Manifest _ n q)
include hq
/-- A finite halo within an arbitrary file. Linear (under fat allowance).
send needn't be bounded by n in statement since alphabet is fixed. -/
theorem localAction
    (v : Strip.Trace r s fun i a => send (slot (g i) a)) :
    Fleet r n s s q (fun i => Optic.travel (Optic.field (g i).focus f) (q i)) := by
  let e := Series.arbitrary A
  let key (a : A) := e.tab fun b => decide (a=b)
  let D := e.count
  have dk a : (key a).length=D := Series.card ..
  have k : Function.Injective key := by
    intro a b t
    have z := congrFun (e.faithful t) b
    simpa using z
  have tag (u : A→Bool × Key) : Strip.Trace r s fun i b => send (u (slot (g i) b)) :=
    v.tune (Regime.Has.ez (r:=onboard r (fun i b => send (slot (g i) b)) v.meter) (g:=fun x=> slot (g x.1) x.2)
      (onboard_hat (fun i b => send (slot (g i) b)) v.meter) (Easy.finite u))
  let x := Drive.fetch (l:=n) v.valid.1 (hq.lives v.valid)
  let y := Drive.self (l:=n) v.valid.1 (hq.lives v.valid)
  obtain ⟨C,P⟩ := hq.size
  exact Palace g (fun _=>f) (fun _ _=>true) (fun _=>key) (fun _=>k) q
    (fun _ _ e => Bool.noConfusion e) (d:=fun _=>D) (fun _=>dk)
    y
    (x.chain ((tag (fun a=>(true,key (f a)))).offer.monoSize (fun _ => le_rfl) (fun _=>Nat.zero_le _)))
    (x.chain ((tag (fun a=>(true,key a))).offer.monoSize (fun _=>le_rfl) (fun _=>Nat.zero_le _)))
    (fun _=>le_rfl) (Dom.const _ _) C P ⟨D+1,by simp⟩
end Strip

end IntegerMultiplication
end Computability
end OAI
