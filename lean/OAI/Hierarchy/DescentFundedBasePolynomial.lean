import OAI.Hierarchy.DescentDonorExponentBounds
import OAI.Hierarchy.DescentPublicDegreeNumbers

namespace OAI
/-! The predecessor census, actor tickets and old packet fit a single calendar exponent. -/
namespace Hierarchy.DescentSixParty.NativePitch.FundedBase
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
open scoped BigOperators
noncomputable section

def upper (D r cap amount : ℕ) :=
  let P:=(D+1)^4
  let slots:=2^packExponent 20 D+2
  let rawBits:=Nat.clog 2 ((r*2)*slots+1)
  let key:=Nat.clog 2 ((r*2-1)*slots+1)
  let donors:=P*r
  let actors:=donors*(1+cap*6)
  let local₀:=max 2 (max (amount+1*r) (max ((Nat.clog 2 (P+1))+1)
      (max rawBits (max (1+rawBits) (key*actors+key)))))
  let paid:=max (amount*donors+amount) (max (key*actors) (1*actors+amount*donors))
  max amount (max amount (max local₀ (max paid 0)))

private theorem finiteTable {I:Type*} (age degree:I→ℕ) (bound:ℕ) (small:∀x,degree x≤bound)
    (f:ℕ→ℕ) : AgeBound age (fun x=>f (degree x)) :=by
  apply (AgeBound.const age (∑q:Fin (bound+1),f q.val)).mono
  intro x
  let q:Fin (bound+1):=⟨degree x,Nat.lt_succ_of_le (small x)⟩
  exact Finset.single_le_sum (f:=fun q:Fin (bound+1)=>f q.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ q)

theorem bounded {I:Type*} (age D r cap amount:I→ℕ) (d:ℕ) (hD:∀x,D x≤d)
    (rad:AgeBound age r) (caps:AgeBound age cap) (units:AgeBound age amount) :
    AgeBound age (fun x=>upper (D x) (r x) (cap x) (amount x)) :=by
  let n:=AgeBound.const age
  have paths:=finiteTable age D d hD (fun D=>(D+1)^4)
  have slots:=finiteTable age D d hD (fun D=>2^packExponent 20 D+2)
  have twice:=rad.mul (n 2)
  have less:AgeBound age (fun x=>r x*2-1):=twice.mono (fun _=>Nat.sub_le ..)
  have raw:=(((twice.mul slots).add (n 1)).clog)
  have key:=(((less.mul slots).add (n 1)).clog)
  have donors:=paths.mul rad
  have actors:=donors.mul ((n 1).add (caps.mul (n 6)))
  have local₀:=(n 2).maximum ((units.add ((n 1).mul rad)).maximum
      ((((paths.add (n 1)).clog).add (n 1)).maximum (raw.maximum (((n 1).add raw).maximum ((key.mul actors).add key)))))
  have paid:=((units.mul donors).add units).maximum ((key.mul actors).maximum (((n 1).mul actors).add (units.mul donors)))
  exact units.maximum (units.maximum (local₀.maximum (paid.maximum (n 0))))

end
end Hierarchy.DescentSixParty.NativePitch.FundedBase

end OAI
