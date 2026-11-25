import OAI.Computability.IntegerMultiplication.Bureau.Remark
import OAI.Computability.IntegerMultiplication.Bureau.Valor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Moira
open Bureau Strip Code Param Halo Scale Brief Carry
variable {I:Type}(n:I→ℕ)
abbrev ct {A:I→Type} (s:(i:I)→Series (A i)) (i:I):ℕ := (s i).count
abbrev amen {A:I→Type} (s:(i:I)→Series (A i)):= Figure (city n) (ct s)
variable {n}
variable {A B C:I→Type}(s:(i:I)→Series (A i))(t:(i:I)→Series (B i))(g:(i:I)→Series (C i))
abbrev land (i:I) := (s i).cart (t i)
theorem amenLand (a:amen n s)(b:amen n t):amen n (land s t):=by
  unfold amen ct land; simp_rw [Series.count_cart]; exact a.multiplied b
structure bounded {A B:I→Type} (n:I→ℕ) (s:(i:I)→Series (A i))(t:(i:I)→Series (B i)):Prop where
  L(i):1≤ct s i
  R(i):1≤ct t i
  out(i):ct s i*ct t i≤ton n i
variable {s t}
namespace bounded
variable (v:bounded n s t)
include v
theorem first (i) : ct s i ≤ ton n i := le_trans (Nat.le_mul_of_pos_right _ (v.R i)) (v.out i)
theorem second (i): ct t i ≤ ton n i := le_trans (Nat.le_mul_of_pos_left _ (v.L i)) (v.out i)
end bounded
variable (s t)
theorem paidG (u:(i:I)→ A i×B i→ Tree) {x:I→Tree}(f:Wood n x (fun i=>stripe ((s i).cart (t i)) (u i)))
    (v:bounded n s t) (a:amen n s)(b:amen n t):
    Wood n x (fun i=>stripe (s i) (fun p=> stripe (t i) (fun z=>u i (p,z)))) := by
  have e:= gig _ _ (dispatchT _ a v.first) (dispatchT _ b v.second)
    (fun i=> by
      have Q:= v.out i; have M:=v.second i; have J:=v.first i; nlinarith [tonp n i])
  apply rows s t u
  exact ((scoop (Volume.right f.small)).chain e).twice f

-- compose to triple: stable layout as (s*t)*g
structure Atlas (n:I→ℕ) (s:(i:I)→Series (A i))(t:(i:I)→Series (B i))(z:(i:I)→Series (C i)):Prop where
  l(i):1≤ct s i
  m(i):1≤ct t i
  p(i):1≤ct z i
  total(i): ct s i * ct t i * ct z i≤ton n i
variable {s t g}
namespace Atlas
variable (v:Atlas n s t g)
include v
theorem up :
    bounded n (land s t) g := by
  have p(i):ct (land s t) i=ct s i*ct t i:=Series.count_cart ..
  exact ⟨fun i=> p i ▸ Nat.mul_pos (v.l i) (v.m i),v.p,fun i=>p i ▸ v.total i⟩
theorem pair :
    bounded n s t :=
  ⟨v.l,v.m,fun i=>(Nat.le_mul_of_pos_right _ (v.p i)).trans (v.total i)⟩
end Atlas
variable (s t g)
abbrev raw (v:(i:I)→A i→B i→C i→Tree) :I→Tree:=
  fun i=>stripe (((s i).cart (t i)).cart (g i)) (fun p=>v i p.1.1 p.1.2 p.2)
abbrev upper (v:(i:I)→A i→B i→C i→Tree) :I→Tree:=
  fun i=> stripe ((s i).cart (t i)) (fun p=>stripe (g i) (v i p.1 p.2))
abbrev triple (v:(i:I)→A i→B i→C i→Tree) :I→Tree:=
  fun i=>stripe (s i) (fun p=>stripe (t i) (fun q=>stripe (g i) (v i p q)))
theorem authorize (v:(i:I)→A i→B i→C i→Tree) {x:I→Tree}(f:Wood n x (raw s t g v))
    (a:amen n s)(b:amen n t)(c:amen n g)
    (h:Atlas n s t g):Wood n x (triple s t g v) :=
  let u: Wood n x (upper s t g v):=paidG (land s t) g _ f h.up (amenLand s t a b) c
  paidG s t _ u h.pair a b

variable {k:I→ℝ} {p:I→Tree}
theorem conform (v:(i:I)→A i→B i→C i→Tree) (f:Spun n k p (triple s t g v)):
    Spun n k p (raw s t g v):=
  let u : Spun n k p (upper s t g v):=Strip.flatten s t (fun i (u:A i×B i)=>stripe (g i) (v i u.1 u.2)) f
  Strip.flatten (land s t) g (fun i (u:(A i× B i)× C i)=>v i u.1.1 u.1.2 u.2) u

theorem wide (c:ℕ) (v:(i:I)→A i→B i→C i→Tree)
    (h:∀ i,ct s i*ct t i*ct g i≤load (n i))
    (p:∀ i x y z,(v i x y z).count ≤ c* Scale.P (n i)):
    close n (raw s t g v) := by
  refine ⟨c+2,fun i=>?_⟩
  let p0:= Scale.P (n i)
  have e := stripe_size ((s i).cart (t i)|>.cart (g i)) (fun x=>v i x.1.1 x.1.2 x.2) (c*p0) (fun u=>p i ..)
  rw [Series.count_cart,Series.count_cart] at e
  have z:= h i
  unfold ct at z
  change ((stripe _ _).count:ℝ) ≤ _
  unfold token ton
  have pay : ((s i).count*(t i).count*(g i).count*(c*p0+1)+1) ≤ (c+2)* (load (n i)* Scale.P (n i)) := by
    have W:=Nat.mul_le_mul_right (c*p0+1) z
    have T:1≤load (n i):=Nat.pow_pos (by decide)
    have X:1≤P (n i):= budget_p _
    unfold p0 at *; nlinarith
  exact_mod_cast (e.trans pay)
end Moira

end IntegerMultiplication
end Computability
end OAI
