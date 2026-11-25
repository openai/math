import OAI.Hierarchy.DescentSharedCableSerial

namespace OAI
/-! Transporting a signed stream without changing any chronological rail or host position. -/
namespace Hierarchy.DescentSharedCableNames.Ends
open scoped Classical
noncomputable section
variable {H : Type} [DecidableEq H] {n m D cap : ℕ} {A : Ends H n} {B : Ends H m}

structure Same (A : Ends H n) (B : Ends H m) : Prop where
  count : n=m
  src : ∀i,B.src (Fin.cast count i)=A.src i
  dst : ∀i,B.dst (Fin.cast count i)=A.dst i

omit [DecidableEq H] in
theorem Same.eq_same {B : Ends H n} (T : Same A B) : A=B := by
  cases A with | mk asrc adst =>
    cases B with | mk bsrc bdst =>
      congr 1
      · funext i;exact (T.src i).symm
      · funext i;exact (T.dst i).symm

theorem Same.peer_at (T : Same A B) (h : H) (a : Fin n) :
    B.peer h (Fin.cast T.count a)=A.peer h a := by simp [peer,T.src,T.dst]

theorem Same.wire_at (T : Same A B) (h : H) (a : Fin n) :
    B.serial h (B.peer h (Fin.cast T.count a)) (Fin.cast T.count a)=A.serial h (A.peer h a) a := by
  obtain rfl : n=m:=T.count
  obtain rfl:=T.eq_same
  rfl

theorem Same.place_at (T : Same A B) (fa : ∀h,(A.incident h).card≤cap) (fb : ∀h,(B.incident h).card≤cap)
    (h : H) (a : ↥(A.incident h)) (b : ↥(B.incident h)) (eqn : b.val=Fin.cast T.count a.val) :
    B.position fb h b=A.position fa h a := by
  obtain rfl : n=m:=T.count
  obtain rfl:=T.eq_same
  obtain rfl : b=a:=Subtype.ext eqn
  rfl

theorem Same.neighbor_at (T : Same A B) (roster : H→Finset H) (names:H↪ℕ)
    (sa : ∀h,(roster h).card≤D) (sb : ∀h,(roster h).card≤D)
    (ca : ∀i,A.dst i∈roster (A.src i) ∧ A.src i∈roster (A.dst i))
    (cb : ∀i,B.dst i∈roster (B.src i) ∧ B.src i∈roster (B.dst i))
    (h : H) (a : ↥(A.incident h)) (b : ↥(B.incident h)) (eqn : b.val=Fin.cast T.count a.val) :
    (B.neighbors roster names sb cb).slot h b=(A.neighbors roster names sa ca).slot h a := by
  obtain rfl : n=m:=T.count
  obtain rfl:=T.eq_same
  obtain rfl : b=a:=Subtype.ext eqn
  rfl

end
end Hierarchy.DescentSharedCableNames.Ends

end OAI
