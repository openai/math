import OAI.Computability.VPVNP.RAMTapeAddressLogControl

/-!
# Exact runs for private-log comparison and restoration
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

/-- Compare exactly one complete key, saving both bit streams. -/
theorem keyRuns (eq : Bool) (qbits kbits tail : List Bool) (s : Bank)
    (hlen : qbits.length = kbits.length) :
    StackRuns loadCode (4 * qbits.length + 1) (.key eq)
      ({s with q := qbits, ks := kbits ++ tail} : Bank).stacks (.value (eq && (qbits == kbits)))
      ({s with q := [], ks := tail, sq := qbits.reverse ++ s.sq, sk := kbits.reverse ++ s.sk} : Bank).stacks := by
  induction qbits generalizing eq kbits s with
  | nil =>
    have hk : kbits = [] := List.length_eq_zero_iff.mp hlen.symm
    subst kbits
    simp only [List.nil_append, List.reverse_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
      beq_self_eq_true, Bool.and_true]
    exact .cons (stepPop _ (show loadCode (.key eq) = _ from rfl)) (.nil ..)
  | cons b bs ih =>
    cases kbits with
    | nil => simp at hlen
    | cons d ds =>
      let st : Bank := {s with sq := b :: s.sq, sk := d :: s.sk}
      have rest := ih (eq && (b == d)) ds st (Nat.succ.inj hlen)
      have first :
          StackRuns loadCode (4 * bs.length + 1 + 1 + 1 + 1 + 1) (.key eq)
            ({s with q := b :: bs, ks := d :: (ds ++ tail)} : Bank).stacks
            (.value ((eq && (b == d)) && (bs == ds)))
            ({st with q := [], ks := tail, sq := bs.reverse ++ st.sq, sk := ds.reverse ++ st.sk} : Bank).stacks :=
        .cons (stepPop _ (show loadCode (.key eq) = _ from rfl))
          (.cons (stepPush _ (show loadCode (.saveQ eq b) = _ from rfl))
            (.cons (stepPop _ (show loadCode (.getK eq b) = _ from rfl))
              (.cons (stepPush _ (show loadCode (.saveK (eq && (b == d)) d) = _ from rfl)) rest)))
      simpa [st, List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_assoc,
        Bool.and_assoc, List.beq_cons_cons] using first

private def Rewind.pair (ph : Rewind) (s : Bank) (x y : List Bool) : Bank :=
  (s.set ph.src x).set ph.dst y

private theorem pair_src (ph : Rewind) (s : Bank) (x y : List Bool) :
    (ph.pair s x y).stacks ph.src = x := by cases ph <;> rfl

private theorem pair_dst (ph : Rewind) (s : Bank) (x y : List Bool) :
    (ph.pair s x y).stacks ph.dst = y := by cases ph <;> rfl

private theorem set_src (ph : Rewind) (s : Bank) (x y z : List Bool) :
    (ph.pair s x y).set ph.src z = ph.pair s z y := by cases ph <;> rfl

private theorem set_dst (ph : Rewind) (s : Bank) (x y z : List Bool) :
    (ph.pair s x y).set ph.dst z = ph.pair s x z := by cases ph <;> rfl

private theorem rewindPair (ph : Rewind) (s : Bank) (x y : List Bool) :
    StackRuns loadCode (2 * x.length + 1) (.rewind ph) (ph.pair s x y).stacks
      ph.next (ph.pair s [] (x.reverse ++ y)).stacks := by
  induction x generalizing y with
  | nil =>
    have h := stepPop (ph.pair s [] y) (show loadCode (.rewind ph) = _ from rfl)
    rw [pair_src, set_src] at h
    exact .cons h (.nil ..)
  | cons b bs ih =>
    have h := stepPop (ph.pair s (b :: bs) y) (show loadCode (.rewind ph) = _ from rfl)
    rw [pair_src, set_src] at h
    have hp := stepPush (ph.pair s bs y) (show loadCode (.put ph b) = _ from rfl)
    rw [pair_dst, set_dst] at hp
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.mul_succ, Nat.add_assoc] using StackRuns.cons h (.cons hp (ih (b :: y)))

/-- Consume a saved stream and prepend its reverse to the corresponding live stream. -/
theorem rewindRuns (ph : Rewind) (s : Bank) :
    StackRuns loadCode (2 * (s.stacks ph.src).length + 1) (.rewind ph) s.stacks
      ph.next ((s.set ph.src []).set ph.dst ((s.stacks ph.src).reverse ++ s.stacks ph.dst)).stacks := by
  have h := rewindPair ph s (s.stacks ph.src) (s.stacks ph.dst)
  have he : ph.pair s (s.stacks ph.src) (s.stacks ph.dst) = s := by cases ph <;> rfl
  rwa [he] at h

/-- Produce one zero bit per address bit on an unsuccessful search. -/
theorem zeroRuns (bits : List Bool) (s : Bank) :
    StackRuns loadCode (3 * bits.length + 1) .zero ({s with q := bits} : Bank).stacks
      (.rewind .query)
      ({s with q := [], sq := bits.reverse ++ s.sq, so := List.replicate bits.length false ++ s.so} : Bank).stacks := by
  induction bits generalizing s with
  | nil =>
    exact .cons (stepPop _ (show loadCode .zero = _ from rfl)) (.nil ..)
  | cons b bs ih =>
    let st : Bank := {s with sq := b :: s.sq, so := false :: s.so}
    have h : StackRuns loadCode (3 * bs.length + 1 + 1 + 1 + 1) .zero
        ({s with q := b :: bs} : Bank).stacks (.rewind .query)
        ({st with q := [], sq := bs.reverse ++ st.sq, so := List.replicate bs.length false ++ st.so} : Bank).stacks :=
      .cons (stepPop _ (show loadCode .zero = _ from rfl))
        (.cons (stepPush _ (show loadCode (.saveZeroQ b) = _ from rfl))
          (.cons (stepPush _ (show loadCode .emitZero = _ from rfl)) (ih st)))
    have rep : List.replicate bs.length false ++ false :: s.so =
        List.replicate (bs.length + 1) false ++ s.so := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    simpa only [st, rep, List.length_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, Nat.mul_succ, Nat.add_assoc] using h

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI
