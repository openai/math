import OAI.Computability.BorderVNP.CubeScatterPacket

/-! # Recovering owned private choices from an actual packet return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM DiagonalResidueRAM Tally

variable {w n b h K s : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- At fixed, valid decoded keys the returning native traces are exactly the realizations of
the physical packet's fixed source modes. All operand loads and branches before the realization
are forced. -/
theorem scatterPacket_iff (u : Selector n K h) (i : Fin (n+1)) (owner : Bool)
    (r : Bank w) (m : Memory w) (one : r 59 = 1) (key : r 43 = word w (selectorOrder n K h u).val)
    (place : r 44 = word w (2^i.val)) (side : r 45 = wordBit w owner)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w)
    {es t mt} :
    Runs pub mac (scatterPacket n b h K s) r m es t mt ↔
      ∃ ds : List Digit, ds.map Digit.mode = bodyModes b s u i owner ∧
        let e := result ds (Function.update r (58 : Reg) 0) m
        es = List.replicate (dispatchTicks (selectorOrder n K h u) i owner) (tick w) ++ e.trace ∧
          t = e.bank ∧ mt = e.mem := by
  rw [scatterPacket,dispatch_iff _ _ _ one fit]
  let k := selectorOrder n K h u
  have keyfit (k' : Fin (Fintype.card (Selector n K h))) : k'.val < 2^w :=
    k'.isLt.trans ((le_max_left ..).trans_lt fit)
  have ifit (i' : Fin (n+1)) : 2^i'.val < 2^w :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) i'.isLt.le).trans_lt ((le_max_right ..).trans_lt fit)
  have ofit (bit : Bool) : bit.toNat < 2^w :=
    bit.toNat_le.trans_lt ((Nat.one_le_pow (n+1) 2 (by decide)).trans_lt ((le_max_right ..).trans_lt fit))
  constructor
  · rintro ⟨k',i',bit,hk,hi,hbit,fs,rfl,hr⟩
    have ek : k' = k := by
      apply Fin.ext
      simpa only [word_val _ _ (keyfit k'),word_val _ _ (keyfit k)] using congrArg Fin.val (hk.symm.trans (show r 43 = word w k.val from key))
    have ei : i' = i := by
      apply Fin.ext
      apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
      simpa only [word_val _ _ (ifit i'),word_val _ _ (ifit i)] using congrArg Fin.val (hi.symm.trans place)
    have eo : bit = owner := by
      have val := congrArg Fin.val (hbit.symm.trans side)
      change (word w bit.toNat).val = (word w owner.toNat).val at val
      rw [word_val _ _ (ofit bit),word_val _ _ (ofit owner)] at val
      cases bit <;> cases owner <;> simp_all
    subst k'
    subst i'
    subst bit
    rw [show (selectorOrder n K h).symm k = u from Equiv.symm_apply_apply ..] at hr
    obtain ⟨ds,hm,htr,ht,hm'⟩ := program_run_inv _ hr
    exact ⟨ds,hm,congrArg (_++·) htr,ht,hm'⟩
  · rintro ⟨ds,hm,rfl,rfl,rfl⟩
    refine ⟨k,i,owner,key,place,side,_,rfl,?_⟩
    simpa only [k,Equiv.symm_apply_apply,hm] using
      program_run pub mac ds (Function.update r (58 : Reg) 0) m

/-- The entire native realization, including every chronological probe and local guess,
is unique for a prescribed stream of private bits. -/
theorem scatterPacket_unique {u : Selector n K h} {i : Fin (n+1)} {owner : Bool} {r : Bank w} {m : Memory w}
    (one : r 59 = 1) (key : r 43 = word w (selectorOrder n K h u).val)
    (place : r 44 = word w (2^i.val)) (side : r 45 = wordBit w owner)
    (fit : max (Fintype.card (Selector n K h)) (2^(n+1)) < 2^w) {es fs t t' mt mt'}
    (run : Runs pub mac (scatterPacket n b h K s) r m es t mt)
    (run' : Runs pub mac (scatterPacket n b h K s) r m fs t' mt')
    (eq : es.flatMap TeamRAM.Event.choices = fs.flatMap TeamRAM.Event.choices) :
    es = fs ∧ t = t' ∧ mt = mt' := by
  obtain ⟨ds,hm,rfl,rfl,rfl⟩ := (scatterPacket_iff u i owner r m one key place side fit).mp run
  obtain ⟨xs,hx,rfl,rfl,rfl⟩ := (scatterPacket_iff u i owner r m one key place side fit).mp run'
  have hds := (result_trace ds (Function.update r (58 : Reg) 0) m).1.2.1
  have hxs := (result_trace xs (Function.update r (58 : Reg) 0) m).1.2.1
  simp only [List.flatMap_append,List.append_cancel_left_eq,hds,hxs] at eq
  obtain rfl := choices_injective (hm.trans hx.symm) eq
  exact ⟨rfl,rfl,rfl⟩

end Cube.Scatter

end BorderVNP
end Computability
end OAI
