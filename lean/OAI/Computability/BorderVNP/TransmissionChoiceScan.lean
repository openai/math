import OAI.Computability.BorderVNP.TransmissionInverseScan

/-! # Prescribed chronological choices in a returning native transmission scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open private output_sameRange from OAI.Computability.BorderVNP.TransmissionScan

variable {w : ℕ}

/-- One more bit appends precisely its possible private choice to the role's stream. -/
theorem Role.prefixBits_succ (mode : Role) (k : ℕ) (bits : ℕ → Bool) :
    mode.prefixBits (k+1) bits = mode.prefixBits k bits ++ mode.bits (bits k) := by
  by_cases h : mode = .sharedHere
  · simp only [Role.prefixBits, Role.bits, h, ite_true, List.ofFn_succ', List.concat_eq_append,
      Fin.val_last, Fin.val_castSucc]
  · simp [Role.prefixBits, Role.bits, h]

/-- For each permitted assignment, there is an actual returning scan with precisely
the assigned chronological choices, final memory, and endpoint cursor. -/
theorem scan_runs_bits (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bits : ℕ → Bool) (h1 : s 1 = 1) (h0 : s 16 = 0)
    (ok : Ready (some mode) pub s m bits) :
    ∃ es t, Runs pub macros (scan mode.bitCode) s m es t (rangeMemory mode pub s m bits (s 11).val) ∧
      es.flatMap TeamRAM.Event.choices = mode.prefixBits (s 11).val bits ∧
      sameRange (Function.update s 16 (s 11)) t ∧
      traceCost es ≤ (s 11).val*(mode.bitCode.slots+2)+1 := by
  let N := (s 11).val
  let bank (i : ℕ) := Function.update s 16 (Fin.ofNat _ i)
  let M := rangeMemory mode pub s m bits
  have go (k i : ℕ) (hi : i+k=N) (v : Bank w) (hv : sameRange (bank i) v) :
      ∃ es t, Runs pub macros (scan mode.bitCode) v (M i) es t (M N) ∧
        mode.prefixBits i bits ++ es.flatMap TeamRAM.Event.choices = mode.prefixBits N bits ∧
        sameRange (bank N) t ∧ traceCost es ≤ k*(mode.bitCode.slots+2)+1 := by
    induction k generalizing i v with
    | zero =>
      have e : i = N := by omega
      subst i
      have guard : ¬v 16 < v 11 := by
        change ¬(v 16).val < (v 11).val
        simp [hv 16 (by decide), hv 11 (by decide), bank, N]
      exact ⟨_,v,.whileDone guard,by simp [tick],hv,by simp only [Nat.zero_mul, Nat.zero_add]; exact le_rfl⟩
    | succ k ih =>
      have hlt : i<N := by omega
      have guard : v 16 < v 11 := by
        change (v 16).val < (v 11).val
        simpa only [hv 16 (by decide), hv 11 (by decide), bank, Function.update_self,
          Function.update_of_ne (by decide : (11 : Reg) ≠ 16), Fin.val_ofNat,
          Nat.mod_eq_of_lt (hlt.trans (s 11).isLt)] using hlt
      obtain ⟨es,u,r,bs,hu,ct⟩ := role_runs_bits mode pub macros v (M i) (bits i)
        (ok mode rfl i hlt v hv)
      let z := Function.update u 16 (u 16 + u 1)
      have hm : mode.output pub v (M i) (bits i) = M (i+1) := output_sameRange _ _ _ _ hv
      rw [hm] at r
      have inc : Runs pub macros (.binary .add 16 16 1) u (M (i+1)) [tick w] z (M (i+1)) :=
        Runs.localStep _ rfl rfl
      have hz : sameRange (bank (i+1)) z := by
        intro j hj
        by_cases he : j=16
        · subst j
          simp only [z, bank, Function.update_self, hu 16 (by decide), hu 1 (by decide),
            hv 16 (by decide), hv 1 (by decide), Function.update_of_ne (by decide : (1 : Reg) ≠ 16), h1]
          exact Fin.ext (Nat.add_mod ..).symm
        · simp only [z, bank, Function.update_of_ne he, hu j hj, hv j hj]
      obtain ⟨fs,t,rr,bf,ht,cf⟩ := ih (i+1) (by omega) z hz
      refine ⟨_, t, Runs.whileStep guard (r.seq inc) rr, ?_, ht, ?_⟩
      · simpa only [tick, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.nil_append,
          List.append_nil, bs, Role.prefixBits_succ, List.append_assoc] using bf
      · change 1+traceCost ((es++[tick w])++fs) ≤ _
        rw [cost_append, cost_append, Nat.succ_mul]
        change 1+(traceCost es+1+traceCost fs) ≤ _
        omega
  have init : sameRange (bank 0) s := fun j _ => by by_cases he : j=16 <;> simp [bank, he, h0]
  obtain ⟨es,t,rr,bs,ht,ct⟩ := go N 0 (by omega) s init
  refine ⟨es,t,rr, ?_, ?_,ct⟩
  · have e : mode.prefixBits 0 bits = [] := by simp [Role.prefixBits]
    simpa only [e, List.nil_append] using bs
  · simpa only [bank,N,Fin.ofNat_val_eq_self] using ht

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
