import OAI.Computability.BorderVNP.TransmissionInverseBit
import OAI.Computability.BorderVNP.TransmissionDispatch

/-! # Recovering the actual local choices and sender checks of a full bit scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A loop invariant carrying the chronological binary choice stream. -/
theorem Runs.while_choices_invariant {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt)
    (cursor bound : Reg) (body : Code) (Inv : List Bool → Bank w → Memory w → Prop)
    (step : ∀ {bs s m es t mt}, Inv bs s m → s cursor < s bound →
      Runs pub macros body s m es t mt → Inv (bs ++ es.flatMap TeamRAM.Event.choices) t mt)
    (same : c = .whileLt cursor bound body) (bs : List Bool) (init : Inv bs s m) :
    Inv (bs ++ es.flatMap TeamRAM.Event.choices) t mt ∧ ¬t cursor < t bound := by
  induction run generalizing bs with
  | atom ha _ _ => subst same; cases ha
  | seq | ifEq | ifLt | choose => contradiction
  | whileDone hg => cases same; exact ⟨by simpa [tick] using init, hg⟩
  | whileStep hg r _ _ ih =>
    cases same
    simpa [tick, List.append_assoc] using ih rfl _ (step init hg r)

namespace Transmission

open private output_sameRange from OAI.Computability.BorderVNP.TransmissionScan

variable {w : ℕ}

/-- The trace word for the first `k` positions of a role, empty at nonlocal roles. -/
def Role.prefixBits (mode : Role) (k : ℕ) (bits : ℕ → Bool) : List Bool :=
  if mode = .sharedHere then List.ofFn (fun i : Fin k => bits i.val) else []

/-- Choices beyond a prefix do not affect that prefix's actual memory. -/
theorem rangeMemory_congr (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w)
    {a b : ℕ → Bool} {k : ℕ} (h : ∀ i < k, a i = b i) :
    rangeMemory mode pub s m a k = rangeMemory mode pub s m b k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rangeMemory, h k (by omega), ih (fun i hi => h i (by omega))]

private theorem prefixBits_update (mode : Role) (k : ℕ) (a : ℕ → Bool) (v : Bool) :
    mode.prefixBits k a ++ mode.bits v = mode.prefixBits (k+1) (Function.update a k v) := by
  by_cases h : mode = .sharedHere
  · simp only [Role.prefixBits, Role.bits, h, ite_true, List.ofFn_succ', List.concat_eq_append,
      Fin.val_last, Fin.val_castSucc, Function.update_self]
    congr 2
    funext i
    exact (Function.update_of_ne (Nat.ne_of_lt i.isLt) ..).symm
  · simp [Role.prefixBits, Role.bits, h]

private theorem permits_congr (mode : Role) (pub : Arg → Word w) {s t : Bank w} {m : Memory w}
    (h : sameRange s t) (safe : mode.addressSafe pub t m) (ok : mode.permits pub s m) :
    mode.permits pub t m := by
  cases mode with
  | sendData =>
    refine ⟨safe, ?_⟩
    have eq := ok.2
    simpa only [endpointNat_eq, h 10 (by decide), h 12 (by decide), h 15 (by decide), h 16 (by decide)]
      using eq
  | sharedHere | dataHere | receiveA | receiveB => exact safe

/-- All endpoint arithmetic stays in range on each possible guessed prefix. This
assumption does not require any source/link equality. -/
def SafeScan (mode : Role) (pub : Arg → Word w) (s : Bank w) (m : Memory w) : Prop :=
  ∀ bits : ℕ → Bool, ∀ j < (s 11).val, ∀ t,
    sameRange (Function.update s 16 (Fin.ofNat _ j)) t →
    mode.addressSafe pub t (rangeMemory mode pub s m bits j)

/-- Every returning scan has the precise memory and guess effects of a permitted
role assignment. The guard's exit also fixes the final offset exactly. -/
theorem scan_sound (mode : Role) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (h1 : s 1 = 1) (h0 : s 16 = 0) (safe : SafeScan mode pub s m)
    {es t mt} (r : Runs pub macros (scan mode.bitCode) s m es t mt) :
    ∃ bits : ℕ → Bool, es.flatMap TeamRAM.Event.choices = mode.prefixBits (s 11).val bits ∧
      mt = rangeMemory mode pub s m bits (s 11).val ∧ sameRange (Function.update s 16 (s 11)) t ∧
      Ready (some mode) pub s m bits := by
  let N := (s 11).val
  let bank (i : ℕ) := Function.update s 16 (Fin.ofNat _ i)
  let mem (bits : ℕ → Bool) (i : ℕ) := rangeMemory mode pub s m bits i
  let Inv (bs : List Bool) (t : Bank w) (mt : Memory w) :=
    ∃ i ≤ N, ∃ bits : ℕ → Bool, bs = mode.prefixBits i bits ∧
      sameRange (bank i) t ∧ mt = mem bits i ∧
      ∀ j < i, ∀ v, sameRange (bank j) v → mode.permits pub v (mem bits j)
  have cursor {i : ℕ} {v : Bank w} (hi : i ≤ N) (hv : sameRange (bank i) v) :
      (v 16).val = i ∧ (v 11).val = N := by
    have hfit := hi.trans_lt (s 11).isLt
    simp only [hv 16 (by decide), hv 11 (by decide), bank, N, Function.update_self,
      Function.update_of_ne (by decide : (11 : Reg) ≠ 16), Fin.val_ofNat, Nat.mod_eq_of_lt hfit, and_self]
  have step {bs v mv fs z mz} (init : Inv bs v mv) (guard : v 16 < v 11)
      (hr : Runs pub macros (.seq mode.bitCode (.binary .add 16 16 1)) v mv fs z mz) :
      Inv (bs ++ fs.flatMap TeamRAM.Event.choices) z mz := by
    obtain ⟨i, hi, bits, rfl, hv, rfl, hprev⟩ := init
    have hlt : i < N := by
      change (v 16).val < (v 11).val at guard
      simpa [(cursor hi hv).1,(cursor hi hv).2] using guard
    cases hr with
    | atom ha => cases ha
    | @seq _ _ _ _ gs u mu hs _ _ rbit rinc =>
      let b := (gs.flatMap TeamRAM.Event.choices).headD false
      let bits' := Function.update bits i b
      obtain ⟨hperm, hmem, hbits, hu, _⟩ := role_sound mode pub macros v _ (safe bits i hlt v hv) rbit
      change gs.flatMap TeamRAM.Event.choices = mode.bits b at hbits
      have inc : Runs pub macros (.binary .add 16 16 1) u mu [tick w]
          (Function.update u 16 (u 16 + u 1)) mu := Runs.localStep _ rfl rfl
      obtain ⟨einc, ebank, emem⟩ := inc.unique_of_deterministic (by decide) rinc
      subst hs; subst z; subst mz
      have earlier {j : ℕ} (hj : j ≤ i) : mem bits' j = mem bits j :=
        rangeMemory_congr mode pub s m (fun k hk => Function.update_of_ne (by omega : k ≠ i) ..)
      refine ⟨i+1, hlt, bits', ?_, ?_, ?_, ?_⟩
      · simp only [List.flatMap_append, tick, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, hbits]
        exact prefixBits_update mode i bits b
      · intro j hj
        by_cases he : j = 16
        · subst j
          simp only [Function.update_self, hu 16 (by decide), hu 1 (by decide), hv 1 (by decide),
            hv 16 (by decide), bank, Function.update_self, Function.update_of_ne (by decide : (1 : Reg) ≠ 16), h1]
          exact Fin.ext (Nat.add_mod ..).symm
        · simp only [bank, Function.update_of_ne he, hu j hj, hv j hj]
      · change mu = mode.output pub (bank i) (mem bits' i) (bits' i)
        rw [earlier le_rfl, show bits' i = b from Function.update_self .., hmem]
        exact output_sameRange _ _ _ _ hv
      · intro j hj v' hv'
        have hji : j ≤ i := by omega
        rw [earlier hji]
        by_cases hji' : j = i
        · subst j
          apply permits_congr mode pub (fun k hk => (hv' k hk).trans (hv k hk).symm)
            (safe bits i hlt v' hv') hperm
        · exact hprev j (by omega) v' hv'
  have init : Inv [] s m := by
    refine ⟨0, Nat.zero_le _, fun _ => false, ?_, ?_, rfl, by simp⟩
    · simp [Role.prefixBits]
    · intro j _
      by_cases he : j=16 <;> simp [bank, he, h0]
  obtain ⟨⟨i,hi,bits,hbits,ht,rfl,perm⟩,exit⟩ :=
    r.while_choices_invariant 16 11 _ Inv step rfl [] init
  have hit : i = N := by
    change ¬(t 16).val < (t 11).val at exit
    rw [(cursor hi ht).1, (cursor hi ht).2] at exit
    omega
  subst i
  refine ⟨bits, by simpa using hbits, rfl, ?_, ?_⟩
  · simpa only [bank,N,Fin.ofNat_val_eq_self] using ht
  · intro other he
    cases he
    exact perm

end Transmission
end RoutingISA

end BorderVNP
end Computability
end OAI
