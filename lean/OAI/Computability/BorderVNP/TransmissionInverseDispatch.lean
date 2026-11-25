import OAI.Computability.BorderVNP.TransmissionChoiceScan

/-! # Exact effects and chronological choices of a sparse transmission dispatch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

/-- A skipped payload emits no guesses. An active payload emits its role's choice word. -/
def optionBits (role : Option Role) (k : ℕ) (bits : ℕ → Bool) : List Bool :=
  role.elim [] fun mode => mode.prefixBits k bits

/-- Exact choices in the forward dispatch of a permitted role. -/
theorem Decision.run_bits {D : Decision} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bits : ℕ → Bool) {role : Option Role}
    (hrole : D.role s = some role) (h1 : s 1 = 1) (h0 : s 16 = 0)
    (ok : Ready role pub s m bits) :
    ∃ es t, Runs pub macros D.code s m es t (finishedMemory role pub s m bits) ∧
      es.flatMap TeamRAM.Event.choices = optionBits role (s 11).val bits ∧
      (∀ i : Reg, i.val < 16 → t i = s i) ∧ traceCost es ≤ D.depth + payloadCost role (s 11).val + 1 := by
  induction D with
  | invalid => cases hrole
  | skip => cases hrole; exact ⟨_,_,Runs.localStep _ rfl rfl,rfl,fun _ _ => rfl,le_rfl⟩
  | active mode =>
    cases hrole
    obtain ⟨es,t,r,hb,hl,hc⟩ := scan_runs_bits mode pub macros s m bits h1 h0 ok
    exact ⟨es,t,r,hb,fun i hi => (hl i hi.le).trans
      (Function.update_of_ne (fun he => by subst i; omega) ..),by simpa [Decision.depth,payloadCost] using hc⟩
  | test x y a b iha ihb =>
    by_cases eq : s x = s y
    · obtain ⟨es,t,r,bs,hl,hc⟩ := iha (by simpa [Decision.role,eq] using hrole)
      refine ⟨_,t,.ifEq (by rw [ite_eq_left eq]; exact r), by simpa [tick] using bs, hl, ?_⟩
      change 1 + traceCost es ≤ 1 + max a.depth b.depth + _ + 1
      omega
    · obtain ⟨es,t,r,bs,hl,hc⟩ := ihb (by simpa [Decision.role,eq] using hrole)
      refine ⟨_,t,.ifEq (by rw [ite_eq_right eq]; exact r), by simpa [tick] using bs, hl, ?_⟩
      change 1 + traceCost es ≤ 1 + max a.depth b.depth + _ + 1
      omega

/-- Every returning dispatch selected a valid role. Its chronological choice word gives
the local assignment, and each source comparison in its actual scan succeeded. -/
theorem Decision.sound (D : Decision) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (h1 : s 1 = 1) (h0 : s 16 = 0)
    (safe : ∀ mode, D.role s = some (some mode) → SafeScan mode pub s m)
    {es t mt} (r : Runs pub macros D.code s m es t mt) :
    ∃ role : Option Role, ∃ bits : ℕ → Bool, D.role s = some role ∧
      Ready role pub s m bits ∧ mt = finishedMemory role pub s m bits ∧
      es.flatMap TeamRAM.Event.choices = optionBits role (s 11).val bits ∧
      (∀ i : Reg, i.val < 16 → t i = s i) ∧ traceCost es ≤ D.depth + payloadCost role (s 11).val + 1 := by
  induction D generalizing es t mt with
  | invalid => cases r with | atom ha => cases ha
  | skip =>
    have canon : Runs pub macros .nop s m [tick w] s m := Runs.localStep _ rfl rfl
    obtain ⟨rfl,rfl,rfl⟩ := canon.unique_of_deterministic (by decide) r
    exact ⟨none,fun _ => false,rfl,(fun _ h => by cases h),rfl,rfl,fun _ _ => rfl,le_rfl⟩
  | active mode =>
    obtain ⟨bits,hb,hm,hl,ok⟩ := scan_sound mode pub macros s m h1 h0 (safe mode rfl) r
    obtain ⟨fs,u,forward,fb,_,ct⟩ := scan_runs_bits mode pub macros s m bits h1 h0 ok
    have hb' : fs.flatMap TeamRAM.Event.choices ++ [] = es.flatMap TeamRAM.Event.choices ++ [] := by rw [hb,fb]
    have tag : ∀ i, (scan mode.bitCode).program.tag i = .native := by cases mode <;> decide
    have eq := (DiagonalResidueRAM.unique_returns tag forward r hb').1
    refine ⟨some mode,bits,rfl,ok,hm,hb,fun i hi => ?_,by simpa [Decision.depth,payloadCost,← eq] using ct⟩
    exact (hl i hi.le).trans (Function.update_of_ne (fun he => by subst i; omega) ..)
  | test x y a b iha ihb =>
    change Runs _ _ (.ifEq x y a.code b.code) _ _ _ _ _ at r
    cases r with
    | atom ha => cases ha
    | @ifEq _ _ _ _ _ _ fs _ _ hr =>
      by_cases he : s x = s y
      · rw [ite_eq_left he] at hr
        obtain ⟨role,bits,sel,ok,hm,bs,hl,ct⟩ := iha
          (fun mode h => safe mode (by simpa [Decision.role,he] using h)) hr
        refine ⟨role,bits,by simpa [Decision.role,he] using sel,ok,hm,by simpa [tick] using bs,hl,?_⟩
        change 1+traceCost fs ≤ 1+max a.depth b.depth+_+1
        omega
      · rw [ite_eq_right he] at hr
        obtain ⟨role,bits,sel,ok,hm,bs,hl,ct⟩ := ihb
          (fun mode h => safe mode (by simpa [Decision.role,he] using h)) hr
        refine ⟨role,bits,by simpa [Decision.role,he] using sel,ok,hm,by simpa [tick] using bs,hl,?_⟩
        change 1+traceCost fs ≤ 1+max a.depth b.depth+_+1
        omega

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
