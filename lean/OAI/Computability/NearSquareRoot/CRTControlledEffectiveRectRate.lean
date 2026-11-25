import OAI.Computability.NearSquareRoot.NamedPackedRate
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveTemplate
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryInterface
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # Time and packed mass of the physical binary rectangle -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication Code Strip Strip.Dims Loom Adic NamedPacked InterchangeROMBinary

private theorem namedTime {X : Type} {c : Cmd} {t s : X → ℕ} {v w : X → Tree}
    (h : PhysicalWalsh.ClosedRuns c t s v w) : EffectiveTask.Runs c t v w :=
  command_contract c from Space.BoundedTask.forget (show Space.BoundedTask t s v w from ⟨c,h⟩)

private theorem charge_bound {X : Type} {r : Regime X} {N w l : X → ℕ} {a : X → Tree}
    (small : r.Small a) (len : ∀ x, w x ≤ l x) (D : ℕ) :
    ∃ d K : ℕ, ∀ x, (charge (N x) (w x) (a x).count D : ℝ) ≤ K * mass r N l d x := by
  obtain ⟨d,C,bound⟩ := ((small.extent.add (Dom.const r.scale 1)).pow D)
  refine ⟨d,C+1,fun x => ?_⟩
  have h : ((a x).count+1)^D ≤ C*(r.scale x+1)^d := bound x
  have le : w x + ((a x).count+1)^D ≤ (C+1)*(l x + (r.scale x+1)^d) := by
    specialize len x
    rw [Nat.succ_mul, Nat.mul_add]
    omega
  have final := Nat.mul_le_mul_left (N x) le
  rw [← Nat.mul_assoc,Nat.mul_comm (N x) (C+1),Nat.mul_assoc] at final
  unfold InterchangeROMBinary.charge mass
  exact_mod_cast final

/-- The canonical-header rectangle meets the packed stripe rate with the
very same tape program and arbitrary fixed-width bead payloads. -/
theorem native_beads {X : Type} {r : Regime X} {c : Cmd} {ρ : ℝ} {D : ℕ}
    (phys : RectPhysical c ρ D) (hρ : 0 ≤ ρ)
    (P G B : X → Tape) (n : X → ℕ)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (guard : ∀ x d, d ∈ P x ++ G x ++ B x → d ≤ Net.Shuttle.base)
    (l : X → ℕ) {T : X → Type} (u : (x : X) → Series (T x)) (len : ∀ x, (u x).count ≤ l x)
    (v : (x : X) → SpanKey (P x) (G x) (B x) (Block 2 (n x)) → T x → Bead) :
    let s x := stock 2 (P x) (G x) (B x) (n x)
    BreezeAt c (Spindle.modes n (τ := ρ)) r (fun x => (s x).count) l
      (together (fun x => header (n x) (P x) (G x) (B x)) (cloth s u v))
      (cloth s u fun x a => v x (swapper _ _ _ a)) := by
  let hdr x := header (n x) (P x) (G x) (B x)
  let s x := stock 2 (P x) (G x) (B x) (n x)
  let N x := (s x).count
  have headReady : r.Small hdr := hn.pair (hp.shape.pair (hg.shape.pair hb.shape))
  have one := terminal (p := 2) (by decide) n hn
  have st : Station r s := hp.station.product (one.product (hg.station.product (one.product hb.station)))
  have prep : Rip r N l (together r.header (cloth s u v)) (together hdr (cloth s u v)) :=
    (Rip.header st.1 headReady).left (cloth_size s u st v len)
  have solid (x : X) (d : ℕ) (hd : d ∈ P x ++ G x ++ B x) : 2 ≤ d ∧ d ≤ Net.Shuttle.base := by
    refine ⟨?_,guard x d hd⟩
    simp only [List.mem_append] at hd
    rcases hd with (h|h)|h
    · exact hp.solid x d h
    · exact hg.solid x d h
    · exact hb.solid x d h
  have executes := namedTime (phys.beads n P G B solid u v)
  obtain ⟨d,C,cb⟩ := charge_bound (N := N) headReady len D
  obtain ⟨b,start⟩ := prep
  let E := max d b
  let f := Spindle.modes n (τ := ρ)
  have pos := Spindle.belly n hρ
  have leM (x : X) : mass r N l b x ≤ runrate f r N l E x :=
    (mass_le (r := r) (n := N) (l := l) (le_max_right d b) x).trans
      (le_mul_of_one_le_right (by unfold mass; positivity) (pos x))
  have room := (start.larger leM).out
  refine ⟨pos,E,⟨(fun x => (unit_mass st.1 b x).trans (leM x)),⟨_,executes,C+2,?_⟩,room⟩⟩
  intro x
  let M := charge (N x) (u x).count (hdr x).count D
  let p := f x
  have pe : 0 ≤ p := (by linarith [pos x] : (0:ℝ) ≤ f x)
  have step : (M:ℝ) * p ≤ C * runrate f r N l E x := by
    change (M:ℝ) * p ≤ C * (mass r N l E x * p)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((cb x).trans (mul_le_mul_of_nonneg_left
      (mass_le (le_max_left d b) x) (Nat.cast_nonneg _))) pe
  have ce := Nat.ceil_lt_add_one (show 0 ≤ (M:ℝ)*p from mul_nonneg (Nat.cast_nonneg _) pe)
  have unit := (unit_mass st.1 b x).trans (leM x)
  change (⌈(M:ℝ)*p⌉₊:ℝ)+1 ≤ ((C+2:ℕ):ℝ) * runrate f r N l E x
  push_cast
  linarith

end Controlled

end NearSquareRoot
end Computability
end OAI
