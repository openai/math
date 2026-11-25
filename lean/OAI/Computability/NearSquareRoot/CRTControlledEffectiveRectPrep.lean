import OAI.Computability.NearSquareRoot.CRTControlledEffectiveTemplate
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryInterface

/-! # A fixed rectangle-header prelude for arbitrary data streams

Only the represented geometry determines the prelude. The record family, its
width bound, and the physical interchange implementation are supplied later.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace NamedPacked

open IntegerMultiplication Code Strip KernelEffectiveFamily

theorem CarriesAt.left {X : Type} {a : X → ℝ} {u v h : X → Tree} {c : Cmd}
    (run : CarriesAt c a u v) (park : Volume a h) :
    CarriesAt (leftCmd c) a (together u h) (together v h) := by
  obtain ⟨t,r,C,b⟩ := run.work
  exact ⟨run.budget,⟨t,command_contract (leftCmd c) from (show Task t u v from ⟨c,r⟩).left h,C,b⟩,
    Volume.fork run.small park run.budget⟩

theorem BreezeAt.left {X : Type} {a : X → ℝ} {r : Regime X} {n l : X → ℕ} {u v h : X → Tree} {c : Cmd}
    (run : BreezeAt c a r n l u v) (park : Alive r n l h) :
    BreezeAt (leftCmd c) a r n l (together u h) (together v h) := by
  obtain ⟨pos,m,go⟩ := run
  obtain ⟨d,stay⟩ := park
  have le (x : X) : mass r n l d x ≤ runrate a r n l (m+d) x :=
    (mass_le (show d ≤ m+d by omega) x).trans (le_mul_of_one_le_right (by unfold mass; positivity) (pos x))
  refine ⟨pos,m+d,(go.larger fun x => rate_higher x (pos x) (show m ≤ m+d by omega)).left ?_⟩
  exact (stay.larger le).small

end NamedPacked

namespace Controlled.Effective

open IntegerMultiplication Code Strip Strip.Dims Loom Adic NamedPacked InterchangeROMBinary KernelEffectiveFamily

theorem prepareRect {X : Type} {r : Regime X} (P G B : X → Tape) (n : X → ℕ)
    (hn : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B) :
    ∃ pre : Cmd, ∀ (l : X → ℕ) {T : X → Type} (u : (x : X) → Series (T x)), (∀ x, (u x).count ≤ l x) →
      ∀ (v : (x : X) → SpanKey (P x) (G x) (B x) (Block 2 (n x)) → T x → Bead)
        (ρ : ℝ), 0 ≤ ρ →
      let s x := stock 2 (P x) (G x) (B x) (n x)
      BreezeAt pre (Spindle.modes n (τ := ρ)) r (fun x => (s x).count) l
        (together r.header (cloth s u v))
        (together (fun x => header (n x) (P x) (G x) (B x)) (cloth s u v)) := by
  let hdr x := header (n x) (P x) (G x) (B x)
  have ready : r.Small hdr := hn.pair (hp.shape.pair (hg.shape.pair hb.shape))
  have rsmall : Rip r (fun _ => 1) (fun _ => 0) r.header hdr := Rip.header (fun _ => le_rfl) ready
  obtain ⟨d,work⟩ := rsmall
  obtain ⟨prep,raw⟩ := CarriesAt.exists_of_carries work
  refine ⟨leftCmd prep,fun l T u len v ρ hρ => ?_⟩
  let s x := stock 2 (P x) (G x) (B x) (n x)
  let N x := (s x).count
  have one := terminal (p := 2) (by decide) n hn
  have st : Station r s := hp.station.product (one.product (hg.station.product (one.product hb.station)))
  have pos := Spindle.belly n hρ
  apply BreezeAt.left (h := cloth s u v) _ (cloth_size s u st v len)
  refine ⟨pos,d,raw.larger fun x => ?_⟩
  have size : mass r (fun _ => 1) (fun _ => 0) d x ≤ mass r N l d x := by
    have Npos : (1:ℝ) ≤ N x := by exact_mod_cast st.1 x
    have hs : (0:ℝ) ≤ (r.scale x+1:ℝ)^d := by positivity
    simp only [mass,Nat.cast_one,Nat.cast_zero,zero_add,one_mul]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg (l x))).trans
      (le_mul_of_one_le_left (by positivity) Npos)
  exact size.trans (le_mul_of_one_le_right (by unfold mass; positivity) (pos x))

end Controlled.Effective

end NearSquareRoot
end Computability
end OAI
