import OAI.Computability.NearSquareRoot.InterchangeCenterBudget
import OAI.Computability.NearSquareRoot.InterchangeCenterBody

/-! # One bounded command for the entire centered field interchange

The spectral program swaps the selected middle ranks at the smaller row
volume. The following program then swaps the two outer reserve strips on the
full stream, parking only its remaining request headers on those descents.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OuterReserves

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom InterchangeAddress InterchangeBatch InterchangeSpace

/-- Both families use the same recursive request type, command, and parent
environment. The maximum for the full-volume family includes the physical
forest of remaining headers. Its data bound has no parked parent array. -/
theorem bounded_center {I : Type} {r : Regime I} {b : ℕ} [NeZero b]
    (a m : ℕ) (P G B : I → Dims.Tape) (f l : I → ℕ) (good : I → Tree → Prop)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (v : (i : I) → domain (J:=Slots a m) (b:=b) P G B f i → Tree)
    (hv : Manifest _ l v) (hgood : ∀ i k, good i (v i k))
    (zone : I → Request b → Prop) (limit : ℤ)
    (middle : BHop (Request.job b) r (countRows (b:=b) (Equiv.refl (Slots a m)) P G B f) l zone limit
      (together r.header (stackRun (layoutRows (Equiv.refl _) P G B f) v))
      (stackRun (layoutRows (Equiv.refl _) P G B f)
        (fun i => v i ∘ InterchangeSpectralFibre.swapMain (main a m)))) :
    ∃ small full : I → List (Request b),
      (∀ i q, q ∈ small i → zone i q) ∧ (∀ i, (small i).length ≤ limit) ∧
      (∀ i, (full i).length = 2*a) ∧
      (∀ i q, q ∈ full i →
        (allowed f (countRows (b:=b) (Equiv.refl (Slots a m)) P G B f) l i q ∧
          ∀ k, good i (q.contents k)) ∧ inherited b (P i) (G i) (B i) q) ∧
      CenterBody r (countRows (b:=b) (Equiv.refl (Slots a m)) P G B f) l
        (Request.job b) small full (fun i => (headers Request.header (full i)).count)
        (together r.header (stackRun (layoutRows (Equiv.refl _) P G B f) v))
        (stackRun (layoutRows (Equiv.refl _) P G B f) (fun i => v i ∘ swapper _ _ _)) := by
  let order := Equiv.refl (Slots a m)
  let rows := layoutRows (b:=b) order P G B f
  let N := countRows (b:=b) order P G B f
  let present (i : I) := v i ∘ InterchangeSpectralFibre.swapMain (main a m)
  let source := stackRun rows present
  let target := stackRun rows (fun i => v i ∘ swapper _ _ _)
  have st := layoutRows_station (b:=b) order P G B f hb hf hp hg hs
  have atStart := hv.lives st
  have atEnd := (hv.shift (fun _ => InterchangeSpectralFibre.swapMain (main a m))).lives st
  obtain ⟨small, childZone, countSmall, smaller⟩ := (middle.keep_header st.1 atStart atEnd).safe
  obtain ⟨C, bound⟩ := hv.size
  let strong (i : I) (t : Tree) := good i t ∧ t.count ≤ C*(l i+1)
  have valid (i : I) (k) : strong i (present i k) := ⟨hgood i _,bound i _⟩
  obtain ⟨full, countFull, child, tags, linked⟩ := full_volume_schedule a m P G B f l strong hb hf hp hg hs
    present valid
  refine ⟨small, full, childZone, countSmall, countFull, fun i q hq =>
    ⟨⟨(child i q hq).1.1, fun k => ((child i q hq).1.2 k).1⟩,(child i q hq).2⟩, ?_⟩
  have chains (i : I) : Chain Request.payload (Request.job b).reply (source i) (full i) (target i) := by
    have eq : present i ∘ swapOuter = v i ∘ swapper _ _ _ :=
      funext fun k => congrArg (v i) (complete k).1
    simpa only [target,source,rows,order,stackRun,eq] using linked i
  let capacity (i : I) := N i * (C*(l i+1)+1)+1
  have fits (i : I) (data : domain (J:=Slots a m) (b:=b) P G B f i → Tree)
      (hd : ∀ k, (data k).count ≤ C*(l i+1)) : (stripe (rows i) data).count ≤ capacity i :=
    stripe_size (rows i) data _ hd
  have starts (i : I) : (source i).count ≤ capacity i := fits i (present i) (fun k => bound i _)
  have ends (i : I) : (target i).count ≤ capacity i := fits i _ (fun k => bound i _)
  have during (i : I) (q : Request b) (hq : q ∈ full i) : q.payload.count ≤ capacity i := by
    obtain ⟨⟨_,size,_⟩,ok⟩ := (child i q hq).1
    change q.payload.count ≤ N i * (C*(l i+1)+1)+1
    change q.rows.count = N i at size
    rw [← size]
    exact stripe_size q.rows q.contents _ (fun k => (ok k).2)
  exact CenterBody.of_batch Request.header Request.payload (fun _ => rfl) source capacity
    smaller tags chains during ends (center_local_cost Request.header full source capacity st.1 tags
      starts (C+2) (record_capacity r N l C))

end OuterReserves

end NearSquareRoot
end Computability
end OAI
