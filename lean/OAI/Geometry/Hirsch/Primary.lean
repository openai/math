import OAI.Geometry.Hirsch.Multiscale

noncomputable section

open Set Filter

namespace OAI.Geometry.Hirsch.Layer

namespace World

variable {X Ω : Type} [Fintype Ω] {D base bits chance h k : ℕ} [NeZero base] [NeZero bits]
  {p : Law Ω} {w : World X (base^h*(k+2))}

abbrev Color (chance bits h : ℕ) := Fin ((2*chance)^h) × (Fin h → Fin bits × Bool)

theorem Hierarchy.color (seq : Hierarchy w p chance D) (key : Address base bits) (hc : 0 < chance)
    {sample : Fin ((2*chance)^h) → Fin h → Ω} (hit : p.Hits chance h sample) :
    Nonempty (w.Emissions (Color chance bits h) (h*(D+1)+1)) := by
  classical
  have chooseTuple : ∀ x, ∃ j, ¬w.Blank (k+2) x → ∀ i, sample j i ∈ (seq i).sets x := by
    intro x
    by_cases hx : w.Blank (k+2) x
    · exact ⟨⟨0,by positivity⟩,fun hn => (hn hx).elim⟩
    obtain ⟨j,hj⟩ := hit (fun i => (seq i).sets x) (fun i =>
      (seq i).dense x (fun hh => hx (w.blank_mono (dvd_mul_left ..) hh)))
    exact ⟨j,fun _ => hj⟩
  choose idx hidx using chooseTuple
  choose mask hmask using fun x => seq.escape key x (sample (idx x))
  let color : X → Color chance bits h := fun x =>
    (idx x,fun i => (mask x i,w.read key i x (mask x i)))
  let emit := fun x => if w.Blank (k+2) x then none else some (color x)
  have emits : ∀ x i, emit x = some i → ¬w.Blank (k+2) x ∧ color x = i := by
    intro x i
    by_cases hx : w.Blank (k+2) x <;> simp [emit,hx]
  refine ⟨⟨emit,fun s j x hx => ⟨color x,by simp [emit,w.blank_micro hx]⟩,fun x i hi d => ?_⟩⟩
  apply (hmask x d).mono _ (fun _ hh => hh)
  intro y hy he
  obtain ⟨hn,hy'⟩ := emits y _ he
  have same : color y = color x := hy'.trans (emits x _ hi).2.symm
  rcases hy with hy | hy | ⟨j,_,hh⟩
  · exact hy
  · exact (hn hy).elim
  · have hj : idx y = idx x := congrArg Prod.fst same
    have he := congrFun (congrArg Prod.snd same) j
    obtain ⟨hm,hv⟩ := Prod.mk.inj he
    rcases hh with hh | hh
    · exact (hh (hj ▸ hidx y hn j)).elim
    · rw [hm] at hv
      exact (hh hv).elim

theorem Emissions.map {X A B : Type} {L k D : ℕ} {w : World X (L*(k+2))}
    (col : w.Emissions A D) (f : A ↪ B) : Nonempty (w.Emissions B D) := by
  refine ⟨⟨fun x => (col.emit x).map f,?_,?_⟩⟩
  · intro s j x hx
    obtain ⟨a,ha⟩ := col.micro s j x hx
    exact ⟨f a,by simp [ha]⟩
  · intro x b hb d
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hb
    apply (col.escape x a ha d).mono _ (fun _ hh => hh)
    intro y hy he
    obtain ⟨c,hc,he⟩ := Option.map_eq_some_iff.mp he
    exact hy (f.injective he ▸ hc)

end World

def PrimaryLemma : Prop :=
  ∀ m : ℕ, 0 < m → ∃ b bits chance D : ℕ, 2 ≤ b ∧ 0 < bits ∧ 0 < chance ∧
    b^m ≤ 2^bits ∧ (2*chance)*(bits*2) ≤ b ∧
    ∃ (Ω : Type) (_ : Fintype Ω) (p : Law Ω), ∀ (X : Type) n (w : World X n) width,
      3 ≤ width → Nonempty (w.Potential p chance D width (b^m))

theorem palette_of_primary (input : PrimaryLemma) : PaletteTheorem := by
  intro m hm threshold
  obtain ⟨b,bits,chance,D,hb,hbits,hc,hkey,hsize,Ω,inst,p,hs⟩ := input m hm
  let : NeZero (b^m) := ⟨by positivity⟩
  let : NeZero bits := ⟨hbits.ne'⟩
  let key : World.Address (b^m) bits :=
    (Fin.castLEEmb (by simpa using hkey : b^m ≤ Fintype.card (Fin bits → Bool))).trans
      (Fintype.equivFin _).symm.toEmbedding
  obtain ⟨h,hh,sample,hit⟩ := ((eventually_gt_atTop threshold).and (p.many_samples chance hc)).exists
  have hbig : h < b^h := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hb _)
  refine ⟨b^h,h*(D+1)+1,by omega,by omega,fun k hk => ?_⟩
  have he : (b^h)^m = (b^m)^h := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [he]
  let w := World.free ((b^m)^h*(k+2))
  let seq : World.Hierarchy w p chance D := fun i =>
    Classical.choice (hs _ _ w _ ((show 3 ≤ k+2 by omega).trans (Nat.le_mul_of_pos_left _ (by positivity))))
  obtain ⟨col⟩ := seq.color key hc hit
  have hcard : Fintype.card (World.Color chance bits h) ≤ b^h := by
    simpa [World.Color,mul_pow] using Nat.pow_le_pow_left hsize h
  exact col.map ((Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hcard))

theorem numerical_of_primary (input : PrimaryLemma) : NumericalLayers :=
  numerical_of_palette (palette_of_primary input)

end OAI.Geometry.Hirsch.Layer

namespace OAI.Geometry.Hirsch

theorem main_of_primary (input : Layer.PrimaryLemma) : MainTheorem :=
  main_of_numerical (Layer.numerical_of_primary input)

theorem excess_of_primary (input : Layer.PrimaryLemma) : ExcessTheorem :=
  excess_of_numerical (Layer.numerical_of_primary input)

theorem not_polynomialHirsch_of_primary (input : Layer.PrimaryLemma) : ¬ PolynomialHirsch :=
  not_polynomialHirsch_of_main (main_of_primary input)

end OAI.Geometry.Hirsch
