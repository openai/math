import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReader
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomStartup

/-! # Budget of the physical tally rectangle and the lead reader on the same batch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing Branch Cover TeamScales PackedHistoryCircuit.Normalized VPVNP
open scoped Classical

variable {F : Type} [Field F] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {ι : Type} [Fintype ι] {aux : ι → F} {q : ℕ}
    {S : SiteSchedule G} {a extra E d Q A B j : ℕ} {s : EpochScales S a extra}

/-- A single length threshold pays both the allocator's actual rectangular
team/coordinate/word scan and the native residue reader including its guard.
The size bound on the reader precedes all choices of common field and chart. -/
theorem JointSchedule.eventually_signed_post_rectangle (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ l, n=l+1 →
      let r := stretch b.ρ n
      let teams := b.physical.teamsPred n+1
      let w := b.physical.word n
      let T := f (adviceScale b.σ b.ρ n)
      ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart teams r w w w (T+6)), reader.charge ≤ c*(T+1)^k →
          let dim := pairedTableParameters (l+1) size+Fintype.card (G.Entry ⊕ ι)
          512*(teams+1)*(dim+1)*(w+1)+(7+reader.charge) ≤ r := by
  filter_upwards [b.physical.eventually_nativePackets (G:=G) (aux:=aux) (q:=q) f hf c k 4096,
    b.eventually_word_capacity 1 1] with n packets words
  intro l eqn
  subst n
  intro r teams w T size ord common chart prime alg reader bound dim
  have teamPos : 0<teams := Nat.succ_pos _
  have wordPos : 0<w := by
    have room : 1*(r*(l+1)+1)^1 < 2^w := words.2.2.1
    by_contra! no
    rw [show w=0 by omega] at room
    simp at room
  have pPos : 0 < pairedTableParameters (l+1) size := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Sum.inl (0,⟨0,by omega⟩)⟩
  have dimPos : 0<dim := pPos.trans_le (Nat.le_add_right ..)
  have paid := packets chart reader bound 0 0 0 0 0 (fun _ => 0)
  change 4096*(_+_+reader.charge+1+teams*(dim*w)) < r at paid
  have scaled : 512*(teams+1)*(dim+1)*(w+1) ≤ 4096*(teams*(dim*w)) := by
    calc
      _ ≤ 512*(2*teams)*(2*dim)*(2*w) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 512 (by omega)) (by omega)) (by omega)
      _ = _ := by ring
  omega

open RoutingISA RoutingISA.SignedTaskArena RoutingISA.CubeArena
open PackedHistoryCircuit.Normalized.SelectedSchedule

/-- Both post-call budgets on the very signed arena used in the chosen startup.
Its exponent digits, parameter entries and gadget axes come from the same
field chart and reader as the real header. -/
theorem JointSchedule.eventually_startup_post_rates {K : Type*} [Field K] (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule s (E+1) d Q A B j)
    (f : ℕ → ℕ) (hf : PolynomiallyBounded f) (c k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ l, n=l+1 →
      let r := stretch b.ρ n
      let teams := b.physical.teamsPred n+1
      let w := b.physical.word n
      let T := f (adviceScale b.σ b.ρ n)
      let expBits := Nat.clog 2 (r*(2*l+1)+1)
      ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
        {common : CommonField G aux q l size ord} (chart : AdvisedBranch common)
        [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
        (reader : ChosenReader chart teams r w w w (T+6)), reader.charge ≤ c*(T+1)^k →
        ∀ base traffic cells cables candidates profile bundles marked header body : ℕ,
        let sizes := selectedSizes base (BorderVNP.Cube.alphabet s.α n) traffic cells cables candidates teams r n profile
        let a₀ := sizes.selected cube.pred cube.b cube.h cube.copies cube.width
        ∀ id (geometry : GeometryDirectories),
        let params := physicalParameters a₀ geometry n bundles marked (pairedTableParameters (l+1) size) expBits
          (Fintype.card (G.Entry ⊕ ι)) w header body
        let ar : SignedTaskArena.Layout := ⟨a₀,id,params⟩
        ar.cube.teams*(ar.p.parameters*expBits) ≤ r ∧
          512*(ar.cube.teams+1)*(ar.dim+1)*(w+1)+(7+reader.charge) ≤ r := by
  filter_upwards [b.eventually_signed_post_rectangle (G:=G) (aux:=aux) (q:=q) f hf c k,
    b.eventually_reader_physical_room (G:=G) (aux:=aux) (q:=q) f hf c k] with n rectangle slots
  intro l hn r teams w T expBits size ord common chart fact alg reader charged
    base traffic cells cables candidates profile bundles marked header body sizes a₀ id geometry params ar
  exact ⟨(slots l hn chart reader charged).2.2.le,rectangle l hn chart reader charged⟩

end Diagonal

end BorderVNP
end Computability
end OAI
