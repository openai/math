import OAI.Computability.VPVNP.PairSimulationMapRowExact

/-! # Uniformly bounded native evaluation of one decoded motif row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapRow

open MotifSelector MotifDemandPadding MotifEntry MotifGrid MotifBlocks MotifConversion MapLookup
open BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM
open scoped Fin.CommRing

variable {J D E : Type} [DecidableEq J] [Fintype J] [Fintype D] [Fintype E]
  {K : Type} [Field K] {src dst : D → J} {G : Supply J E}
  {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (s : Selector B) {u w r k pcCount : ℕ}
  (i : Fin u) (j : J) (demand : D → ℕ) (v : E → ℕ) (d : DemandBits src dst demand j)
  (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
  (base : LabelField D E → ℕ) (off : E → ℕ) (fd : ∀ e, baseDemand B z e ≤ w)
  (fs : ∀ e, basePayload B s e ≤ w)
  (reg : MapRowFields.Registers (LabelField D E) (D ⊕ E) r) (widthPort : (D ⊕ E) → Fin k)
  (key : LabelRow B z s j → LabelField D E → Fin k) (name : LabelRow B z s j → Fin k)
  (P : Sites (pcCount := pcCount) B z s j reg widthPort key name)

/-- Reading one decoded copy computes its prescribed parameter ordinal and advances
the natural offsets of every group. The only private operations are deterministic ticks. -/
theorem native (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (M : Machine w pcCount r k) (stop bad : Fin pcCount)
    (hl : Linked B z s j reg widthPort key name P M stop bad)
    (hp : ∀ g, M.publicData (widthPort g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (hkey : ∀ y f, M.publicData (key y f) = labelKey B z s j fd fs y f)
    (hname : ∀ y, M.publicData (name y) = ordinal (lookup B z s j y.1 y.2))
    (fit : MapRowFields.Fits group (Sum.elim (baseDemand B z) (basePayload B s))
      (slices B z i j demand v d x base off) w)
    (c : Config w pcCount r)
    (hc : c.pc = P.fields.first (P.lookupPC (nameFlow B z s j reg key name).entry)
      (labelFields D E))
    (hr : MapRowFields.Resident reg (slices B z i j demand v d x base off) c) :
    let buffers := slices B z i j demand v d x base off
    let width := Sum.elim (baseDemand B z) (basePayload B s)
    ∃ n ≤ cap B z s j, ∃ out, Prefix M c (List.replicate n .tick) out ∧ out.pc = stop ∧
      out.reg (reg .label) = ordinal (MapStream.readRow src dst (baseDemand B z) demand G
        (basePayload B) (lookup B z) v j d x i s off) ∧
      MapRowFields.Resident reg { buffers with offset := fun g ↦ buffers.offset g + width g } out ∧
      (∀ q, q ≠ reg .label → (∀ g, q ≠ reg (.offset g)) → q ≠ reg .tmp →
        q ≠ reg .start → q ≠ reg .cursor → (∀ f, q ≠ reg (.query f)) → out.reg q = c.reg q) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro buffers width
  exact ⟨exactSteps B z s i j demand v d x off fd fs key M.publicData,
    exactSteps_le_cap B z s i j demand v d x off fd fs key M.publicData,
    native_exact B z s i j demand v d x base off fd fs reg widthPort key name P ordinal M stop bad
      hl hp hkey hname fit c hc hr⟩

end PairSimulation.MapRow

end VPVNP
end Computability
end OAI
