import OAI.Hierarchy.DescentRotorRootPresence
import OAI.Hierarchy.DescentResetSignedStencilRun

namespace OAI
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGL DescentColonies DescentResetAttachments
open DescentChosenRouter DescentSharedCableNames.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
local notation "native" => order.trans Fin.valEmbedding
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (DescentSixParty.StarKeys.filled W.graph A.pos A.block digits) A.hub g)

local notation "baseDepth" => T.commonDepth
local notation "R" => Z.placement

private theorem cast_join {k₁ k₂ c d₁ : ℕ} (same : k₁=k₂) (fit : c≤k₁) (key : Block c)
    (j : Block (k₁-c)) :
    group d₁ (join (fit.trans_eq same) key (Fin.cast (congrArg (fun k=>2^(k-c)) same) j))=
      group d₁ (join fit key j) := by subst k₂;rfl

/-- Strip the arithmetic shape's low mode bit from the actual all-coordinates stencil result.
    This also applies on coordinates supporting no positive predecessor wire. -/
theorem rotor_stencil_mode (v : V) (hi : Block baseDepth) (packed : Block (m-baseDepth)→ℕ)
    (highField : Block (m-baseDepth)→ℕ)
    (seen : ∀j,packed j=2*highField j+
      ((A.hub v) || decide ((frm.host v,group ((R).b (frm.host v))
        (join (((T.commonLow (frm.host v)).trans ((R).depth (frm.host v))).trans_eq frm.extent) hi j))∈(R).keys)).toNat)
    (j : Block (Z.k-baseDepth)) :
    packed (Fin.cast (congrArg (fun k=>2^(k-baseDepth)) frm.extent) j)%2=
      Bool.toNat (decide ((R).hub (frm.host v) ∨ (frm.host v,group ((R).b (frm.host v))
        (join ((T.commonLow (frm.host v)).trans ((R).depth (frm.host v))) hi j))∈(R).keys)) := by
  rw [seen,cast_join frm.extent ((T.commonLow (frm.host v)).trans ((R).depth (frm.host v)))]
  have mode : (A.hub v || decide ((frm.host v,group ((R).b (frm.host v))
      (join ((T.commonLow (frm.host v)).trans ((R).depth (frm.host v))) hi j))∈(R).keys))=
      decide ((R).hub (frm.host v) ∨ (frm.host v,group ((R).b (frm.host v))
      (join ((T.commonLow (frm.host v)).trans ((R).depth (frm.host v))) hi j))∈(R).keys) := by
    by_cases flag : A.hub v=true
    · simp [flag,(frm.rotorHub v).mpr flag]
    · have no := mt (frm.rotorHub v).mp flag
      have off : A.hub v=false := by cases eqn : A.hub v <;> simp_all
      simp [no,off]
  rw [mode]
  have parity (n : ℕ) (flag : Bool) : (2*n+flag.toNat)%2=flag.toNat := by
    cases flag <;> simp [Nat.add_mod]
  exact parity _ _

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
