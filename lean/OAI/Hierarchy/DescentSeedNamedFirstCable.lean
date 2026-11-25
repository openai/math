import OAI.Hierarchy.DescentSeedNamedSigned
import OAI.Hierarchy.DescentOriginalArgumentPointer
import OAI.Hierarchy.DescentNamedBoundary

namespace OAI
/-! # The first cable pointer under the physical seed renaming -/
namespace Hierarchy.DescentSixParty.SeedNamed.Signed
open DescentCompiler DescentColonies DescentSharedCableNames DescentKernelHistory DescentOperandStateBanks
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
    (R : Reached W G q ε S k i z D wire hist)
local notation "A" => R.placement
local notation "T" => placed R
local notation "H" => Stage.Host (Fin (S.groupCount i)) R.V k
local notation "orig" => R.order.trans Fin.valEmbedding
local notation "next" => Function.Embedding.trans (Reached.order (reached R)) Fin.valEmbedding
local notation "ranks" => DescentStageEdgeReceipt.groupRank
  (Function.Embedding.trans (Function.Embedding.refl (Fin (S.groupCount i))) Fin.valEmbedding)
  (R.vertex.trans Fin.valEmbedding)
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k ranks

private def ticket (h : H) (p : NamedPorts R h) :
    ((world R).graph.Edge×ℕ) ⊕ ((world R).graph.Edge×ℕ) :=
  match p with
  | .inl ⟨e,u⟩ => .inl (e.val,u.val)
  | .inr ⟨e,u⟩ => .inr (e.val,u.val)

private theorem ticket_inj (h : H) : Function.Injective (ticket R h) := by
  rintro (⟨⟨a,ha⟩,u⟩|⟨⟨a,ha⟩,u⟩) (⟨⟨b,hb⟩,v⟩|⟨⟨b,hb⟩,v⟩) eqn
  · have pair : (a,u.val) = (b,v.val) := Sum.inl.inj eqn
    have edges : a = b := congrArg Prod.fst pair
    exact congrArg Sum.inl (Sigma.ext (Subtype.ext edges)
      ((Fin.heq_ext_iff (congrArg (placed R).grainCount edges)).2 (congrArg Prod.snd pair)))
  · simp [ticket] at eqn
  · simp [ticket] at eqn
  · have pair : (a,u.val) = (b,v.val) := Sum.inr.inj eqn
    have edges : a = b := congrArg Prod.fst pair
    exact congrArg Sum.inr (Sigma.ext (Subtype.ext edges)
      ((Fin.heq_ext_iff (congrArg (placed R).grainCount edges)).2 (congrArg Prod.snd pair)))

private theorem live_ticket (h h' : H) (eqHost : h'=h) (p : Ports R h) (p' : NamedPorts R h')
    (same : ticket R h' p'=ticket R h (port R h p)) :
    Stage.live T next S (reached R).valid names h' p'=Stage.live A orig S R.valid names h p := by
  subst h'
  have slot : p' = port R h p := ticket_inj R h same
  exact (congrArg (fun q : NamedPorts R h => Stage.live T next S (reached R).valid names h q) slot).trans
    (live R names h p)

/-- The source half of a loop and the target half of a genuinely incoming
edge select the same signed grain before and after renumbering. -/
theorem firstCable_incident {p : ℕ} (hp : 0<p) (v : (world R).graph.Site)
    (e : Incident W.graph ((site R).symm v)) (chunk : ℕ)
    (fitsNamed : (chunk+1)*p≤(world R).graph.width
      (PhysicalRename.incident W.graph (site R) (edge R) v e).val)
    (fits : (chunk+1)*p≤W.graph.width e.val) :
    Reached.firstCable (reached R) hp v (PhysicalRename.incident W.graph (site R) (edge R) v e) chunk fitsNamed=
      Reached.firstCable R hp ((site R).symm v) e chunk fits := by
  let u:=(site R).symm v
  let fresh:=PhysicalRename.incident W.graph (site R) (edge R) v e
  have positive : 0<R.placement.grainCount e.val:=by
    by_contra! empty
    have full:=R.placement.grainCount_fit S R.valid e.val
    rw [show R.placement.grainCount e.val=0 by omega,Nat.zero_mul] at full
    have noRoom : (chunk+1)*p ≤ 0 := fits.trans_eq full
    exact (Nat.not_lt_of_ge noRoom) (Nat.mul_pos (Nat.zero_lt_succ chunk) hp)
  have positive' : 0<(placed R).grainCount fresh.val:=by
    change 0<(placed R).grainCount (edge R e.val)
    simpa only [grain] using positive
  have back : site R u = v := (site R).apply_symm_apply v
  have hosts : Stage.home T v=Stage.home A u := by
    have eqn : Stage.home T (site R u)=Stage.home A u :=
      Prod.ext (position R u).1 (position R u).2.1
    exact (congrArg (Stage.home T) back).symm.trans eqn
  have ends : (world R).graph.src fresh.val=site R (W.graph.src e.val) := (cable R e.val).1
  have source : (world R).graph.src fresh.val=v ↔ W.graph.src e.val=u := by
    constructor
    · intro hit
      exact (site R).injective (ends.symm.trans (hit.trans back.symm))
    · intro hit
      exact ends.trans ((congrArg (site R) hit).trans back)
  have first:=live_ticket R (Stage.home A u) (Stage.home T v) hosts
    (DescentTerminalPortChart.first A u e positive)
    (DescentTerminalPortChart.first T v fresh positive') (by
      by_cases atSrc : W.graph.src e.val=u
      · simp only [DescentTerminalPortChart.first,dite_eq_left atSrc]
        split
        · rfl
        · rename_i missed
          exact (missed (source.mpr atSrc)).elim
      · simp only [DescentTerminalPortChart.first,dite_eq_right atSrc]
        split
        · rename_i hit
          exact (atSrc (source.mp hit)).elim
        · rfl)
  exact congrArg (fun wing : Stage.Live R.placement.degree R.placement.cap=>Pointer.cable wing.neighbor.val wing.wire.val chunk) first

end
end Hierarchy.DescentSixParty.SeedNamed.Signed

end OAI
