import OAI.Computability.BorderVNP.CubeTeamOwnedVertexCount
import OAI.Computability.BorderVNP.CubeTeamRowFold

/-! # Complete traversal and publication of the owned vertex directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned VPVNP.BurstRAM

/-- Vertices written for a strict endpoint role in one ordered symbol row. -/
def strictVertices (n d blocks : ℕ) := (2*blocks*(d.choose 2)^n)*2^n

/-- The number of vertex records belonging to the first `q` endpoint views of
this team's public traversal. -/
def vertexPrefix (l : TeamRowPrepare.Layout) (owner : ℕ → ℕ) (n blocks q : ℕ) :=
  ∑ k ∈ Finset.range q, if owner (k/l.d) = l.teamID ∧ k/l.d ≠ k%l.d
    then strictVertices n l.d blocks else 0

/-- All counts and writes of the full owned-group evaluator, including initialization
from field 78 and publication of the computed vertex count in field 46. -/
theorem ownedGroups_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (n blocks b h K s : ℕ) (l : TeamRowPrepare.Layout) (owner cost : ℕ → ℕ)
    (bits : ℕ → List Bool) (I : ℕ → Memory w → Prop) (base : ℕ) (r : Bank w) (m : Memory w)
    (fit : l.Fits w) (hf : readings pub 0 = l.frame) (start : I 0 m)
    (inventory : ∀ q mu, I q mu → l.Fields (readings mu) ∧ readings mu (l.frame+78) = base ∧
      ∀ g < l.d, readings mu (l.ownerBase+g) = owner g)
    (skip : ∀ q < l.d*l.d, owner (q/l.d) ≠ l.teamID → ∀ mu, I q mu → I (q+1) mu)
    (visit : ∀ q < l.d*l.d, owner (q/l.d) = l.teamID → ∀ u mu, I q mu →
      readings u 7 = base+3*vertexPrefix l owner n blocks q →
      TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu) →
      TraceRun pub mac (if q/l.d = q%l.d then diagonalRole n b h K s else strictRole n b h K s)
        u mu (bits q) (cost q) (fun t mt =>
          I (q+1) mt ∧ readings t 7 = readings u 7 +
            (if q/l.d = q%l.d then 0 else 3*strictVertices n l.d blocks) ∧
            readings t 22 = q ∧ readings t 23 = l.d*l.d)) :
    let N := l.d*l.d
    let count := vertexPrefix l owner n blocks N
    TraceRun pub mac (ownedGroups n b h K s) r m (choices l owner bits) (4+(ticks l owner cost+11))
      (fun t mt => readings t 7 = base+3*count ∧
        ∃ pre : Memory w, I N pre ∧ mt = publishVertexCount pre l.frame count) := by
  let J (q : ℕ) (p : Word w) (mu : Memory w) :=
    I q mu ∧ p.val = base+3*vertexPrefix l owner n blocks q
  have frameFit : l.frame+78 < 2^w := by have := fit.frameFit; omega
  have ptr := (inventory 0 m start).2.1
  have init := startVertices_run pub mac r m l.frame base hf frameFit ptr
  have stage (u : Bank w) (mu : Memory w) (hu : readings u 7 = base ∧ mu = m) :
      TraceRun pub mac (scan (strictRole n b h K s) (diagonalRole n b h K s)) u mu
        (choices l owner bits) (ticks l owner cost) (fun t mt =>
          J (l.d*l.d) (t 7) mt ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d) := by
    obtain ⟨hu,rfl⟩ := hu
    have initial : J 0 (u 7) mu := ⟨start,by simpa [vertexPrefix,readings] using hu⟩
    have publicWords q p mu' (hj : J q p mu') :
        l.Fields (readings mu') ∧ ∀ g < l.d, readings mu' (l.ownerBase+g) = owner g :=
      ⟨(inventory q mu' hj.1).1,(inventory q mu' hj.1).2.2⟩
    have miss (q : ℕ) (hq : q < l.d*l.d) (ho : owner (q/l.d) ≠ l.teamID) p mu' (hj : J q p mu') : J (q+1) p mu' := by
      refine ⟨skip q hq ho mu' hj.1,?_⟩
      simpa [vertexPrefix,Finset.sum_range_succ,ho] using hj.2
    have work (q : ℕ) (hq : q < l.d*l.d) (ho : owner (q/l.d) = l.teamID)
        (v : Bank w) (mv : Memory w) (hj : J q (v 7) mv)
        (ready : TeamRowPrepare.ReadyRow l (readings mv) q (.ofWords v mv)) :
        TraceRun pub mac (if q/l.d = q%l.d then diagonalRole n b h K s else strictRole n b h K s)
          v mv (bits q) (cost q) (Next l J q) := by
      apply (visit q hq ho v mv hj.1 hj.2 ready).mono le_rfl
      rintro z mz ⟨hi,h7,h22,h23⟩
      refine ⟨⟨hi,?_⟩,h22,h23⟩
      change readings z 7 = _
      have cur : readings v 7 = _ := hj.2
      by_cases hd : q/l.d = q%l.d <;>
        simp [h7,cur,vertexPrefix,Finset.sum_range_succ,ho,hd,Nat.mul_add,Nat.add_assoc]
    exact scan_run pub mac _ _ l owner cost bits J u mu fit hf initial publicWords miss work
  let N := l.d*l.d
  let count := vertexPrefix l owner n blocks N
  let post (t : Bank w) (mt : Memory w) := readings t 7 = base+3*count ∧
    ∃ pre : Memory w, I N pre ∧ mt = publishVertexCount pre l.frame count
  have next (u : Bank w) (mu : Memory w) (hu : readings u 7 = base ∧ mu = m) :=
    (stage u mu hu).seq (Q := post) (fun v mv hv =>
      (finishVertices_run pub mac v mv l.frame base count hf frameFit
        (inventory N mv hv.1.1).2.1 hv.1.2).mono le_rfl
          (fun t mt ht => ⟨ht.1.trans hv.1.2, mv,hv.1.1,ht.2⟩))
  simpa only [ownedGroups,Code.block,List.nil_append,List.append_nil,N,count,post]
    using init.seq next

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
