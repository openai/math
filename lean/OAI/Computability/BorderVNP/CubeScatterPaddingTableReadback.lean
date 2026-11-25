import OAI.Computability.BorderVNP.CubeScatterPaddingPublished
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally
import OAI.Computability.BorderVNP.CubeDirectedIntervalTables

/-! # Native greedy, directed interval and packet-directory readout for padding -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open HostAddress Crossing Physical NativeIntervals PairDirectory VPVNP.MotifBase Tally
open private key_surj from OAI.Computability.BorderVNP.CubeScatterPaddingTail

variable {n blocks b h K s : ℕ}

/-- Words retained from the three actual native producers when the padding verifier
starts. Only the addressed owner and data words are needed. -/
structure TableReadback (P : Pointers) (d n : ℕ) (final : ℕ → ℕ) (teams : TeamNative.Layout)
    (scheduled : ℕ → ℕ) (interval : NativeIntervals.Layout) (widths : ℕ → ℕ)
    (pair : PairDirectory.Layout) (table : ℕ → ℕ) : Prop where
  /-- The greedy owner words. -/
  owner : ∀ g : Fin d, final (P.owners+g.val) = scheduled (teams.owners+g.val)
  /-- The occupied-width array written by the native crossing interval scan. -/
  width : ∀ key < d^(n+1)*d^(n+1), final (P.widths+key) = widths (interval.widths+key)
  /-- The three-word array filled by the native packet directory. -/
  fields : ∀ key < d^(n+1)*d^(n+1), ∀ f < 3, final (P.triples+3*key+f) = table (pair.table+3*key+f)

/-- The full physical header follows from the actual greedy scheduler for the passing
declaration, the directed-width readout, and the actual native three-word directory image. -/
theorem TableReadback.header {P : Pointers} {weights : GroupWeights.Layout} {teams : TeamNative.Layout}
    {orig scheduled final widths table origTable : ℕ → ℕ} {interval : NativeIntervals.Layout}
    {pair : PairDirectory.Layout} (words : TableReadback P weights.groups n final teams scheduled interval widths pair table)
    (result : GroupWeights.ScheduleResult weights teams orig scheduled)
    {decl : LengthDeclaration n weights.groups} (select : Packet n weights.groups blocks → Selector n K h)
    (pass : passesLengths b s select decl) (label : Fin weights.cells → Label (n+1) weights.groups)
    {X : Type*} [Fintype X] (recv : X → Fin weights.cells) (dataWidth : X → ℕ)
    (image : GroupWeights.PhysicalImage weights orig blocks b K h decl label recv dataWidth)
    (tableImage : PairDirectory.Image pair origTable pair.count table)
    (shape : pair.d = weights.groups ∧ pair.axes = n+1 ∧ pair.blocks = blocks)
    (team : Fin (teams.r+1)) (frame packetBase : ℕ) :
    TailHeader decl.1 (greedyOwner teams.r b s label recv dataWidth select) Fin.valEmbedding team
      (P.layout frame team.val packetBase decl.1 weights.groups blocks b h K s)
      final (fun k => widths (interval.widths+k)) blocks b h K s := by
  refine ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,rfl,?_,fun k hk => words.width k hk,?_⟩
  · intro g
    exact (words.owner g).trans (greedyOwner_stored result select pass label recv dataWidth image g)
  · intro u v
    let k := code u*weights.groups^(n+1)+code v
    have key : k < weights.groups^(n+1)*weights.groups^(n+1) := by
      have bound := (finProdFinEquiv (finFunctionFinEquiv u,finFunctionFinEquiv v)).isLt
      change code v + weights.groups^(n+1)*code u < _ at bound
      simpa only [k,Nat.mul_comm,Nat.add_comm] using bound
    have z : pair.Z = weights.groups^(n+1) := by simp [PairDirectory.Layout.Z,shape.1,shape.2.1]
    have lt (x : Label (n+1) weights.groups) : code x < pair.Z := z ▸ (finFunctionFinEquiv x).isLt
    obtain ⟨kind,first,vertex⟩ := tableImage.lookup (code u) (code v) (lt u) (lt v)
    simp only [z,shape.1,shape.2.1,shape.2.2] at kind first vertex
    have zero := words.fields k key 0 (by decide)
    simp only [Nat.add_zero] at zero
    exact ⟨zero.trans kind,
      (words.fields k key 1 (by decide)).trans first,(words.fields k key 2 (by decide)).trans vertex⟩

/-- Every used width from the final native square table satisfies the actual physical
slot cap, including all pairs whose interval is empty. -/
theorem occupied_le {D m d : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    {N : Network D P bits} {cell : N.Site → Cell} {interval : NativeIntervals.Layout}
    {before dir : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin interval.count}
    {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {hz : d^(n+1) = interval.alphabet}
    (rows : PhysicalRows N cell interval before ord row cells label (productCode n d interval.alphabet hz))
    (image : interval.Image before interval.count dir)
    (cap : ∀ p, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) p ≤ blocks*(h*b))
    (key : ℕ) (hk : key < d^(n+1)*d^(n+1)) : dir (interval.widths+key) ≤ blocks*(h*b) := by
  obtain ⟨u,v,rfl⟩ := key_surj hk
  have codeEq : pairCode (productCode n d interval.alphabet hz) (u,v) = code u*d^(n+1)+code v := by
    change (finFunctionFinEquiv u).val*interval.alphabet+(finFunctionFinEquiv v).val = _
    rw [← hz]; rfl
  rw [← codeEq,rows.image_load image (u,v)]
  exact cap _

end Cube.Padding

end BorderVNP
end Computability
end OAI
