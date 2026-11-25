import OAI.Computability.BorderVNP.TransmissionCoverWorkspace
import OAI.Computability.BorderVNP.PackedDirectoryAddressWidth
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # Placement workspace for the actual selected geometry output

The one-field and two-field instances reserve the true candidate count before
the selected circuit's scratch. Both placement-table bases and all thirty-seven
indirect controls lie within that allocation. The site block width is the
ceiling obtained from the actual number of occupied verifier slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open Filter TeamScales Packing RoutingOutputs
open GeometryAdviceRate (packetWords)

/-- Uniform room for the real directory and geometry, including a verifier
whose occupied slots use just one live field. -/
theorem eventually_cover_workspace_fields (I : Type) [Fintype I] [Nonempty I]
    {α τ : ℝ} (ha : 0 < α) (ha' : α < 1/1000) (ht : 0 < τ) (hts : τ < α/100)
    {K : ℕ} (hK : 1 ≤ K) (fan : τ*Real.logb 2 K ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r header copied w slots u k o b : ℕ) (D : Directory.Layout),
      0 < r → 0 < slots → r*literal α n ≤ slots → slots ≤ r*n →
      let N := teams α τ K n
      let V := CoverScale.sites I (CoverScale.initialDepth I r n)
      let arena : StartupArena := ⟨N,r,literal α n,link (τ/5) N n,header,copied⟩
      D.teams = N → D.processors = r → D.entries = K^epochs τ n*V → D.fields ≤ 2 →
      D.block = blockWidth slots V → D.literal = literal α n →
      header ≤ r*arena.link → copied ≤ r*block (τ/5) n → logWidth r n ≤ w → 1 ≤ b → 1 ≤ w →
      packetWords k u o b*w ≤ r*width n (95/100:ℝ) →
      let fresh := arena.next+7*D.candidates
      let stop := GeometryAdvice.Allocation.stop fresh u k o b w
      arena.frame+112 ≤ arena.next ∧ stop ≤ 2*r*n ∧ stop < 2^w := by
  have base := eventually_cover_workspace I ha ha' ht hts hK fan 1 (by decide)
  have arenas := StartupArena.eventually_fits (by linarith : 0<τ/5) (by linarith : τ/5≤α)
  filter_upwards [base,arenas,eventually_many_teams ha τ hK 3] with n cut asize three
  intro r header copied w slots u k o b D hr hs litSlots slotCap N V arena nt nr ne nf nb nl hH hC hw hb hw' cap fresh stop
  let two := { D with fields := 2 }
  have x := cut r header copied w slots u k o b two hr hs litSlots slotCap nt nr ne rfl nb nl hH hC hw hb hw' cap
  let top := GeometryAdvice.Allocation.stop (arena.next+7*two.candidates) u k o b w
  change arena.frame+112 ≤ arena.next ∧ _ ∧ 1*(top-arena.next) ≤ r*n ∧ top < 2^w at x
  have counts : D.candidates ≤ two.candidates := by
    change 2*D.entries+D.teams*D.processors*D.fields*(D.literal/D.block+2) ≤
      2*D.entries+D.teams*D.processors*2*(D.literal/D.block+2)
    gcongr
  have le : stop ≤ top := by
    dsimp only [stop,top,GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,GeometryAdvice.Allocation.dense,
      GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp,fresh]
    omega
  have arenaRoom := (asize r N header copied w hr three hH hC hw).1
  change arena.next < r*n at arenaRoom
  have diff := x.2.2.1
  rw [one_mul] at diff
  exact ⟨x.1,by rw [Nat.mul_assoc]; omega,le.trans_lt x.2.2.2⟩

/-- Concrete placement room obtained from the real evaluator's output count
and the end of its allocated scratch, on each selected network. -/
theorem output_directory_room {n r W base u k o b gap m C slots : ℕ} {α ξ : ℝ}
    (D : Directory.Layout) (hn : 1 ≤ n) (hr : 1 ≤ r) (ha : 0 ≤ α) (hx : 0 ≤ ξ)
    (teams : D.teams ≤ n) (procs : D.processors = r) (fields : D.fields ≤ 2)
    (lit : D.literal = literal α n) (linkEq : D.link = link ξ D.teams n)
    (sites : r ≤ D.sites) (cover : D.sites ≤ r*n) (block : D.block = blockWidth slots D.sites)
    (pos : 0 < slots) (supply : r*D.literal ≤ slots) (slotCap : slots ≤ r*n)
    (desc : D.description ≤ D.literal/2) (entries : D.entries ≤ D.teams*D.sites)
    (tails : D.entries*D.description ≤ D.teams*r*(D.literal/2))
    (extra : gap ≤ n^2) (wide : 16*(logWidth r n+2) ≤ W) :
    let a := D.teams*D.sites
    let fresh := base+7*D.candidates
    let origin := GeometryAdvice.Allocation.dest fresh u k o b
    let stop := GeometryAdvice.Allocation.stop fresh u k o b W
    let p := bases origin m C D.entries
    m*3+RoutingOutputs.count m C D.entries a+((C+(D.entries+C))+37) ≤ o →
    stop ≤ 2*r*n → stop < 2^W →
    base+7*D.candidates ≤ origin ∧ controlsBase origin m C D.entries a+36 < 2^W ∧
      width n (1/5)+gap+D.entries*D.description ≤ 3*(r*n)^2 ∧
      Directory.ISA.wordBound (Directory.ISA.placementBound D p.privatePairs p.livePairs (3*(r*n)^2)) < 2^W := by
  intro a fresh origin stop p out small room
  have whole : controlsBase origin m C D.entries a+37 ≤ stop := by
    dsimp only [controlsBase,bases,RoutingOutputs.count] at out ⊢
    change _ ≤ origin+o+GeometryOutput.packetCount u k o b*W+GeometryOutput.packetCount u k o b
    omega
  have indices : p.privatePairs ≤ 2*r*n ∧ p.livePairs ≤ 2*r*n := by
    dsimp only [controlsBase,p,bases] at whole ⊢
    omega
  exact ⟨by dsimp only [origin,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp,fresh]; omega,
    by omega,Directory.ISA.directory_slot_word_room D hn hr ha hx teams procs fields lit linkEq sites cover block
      pos supply slotCap desc entries tails indices extra wide⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
