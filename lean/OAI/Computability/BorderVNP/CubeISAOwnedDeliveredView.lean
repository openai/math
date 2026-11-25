import OAI.Computability.BorderVNP.CubeISAOwnedPreparedView
import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload

/-! # True delivered strict-row words at the outer team's native row entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRowSources

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {a q blocks K h b s : ℕ}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- A passing physical shared assignment, when read from the actual successful
receivers, prepares either owner's complete strict-side scatter and vertex role.
The current memory may already contain earlier role outputs. -/
theorem SharedWriters.strict_side_ready (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (A : Padding.Banks.Data a q blocks b h K s) (p : Symbols q) (high : Bool)
    (pass : passesLengths b s A.select decl)
    (emits : sharedWords decl ⟨⟨A.select,pass⟩,fun _ => rowCrossValue A.supply (fun z => A.value z.1.val z.2)⟩ =
      f.receivedRows g group)
    (pub : Arg → Word w) (r₀ : Bank w) (m : Memory w) (power vertexBase stop out : ℕ) :
    let u := if high then group p.val.2 else group p.val.1
    let l := TeamRowPrepare.Layout.ofShared g u.val
    let k := key (oriented p high)
    let old := (H u).history.val.2.2
    Seed A l power pub old → Allocation A l power vertexBase stop w →
    readings r₀ 7 = out → vertexBase ≤ out → out+(2*blocks*(q.choose 2)^a)*(3*2^a) ≤ stop →
    (∀ j ∈ source l power a, m j = old j) → TeamRowPrepare.ReadyRow l (readings m) k (.ofWords r₀ m) →
    OwnedStages.SideReady (A.packet p high (l.view k) (l.crossing k)) (A.side power l.header out)
      pub (source l power a) r₀ m := by
  intro u l k old seed room cursor low endRoom previous ready
  have axis : A.axis = decl.1 := Fin.ext (seed.axis.symm.trans frame.axis)
  obtain ⟨sels,crosses⟩ := writer.physical_streams frame A.select pass A.supply (fun z => A.value z.1.val z.2) emits p high
  have ptr : l.view k = if high then g.view p.val.2 p.val.1 else g.view p.val.1 p.val.2 := by
    rw [TeamRowPrepare.Layout.ofShared_view,frame.groups,(key_digits (oriented p high)).1,(key_digits (oriented p high)).2]
    cases high <;> rfl
  have region : Set.Ico l.viewBase (l.viewBase+l.stride*(l.d*l.d)) = pairRegion g := by
    simp only [l,TeamRowPrepare.Layout.ofShared,pairRegion,pow_two]
  apply strict_ready seed room p high r₀ out cursor low endRoom previous ready
  · rw [region,ptr,axis]
    exact sels
  · rw [region,ptr,axis]
    exact crosses

end TeamContraction

end BorderVNP
end Computability
end OAI
