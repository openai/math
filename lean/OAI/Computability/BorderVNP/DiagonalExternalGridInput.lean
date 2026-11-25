import OAI.Computability.BorderVNP.DiagonalExternalGridHosts
import OAI.Computability.BorderVNP.DiagonalExternalFinePack

/-! # The real input read by each packed bottom copy

A global assignment is extended once to the physical array of grouped tile words.
Selecting an outer pack and a bottom slice recovers the original team's fine input,
including its literal, shared exterior and pin fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.GridHosts

open Crossing Packing TeamContraction ParseBatch.Prewire

variable {R r t pins link inner n V : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (hV : 0 < V) (groups copies : ℕ) (h : groups*copies = R+1)

/-- Encoding an outer group and a bottom copy recovers the very same grouped
word and lane used by the copy's native external reader. -/
theorem groupedLane_copy (u : Fin groups) (i : Fin copies) (p : Fin r × Fin (publicWidth G)) :
    let a := Network.repeatLane (fun _ : Fin V => blockWidth (r*n) V) (wiredLane G V hV) copies (i,p)
    groupedLane G V hV groups copies h ((teamBlocks groups copies h).symm (u,i),p) =
      ⟨(u,a.1),a.2⟩ := by
  let e := teamBlocks groups copies h
  let f (t : Fin groups × Fin copies) :=
    let a := Network.repeatLane (fun _ : Fin V => blockWidth (r*n) V) (wiredLane G V hV) copies (t.2,p)
    (⟨(t.1,a.1),a.2⟩ : (Σ _ : Fin groups × Fin V, Fin (copies*blockWidth (r*n) V)))
  exact congrArg f (e.apply_symm_apply (u,i))

/-- Reading any bottom pack after extending the whole physical input recovers
the individual bits assigned to the teams in that pack. -/
theorem grouped_read (x : Ports (fun _ : PublicPort R r (G.program.length+t) link => 1))
    (u : Fin groups) (i : Fin copies) (p : Fin r × Fin (publicWidth G)) :
    let g := blockWidth (r*n) V
    let z := FineView.extend (groupedLane G V hV groups copies h) x
    Network.readExternal (fun _ : Fin V => copies*g)
      (Network.repeatLane (fun _ : Fin V => g) (wiredLane G V hV) copies)
      (fun a => z (u,a)) (i,p) 0 = x ((teamBlocks groups copies h).symm (u,i),p) 0 := by
  let a := Network.repeatLane (fun _ : Fin V => blockWidth (r*n) V) (wiredLane G V hV) copies (i,p)
  let z := FineView.extend (groupedLane G V hV groups copies h) x
  let bit (y : Σ _ : Fin groups × Fin V, Fin (copies*blockWidth (r*n) V)) := z y.1 y.2
  change bit ⟨(u,a.1),a.2⟩ = _
  rw [← groupedLane_copy G hV groups copies h u i p]
  exact FineView.extend_lane _ x _

/-- The copy selected by an outer pack and bottom-slice number sees precisely
the true prewired processor bit on the given shared exterior assignment and pin. -/
theorem grouped_publicBits (pin : Fin pins → Bool) (ext : Exterior R r link → Bool)
    (u : Fin groups) (i : Fin copies) (p : Fin r × Fin (publicWidth G)) :
    let g := blockWidth (r*n) V
    let z := FineView.extend (groupedLane G V hV groups copies h)
      (fun p _ => publicBits G p.1 pin ext p.2)
    Network.readExternal (fun _ : Fin V => copies*g)
      (Network.repeatLane (fun _ : Fin V => g) (wiredLane G V hV) copies)
      (fun a => z (u,a)) (i,p) 0 = publicBits G ((teamBlocks groups copies h).symm (u,i)) pin ext p :=
  grouped_read G hV groups copies h _ u i p

end Diagonal.ExternalSew.GridHosts

end BorderVNP
end Computability
end OAI
