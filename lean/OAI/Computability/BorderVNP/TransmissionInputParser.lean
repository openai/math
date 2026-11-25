import OAI.Computability.BorderVNP.TransmissionPinSlots
import OAI.Computability.BorderVNP.TeamTapeInputLayout

/-! # Parsing the signed processor words into the actual RAM initialization rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP UniversalMachine Diagonal.Layout RoutingISA.Pins

variable {R r t d link inner n a : ℕ} {Edge : Type}

/-- Two self-delimiting compact binary public counts, for RAM input and interior routing. -/
def cutWidth (n : ℕ) : ℕ := 4 * Nat.clog 2 (n+1) + 2

/-- The fixed part of the literal tail contains the two real cut lengths. The rest of
the literal is free to hold site descriptions and other processor-specific advice. -/
def cutTail (n size inner : ℕ) (free : Fin a → Bool) : Fin (cutWidth n+a) → Bool :=
  let bits := TeamTapeInput.parameters (TeamTapeInput.digits n size) (TeamTapeInput.digits n inner)
    ++ List.ofFn free
  fun j => bits[j.val]'(by
    simpa [bits, cutWidth, TeamTapeInput.length_parameters] using j.isLt)

/-- Enumerating the pinned literal tail restores the exact length fields and free bits. -/
theorem ofFn_cutTail (n size inner : ℕ) (free : Fin a → Bool) :
    List.ofFn (cutTail n size inner free) =
      TeamTapeInput.parameters (TeamTapeInput.digits n size) (TeamTapeInput.digits n inner)
        ++ List.ofFn free := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_append, TeamTapeInput.length_parameters, List.length_ofFn]; rfl
  · intros; simp [cutTail]

/-- A signed-contraction layout with the real public program and compact input
lengths installed in every processor literal. -/
def tapeWiring (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link n : ℕ)
    (fit : 2*((programPrefix p).length+(cutWidth n+a))+R*link+inner ≤ n) :
    Wiring R r (cutWidth n+a) d link inner n Edge where
  program := programPrefix p
  literal u j := cutTail n (2*((programPrefix p).length+(cutWidth n+a))+R*link) inner (free u j)
  interior := interior
  fits := fit

/-- On every assignment of the actual contraction wires, the finite tape parser extracts
precisely the processor row and interior bit stream, including the full program prefix
in the RAM data, within its linear clock. -/
theorem tapeWiring_parse (p : UniversalMachine.Program) (free : Fin (R+1) → Fin r → Fin a → Bool)
    (interior : Fin r → Fin inner → Option Edge) (d link n : ℕ)
    (fit : 2*((programPrefix p).length+(cutWidth n+a))+R*link+inner ≤ n)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Edge → Bool) (ibase hbase starbase : ℕ) :
    let G := tapeWiring p free interior d link n fit
    let fields := G.processorFields u pin ext ibase hbase starbase
    let route := List.ofFn (fun i => (interior j i).elim false int)
    let pad := List.replicate (n-(2*((programPrefix p).length+(cutWidth n+a))+R*link+inner)) false
    ∃ k ≤ 46*n+19, TeamTapeInput.program.Runs k
      (TeamTapeInput.initial (List.ofFn (G.word pin ext int u j)))
      (TeamTapeInput.loaded (programPrefix p)
        (List.ofFn (free u j) ++ (fields.exterior j).flatten ++ fields.pins j ++ route ++ pad)
        (fields.row j) route) := by
  intro G fields route pad
  let width := (programPrefix p).length+(cutWidth n+a)
  have he : (fields.exterior j).flatten.length = R*link := by
    simpa only [fields,G,Wiring.pinLayout,tapeWiring,Nat.add_sub_cancel] using fields.exterior_length j
  have hp : (fields.pins j).length = width := fields.pins_length j
  have hr : route.length = inner := List.length_ofFn
  have hs : width+(fields.exterior j).flatten.length+(fields.pins j).length+route.length ≤ n := by
    rw [he,hp,hr]
    dsimp [width] at *
    omega
  have hc : (programPrefix p).length+4*Nat.clog 2 (n+1)+2+(List.ofFn (free u j)).length = width := by
    simp [width,cutWidth,Nat.add_assoc]
  obtain ⟨_,_,k,hk,run⟩ := TeamTapeInput.run_layout p n width (List.ofFn (free u j)) (fields.pins j)
    route (fields.exterior j) hc hs
  have hdata : fields.row j = TeamTapeInput.inputData
      (programPrefix p ++ TeamTapeInput.parameters (TeamTapeInput.digits n (2*width+R*link))
          (TeamTapeInput.digits n inner) ++ List.ofFn (free u j)) (fields.exterior j) (fields.pins j) := by
    unfold ProcessorFields.row
    change TeamTapeInput.inputData (programPrefix p ++ List.ofFn (cutTail _ _ _ _)) _ _ = _
    rw [ofFn_cutTail, List.append_assoc]
  have hraw := G.word_processorFields u j pin ext int ibase hbase starbase
  change List.ofFn (G.word pin ext int u j) = fields.row j ++ route ++ pad at hraw
  rw [he,hp,hr,show width+R*link+width = 2*width+R*link by omega, ← hdata] at run
  exact ⟨k,hk,hraw ▸ run⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
