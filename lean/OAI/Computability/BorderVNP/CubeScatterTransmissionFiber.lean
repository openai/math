import OAI.Computability.BorderVNP.CubeScatterTransmissionRecovery
import OAI.Computability.BorderVNP.CubeScatterCoownedTape

/-! # Multiplicity one for the physical transmission of a cube term

The family of local tapes depends only on the original public record columns
and the prescribed cube words. Its complete physical exterior is constructed
from the forced data, the common header and those same cube words. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w}
variable {before : Fin (R+1) → Memory w} {dst ib hb sb : Fin (R+1) → ℕ}
variable {guess : Fin (R+1) → ℕ → Bool}
variable {a q blocks K h : ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}

/-- Exterior assignment of a term carrying the given full binary header and
the original compact data and shared rows of its public schedule. -/
noncomputable def cubeExterior (G : Wiring R r t d link inner n Edge) (L : WireLayout (R+1) r link)
    (tab : TableLayout) (row : ℕ → TableRow) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (guess : Fin (R+1) → ℕ → Bool) (g : SharedRows.Layout) (raw : Symbols q → List Bool)
    (header : List Bool) (length : header.length = L.header) : Exterior R r link → Bool :=
  JointHeader.exterior L header length (tab.recordPayload row (G.assignedRows guess D pp lp
    (fun i => assignedShared g raw i.val)))

/-- Exactly one family of full native route returns carries the term's prescribed
local tapes. This is a statement on genuine returning event histories from each
team's populated input RAM. It permits arbitrary co-ownership and zero-width
rows and imposes no additional exterior check on the given canonical input. -/
theorem unique_assigned_routes (header : List Bool) (len : header.length = L.header)
    (raw : Symbols q → List Bool) (lengths : ∀ p, (raw p).length = SharedRows.reserved blocks K h decl p)
    (input : SharedRoutePrepared G pin (cubeExterior G L tab row D pp lp guess g raw header len) L D pp lp
      owner origin stride tab row pub before dst ib hb sb guess)
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)
    (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) (fixed : Block (R+1)) :
    ∃! z : ∀ u, Returns route (pub u) (mac u) (regs u) (before u),
      ∀ u, (z u).val.1.flatMap TeamRAM.Event.choices = coownedStream tab row u (assignedShared g raw) := by
  let pay := tab.recordPayload (N := R+1) row (G.assignedRows guess D pp lp fun i => assignedShared g raw i.val)
  let ext := cubeExterior G L tab row D pp lp guess g raw header len
  have checked := (JointHeader.exterior_unique L fixed header len (fun _ _ _ => false) pay ext).mpr rfl
  obtain ⟨z,H,f,ft,fr,_,_,all⟩ := input.realize mac regs emitted fitted records count dataCount room frame raw lengths checked
  have tape (u : Fin (R+1)) : (z u).val.1.flatMap TeamRAM.Event.choices = coownedStream tab row u (assignedShared g raw) :=
    (all u).2.1.trans ((f.tableChoiceBits_eq_coownedStream u _).trans (by rw [ft,fr]))
  refine ⟨z,tape,?_⟩
  intro alt same
  funext u
  exact (all u).2.2.1 (alt u) ((same u).trans (tape u).symm)

/-- Every family of actual returned header copies and routes yields precisely
its layout-defined local tapes and canonical exterior, so the two sides of the
multiplicity statement name exactly the same assignment. -/
theorem recovered_route_fiber {ext : Exterior R r link → Bool}
    (input : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (header : ReturnedHeaders G pin ext L w) (fixed : Block (R+1))
    (mac : Fin (R+1) → TeamOpcode.Macros w 8) (regs : Fin (R+1) → Bank w)
    (z : ∀ u, Returns route (pub u) (mac u) (regs u) (before u))
    (emitted : ∀ u, g.Emitted (src u) (readings (before u))) (fitted : ∀ u, g.Fits w (src u))
    (records : tab.records = g.records) (count : tab.count = g.dataCount+g.groups.choose 2)
    (dataCount : (D.directory pp lp).length = g.dataCount) (room : g.banks+g.stride*g.groups^2 ≤ 2^w)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) :
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H (fun u => G.pinLayout u (ib u) (hb u) (sb u))),
      f.table = tab ∧ f.row = row ∧ SharedWriters f g src ∧
      ext = cubeExterior G L tab row D pp lp guess g (f.receivedRows g group) (JointHeader.observed L ext fixed)
        (JointHeader.observed_length ..) ∧ ∀ u, (H u).history.val.2 = (z u).val.2 ∧
        JointHeader.FlatAt (header.returned u).val.2.2 (header.dest u) (JointHeader.observed L ext fixed) ∧
        (z u).val.1.flatMap TeamRAM.Event.choices = coownedStream tab row u (assignedShared g (f.receivedRows g group)) := by
  obtain ⟨H,f,ft,fr,writer,he,all⟩ := input.recover header fixed mac regs z emitted fitted records count dataCount room frame
  let raw := f.receivedRows g group
  have target : ext = cubeExterior G L f.table f.row D pp lp guess g raw (JointHeader.observed L ext fixed)
      (JointHeader.observed_length ..) := he
  rw [ft,fr] at target
  refine ⟨H,f,ft,fr,writer,target,?_⟩
  intro u
  exact ⟨(all u).1,(all u).2.1,(all u).2.2.trans ((f.tableChoiceBits_eq_coownedStream u _).trans (by rw [ft,fr]))⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
