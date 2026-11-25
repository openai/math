import OAI.Computability.BorderVNP.PackedBankPacket
import OAI.Computability.BorderVNP.PackedBankShift

/-! # Physical origin and terminal packet emitters

The static word tapes cover the relocated profile, padding, and whole-bundle
ties at each fixed site. The terminal's gathered original bundle has an
interval tie for each incoming hook, emitted by the cut-descriptor pass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket

open Word BankCircuit CellSparse Crossing.Profile.Cell

/-- The site offset, header operands, and bases of canonical physical bundles. -/
abbrev SiteInput (D A : ℕ) := Option (Header D A ⊕ Slice D A)

variable {D A : ℕ} (b : ℕ)

private def header (h : Header D A) : WidthExpr (SiteInput D A) := .field (some (.inl h))

private def count (i : Option (Fin A)) : WidthExpr (SiteInput D A) := header (.inl i)

private def moved (r : Slice D A) (c : SliceColumn) : WidthExpr (SiteInput D A) :=
  .binary .add (.field none) (header (.inr (r,c)))

private def aux (r : Slice D A) : PortCode (SiteInput D A) := ⟨moved r .base,.const (lanes b r),.const 1⟩

private def phys (r : Slice D A) : PortCode (SiteInput D A) :=
  ⟨.field (some (.inr r)),.const (lanes b r),.const 1⟩

private def zero (r : Slice D A) : RecordCode (SiteInput D A) :=
  .zero (.const 1) (header (.inr (r,.padWidth))) ⟨moved r .padBase,.const 0,.const 1⟩

private def ties (i : Option (Fin A)) (r : Slice D A) : RecordCode (SiteInput D A) :=
  .equal (count i) (.const (lanes b r)) (phys b r) (aux b r)

private noncomputable def ordered {R T : Type*} [Fintype R] (f : R → T) : List T :=
  List.ofFn fun i : Fin (Fintype.card R) => f ((Fintype.equivFin R).symm i)

/-- Executable record templates at the origin, including the ties from the canonical spokes. -/
noncomputable def origin (first : Fin D × Bool) : List (RecordCode (SiteInput D A)) :=
  (.profile (count none) (aux b (.inl first)) (.const (Nat.clog 2 A)) (List.ofFn (fun a => count (some a))) [] ::
      ordered (fun u => .equal (count none) (.const (Nat.clog 2 A)) (aux b (.inl u)) (aux b (.inl first)))) ++
    ordered (fun u => zero (.inl u)) ++ ordered (fun u => ties b none (.inl u))

/-- Executable record templates at the terminal. Only the gathered original is filled
by the variable list of incoming cut-hook intervals. -/
noncomputable def terminal : List (RecordCode (SiteInput D A)) :=
  let original := aux b (.inr (.inr (.inl ())))
  let routes := List.ofFn fun a : Fin A =>
    (⟨.const a.val,.const b,original,aux b (.inr (.inr (.inr a)))⟩ : RouteCode (SiteInput D A))
  let head := RecordCode.profile (count none) (aux b (.inr (.inl ()))) (.const (Nat.clog 2 A))
    (List.ofFn (fun a => count (some a))) routes
  (head :: ordered (fun r => zero (.inr r))) ++
    (ties b none (.inr (.inl ())) :: List.ofFn (fun a => ties b (some a) (.inr (.inr (.inr a)))))

variable (x : SiteInput D A → ℕ)

/-- Header values at the assigned physical site. -/
def localHeader (h : Header D A) := x (some (.inl h))

/-- Canonical cell-bank port for one physical selector or feeder cable. -/
def physicalPort (r : Slice D A) : Port := ⟨x (some (.inr r)),lanes b r,1⟩

/-- A whole-cable tie produced by the site emitter. -/
def bind (i : Option (Fin A)) (r : Slice D A) : Record :=
  .equal (localHeader x (.inl i)) (lanes b r) (physicalPort b x r) ((readPort b (localHeader x) r).shift (x none))

private theorem aux_read (r : Slice D A) :
    (aux b r).read x = (readPort b (localHeader x) r).shift (x none) := rfl

/-- Exact flattened origin record sequence, with all cell-local address shifts already applied. -/
theorem origin_read (first : Fin D × Bool) :
    (origin (A := A) b first).map (RecordCode.read x) =
      (originList b (localHeader x) first).map (fun r => r.shift (x none)) ++
        allRows (fun u => bind b x none (.inl u)) := by
  simp only [origin,originList,originRecords,allRows,ordered,List.map_append,List.map_cons,
    List.map_ofFn,Function.comp_def,RecordCode.read,aux_read,
    count,header,WidthExpr.eval,List.map_nil,Record.shift,localHeader]
  rfl

/-- Exact flattened terminal record sequence, including the canonical selector and feeder ties. -/
theorem terminal_read :
    (terminal (D := D) (A := A) b).map (RecordCode.read x) =
      (terminalList b (localHeader x)).map (fun r => r.shift (x none)) ++
        (bind b x none (.inr (.inl ())) :: List.ofFn fun a => bind b x (some a) (.inr (.inr (.inr a)))) := by
  simp only [terminal,terminalList,terminalRecord,Crossing.Profile.Cell.routes,allRows,ordered,
    List.map_append,List.map_cons,List.map_ofFn,Function.comp_def,RecordCode.read,aux_read,
    count,header,WidthExpr.eval,Record.shift,localHeader,RouteCode.read,Route.shift]
  rfl

end Packing.BankPacket

end BorderVNP
end Computability
end OAI
