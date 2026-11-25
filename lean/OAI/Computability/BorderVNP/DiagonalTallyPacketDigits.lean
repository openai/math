import OAI.Computability.BorderVNP.DiagonalCubeNetwork
import OAI.Computability.BorderVNP.DiagonalTallyGather

/-!
# Digit order in the fixed cube table

For a selected cube term and vertex the row bits are exactly the two kinds of demand
half-edges followed by the two kinds of incident supply half-edges. A fixed enumeration
of this finite digit type works for every packet using the cube identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Tally

open Crossing VPVNP.MotifBase VPVNP.RAMSerialization

/-- A single bit at an outgoing or incoming half-edge. -/
abbrev HalfBit {I V : Type} (src dst : I → V) (width : I → ℕ) (v : V) :=
  (Σ e : {e : I // src e = v}, Fin (width e.val)) ⊕
    (Σ e : {e : I // dst e = v}, Fin (width e.val))

/-- All local integer words at a vertex are encoded by their actual incidence digits. -/
def halfBits {I V : Type} (src dst : I → V) (width : I → ℕ) (v : V) :
    PortWords src dst width v ≃ (HalfBit src dst width v → Bool) where
  toFun z := Sum.elim
    (fun i => wordBits _ (z.1 i.1.val i.1.property.symm) i.2)
    (fun i => wordBits _ (z.2 i.1.val i.1.property.symm) i.2)
  invFun bits := (fun e he => (wordBits _).symm fun j => bits (.inl ⟨⟨e,he.symm⟩,j⟩),
    fun e he => (wordBits _).symm fun j => bits (.inr ⟨⟨e,he.symm⟩,j⟩))
  left_inv z := by
    apply Prod.ext <;> funext e he
    · exact (wordBits (width e)).symm_apply_apply (z.1 e he)
    · exact (wordBits (width e)).symm_apply_apply (z.2 e he)
  right_inv x := by
    funext i
    cases i with
    | inl i | inr i => simp

variable {n b h K s D : ℕ}

/-- The demand and supply data in one cube table row. -/
abbrev Row (u : Selector n K h) (v : Vertex (n+1)) :=
  DemandBasis n b h v × SupplyBasis s u v

/-- Individual bit positions in one row of the fixed table, including both ends
of any incident edge and every available digit of that end's word. -/
abbrev RowBit (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :=
  HalfBit (@start n) (@stop n) (fun _ => h*b) v ⊕
    HalfBit Prod.fst head (payload (onEdge s) u.2) v

/-- The old demands and selected supplies determine and are determined by the native bits. -/
def rowBits (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :
    Row (b := b) (s := s) u v ≃ (RowBit u v b s → Bool) :=
  ((halfBits (@start n) (@stop n) (fun _ => h*b) v).prodCongr
    (halfBits Prod.fst head (payload (onEdge s) u.2) v)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm

/-- The particular row supplied by the external words and shared incident edge assignments
of an individual packet. -/
def packetRow (D b s : ℕ) (u : Selector n K h) (v : Vertex (n+1))
    (y : (i : {e : (packetNetwork D b s u).Edge //
      (packetNetwork D b s u).src e = v ∨ (packetNetwork D b s u).dst e = v}) →
        Fin ((packetNetwork D b s u).width i.val) → Bool)
    (x : {p : Ends n // (packetNetwork D b s u).attach p = v} → Fin (h*b) → Bool) :
    Row (b := b) (s := s) u v :=
  (⟨fun e hv => (wordBits _).symm (x ⟨(e,false),hv.symm⟩),
    fun e hv => (wordBits _).symm (x ⟨(e,true),hv.symm⟩)⟩,
   ⟨fun e hv => (wordBits _).symm (y ⟨e,Or.inl hv.symm⟩),
    fun e hv => (wordBits _).symm (y ⟨e,Or.inr hv.symm⟩)⟩)

/-- Physical packet lookup identifies the full tagged table address, not just the value
of that row. Distinct positions can hold equal or zero field constants. -/
theorem packetTables_row {A : Type*} (ids : TableEntry n b h K s → A) (D : ℕ)
    (u : Selector n K h) (v : Vertex (n+1)) (y x) :
    packetTables ids D u v y x = ids ⟨u,v,packetRow D b s u v y x⟩ := rfl

/-- The Boolean digits of a selected row can be read directly from the physical ends
and incident edges. This reindexing introduces no fresh per-vertex cable assignments. -/
theorem packetRow_bits (u : Selector n K h) (v : Vertex (n+1)) (y x)
    (k : RowBit u v b s) :
    rowBits u v b s (packetRow D b s u v y x) k =
      match k with
      | .inl (.inl ⟨e,j⟩) => x ⟨(e.val,false),e.property⟩ j
      | .inl (.inr ⟨e,j⟩) => x ⟨(e.val,true),e.property⟩ j
      | .inr (.inl ⟨e,j⟩) => y ⟨e.val,Or.inl e.property⟩ j
      | .inr (.inr ⟨e,j⟩) => y ⟨e.val,Or.inr e.property⟩ j := by
  cases k with
  | inl k | inr k =>
    cases k with
    | inl k | inr k =>
      first
      | exact congrFun ((wordBits _).apply_symm_apply (x ⟨(_,false),k.1.property⟩)) k.2
      | exact congrFun ((wordBits _).apply_symm_apply (x ⟨(_,true),k.1.property⟩)) k.2
      | exact congrFun ((wordBits _).apply_symm_apply (y ⟨k.1.val,Or.inl k.1.property⟩)) k.2
      | exact congrFun ((wordBits _).apply_symm_apply (y ⟨k.1.val,Or.inr k.1.property⟩)) k.2

/-- Fixed number of physical digits for the given selector and vertex. -/
noncomputable def rowWidth (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) : ℕ :=
  Fintype.card (RowBit u v b s)

/-- The finite directory orders local digit positions once for all input lengths. -/
noncomputable def bitOrder (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :
    RowBit u v b s ≃ Fin (rowWidth u v b s) := Fintype.equivFin _

/-- Row-number correspondence used in the native table. -/
noncomputable def rowIndex (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :
    Row (b := b) (s := s) u v ≃ Fin (2^(rowWidth u v b s)) :=
  ((rowBits u v b s).trans ((bitOrder u v b s).arrowCongr (Equiv.refl _))).trans
    (wordBits _).symm

/-- List of actual incident bits for the most-significant-first indirect gather. -/
noncomputable def physicalDigits (u : Selector n K h) (v : Vertex (n+1))
    (r : Row (b := b) (s := s) u v) : List Bool :=
  (List.ofFn fun k => rowBits u v b s r ((bitOrder u v b s).symm k)).reverse

/-- Native accumulation of the physical digit list produces the exact finite table row. -/
theorem physicalDigits_index (u : Selector n K h) (v : Vertex (n+1))
    (r : Row (b := b) (s := s) u v) :
    DiagonalTallyGather.readDigits 0 (physicalDigits u v r) = (rowIndex u v b s r).val := by
  rw [physicalDigits,DiagonalTallyGather.readDigits_reverse]
  convert VPVNP.TapeWord.value_wordBits (rowIndex u v b s r) using 2
  unfold rowIndex VPVNP.BurstRAM.wordBits
  simp [Equiv.arrowCongr,Function.comp_def]

end Cube.Tally

end BorderVNP
end Computability
end OAI
