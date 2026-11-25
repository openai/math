import OAI.Computability.BorderVNP.CellPacketGeometryHistoryKeys

/-! # Shared sparse lookup of every active history piece's final site and two relocation offsets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited FrozenTape ParseBatchSort ParseBatchCounts PackedHistogram VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {a C k w d t q : ℕ} {R B U V E σ : Type} [Fintype σ]
variable (S : Schema R B) (L : Schema U V) (A₀ : Access R B U V E σ a d t k w)
variable (hd : d≤q) (ht : t≤q) (room : a<2^q) (croom : C<2^k)

private noncomputable def columnID (k w : ℕ) : Column k w ≃ Fin (k+2*w) :=
  Fintype.equivOfCardEq (by simp [Column])

private def siteID : Fin (a+1) ↪ Fin (2^q) := ⟨fun i => ⟨i.val,Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt room)⟩,fun _ _ h => Fin.ext (congrArg (fun z : Fin (2^q) => z.val) h)⟩

private noncomputable def table (i : Fin (a+1)) (j : Fin (k+2*w)) : Expr σ :=
  let col := (columnID k w).symm j
  if h : i.val<a then .input (A₀.table ⟨i.val,h⟩ col) else col.elim (fixed ⟨C,croom⟩) (fun _ => .const false)

/-- One query per physical roster slot, shared by both offset fields and the
cell key. The extra table address has the skipped cell key and zero offsets. -/
noncomputable def sites : Frame σ (Fin (roster a S L).length × Column k w) :=
  let f := PackedLookup.lookup (layout (Fin (a+1)) (Fin (roster a S L).length)) (siteID room)
    (table A₀ croom) (fun i => request A₀ hd ht room ((roster a S L).get i))
  f.select fun z => (z.1,columnID k w z.2)

/-- Packed numeric address of an enabled owner or the sentinel. -/
def siteKey (r : Option (Fin a)) : Fin (a+1) := r.elim (Fin.last a) Fin.castSucc

private theorem key_value (u : Option (Fin a)) :
    (siteKey u).val = (u.elim (holeSlot a S L) (anchorSlot S L)).val := by cases u <;> rfl

/-- Every lookup recovers the actual site pin, or the appropriate inactive
cell/zero bits. This result is bitwise even for widths smaller than a machine word. -/
theorem sites_bits (x : σ → Bool)
    (old : ∀ r ∈ S.rows, x (A₀.history (.inl (r,.inl ()))) = true → owner (x ∘ A₀.history) r < a)
    (last : ∀ u ∈ L.rows, x (A₀.binding (.inl (u,.inl ()))) = true → owner (x ∘ A₀.binding) u < a)
    (i : Fin (roster a S L).length) (col : Column k w) :
    (sites S L A₀ hd ht room croom).eval x (i,col) =
      (siteOf (x ∘ A₀.history) (x ∘ A₀.binding) ((roster a S L).get i)).elim
        (col.elim ((numberWords k).symm ⟨C,croom⟩) (fun _ => false)) (fun j => x (A₀.table j col)) := by
  let opt := siteOf (x ∘ A₀.history) (x ∘ A₀.binding) ((roster a S L).get i)
  have h := request_value A₀ hd ht room S L x old last i
  have key : wordValue x (request A₀ hd ht room ((roster a S L).get i)) = (siteID room (siteKey opt)).val :=
    h.trans (key_value S L opt).symm
  have atCol := PackedLookup.lookup_bits (layout (Fin (a+1)) (Fin (roster a S L).length)) (siteID room)
    (table A₀ croom) (fun i => request A₀ hd ht room ((roster a S L).get i)) x i (siteKey opt) key (columnID k w col)
  refine (Frame.select_eval ..).trans (atCol.trans ?_)
  change (table A₀ croom (siteKey opt) (columnID k w col)).eval x = opt.elim _ _
  cases opt with
  | none => cases col <;> simp [siteKey,table,fixed,StatementCircuit.Expr.eval]
  | some j => simp [siteKey,table,j.isLt,StatementCircuit.Expr.eval]

/-- True finite gate cost of the sparse owner lookup; no scalar-field cap
or private description length enters this count. -/
def siteCost (a slots q k w : ℕ) :=
  let b := Nat.clog 2 ((a+1)+slots)
  let u := k+2*w
  2^b*((q+1+u)*8 + ((u+b)+1+q) + b^2*(24*((u+b)+1+q)+1) + u*(60*q+16*u+33) + b^2*(24*(u+b)+1))

theorem sites_size :
    (sites S L A₀ hd ht room croom).size ≤ siteCost a (roster a S L).length q k w := by
  have tabs (i : Fin (a+1)) (j : Fin (k+2*w)) : (table A₀ croom i j).size ≤ 8 := by
    unfold table
    split
    · simp [StatementCircuit.Expr.size]
    · cases (columnID k w).symm j <;> simp [fixed,StatementCircuit.Expr.size]
  have h := queries_size (layout (Fin (a+1)) (Fin (roster a S L).length)) (fun i => fixed (siteID room i))
    (table A₀ croom) (fun i => request A₀ hd ht room ((roster a S L).get i)) 8 (by decide)
    (fun _ _ => by simp [fixed,StatementCircuit.Expr.size]) tabs (fun i j => request_size A₀ hd ht room ((roster a S L).get i) j)
  simpa only [sites,Frame.select_size,PackedLookup.lookup,siteCost,Fintype.card_fin] using h

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
