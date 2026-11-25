import OAI.Computability.BorderVNP.PackedDeckScoreCost

/-!
# Batched lookup of the two old sites of each cable

In a shortening epoch the public cable row contains its width and the two
site addresses. The public site row stores its local position, tile address,
and pointer to its private table. A single sort-and-scan circuit reads both
endpoint records for all cables, using the stable row numbers as table keys.
The cost counts public record bits and is independent of cable widths and
private table lengths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

/-- Fields of a public site record: the local-position tag, the coordinates
of its deck address, and its public table pointer. -/
abbrev SiteBit (tagBits coordinates addressBits pointerBits : ℕ) :=
  Fin tagBits ⊕ ((Fin coordinates × Fin addressBits) ⊕ Fin pointerBits)

/-- Public site payloads and cable rows in stable name order. Each cable
holds a width, source address (true), and destination address (false). -/
abbrev Inputs (FieldBit : Type*) (sites cables k w : ℕ) :=
  (Fin sites × FieldBit) ⊕ (Fin cables × (Fin w ⊕ (Bool × Fin k)))

/-- Joined endpoint records, retaining the original public arrays. -/
abbrev Outputs (FieldBit : Type*) (sites cables k w : ℕ) :=
  Inputs FieldBit sites cables k w ⊕ ((Fin cables × Bool) × FieldBit)

variable {FieldBit : Type*} {sites cables k w : ℕ}

/-- Decoded big-endian address at one end of a public cable row. -/
def address (x : Inputs FieldBit sites cables k w → Bool) (row : Fin cables) (source : Bool) : ℕ :=
  value (fun j => x (.inr (row, .inr (source,j))))

private noncomputable def table [Fintype FieldBit] (row : Fin sites) (j : Fin (Fintype.card FieldBit)) :
    Expr (Inputs FieldBit sites cables k w) :=
  .input (.inl (row,(Fintype.equivFin FieldBit).symm j))

private def request (q : Fin cables × Bool) (j : Fin k) : Expr (Inputs FieldBit sites cables k w) :=
  .input (.inr (q.1, .inr (q.2,j)))

/-- Join the dynamic source and target addresses of all cables against
the site array in one shared Boolean network. -/
noncomputable def join (FieldBit : Type*) [Fintype FieldBit] {sites cables k : ℕ} (w : ℕ)
    (fit : sites ≤ 2^k) :
    Frame (Inputs FieldBit sites cables k w) (Outputs FieldBit sites cables k w) :=
  ((PackedLookup.lookup (layout (Fin sites) (Fin cables × Bool)) (Fin.castLEEmb fit)
    table request).select (fun qj : (Fin cables × Bool) × FieldBit =>
      (qj.1,Fintype.equivFin FieldBit qj.2))).withInput

/-- Every public input row is still accessible after the join. -/
theorem join_input [Fintype FieldBit] (fit : sites ≤ 2^k)
    (x : Inputs FieldBit sites cables k w → Bool) (j : Inputs FieldBit sites cables k w) :
    (join FieldBit w fit).eval x (.inl j) = x j := Frame.withInput_eval_inl _ _ _

/-- Every bit of a valid source or target record agrees with the addressed
site's public data, even for repeated endpoint requests. -/
theorem join_bits [Fintype FieldBit] (fit : sites ≤ 2^k)
    (x : Inputs FieldBit sites cables k w → Bool) (row : Fin cables) (source : Bool)
    (site : Fin sites) (valid : address x row source = site.val) (j : FieldBit) :
    (join FieldBit w fit).eval x (.inr ((row,source),j)) = x (.inl (site,j)) := by
  rw [join, Frame.withInput_eval_inr, Frame.select_eval]
  have result := PackedLookup.lookup_bits (layout (Fin sites) (Fin cables × Bool))
    (Fin.castLEEmb fit) table request x (row,source) site valid (Fintype.equivFin FieldBit j)
  simpa only [table, Equiv.symm_apply_apply, StatementCircuit.Expr.eval] using result

/-- Gate bound with one physical lane per site or endpoint request up to
binary padding, and cubic overhead in address, row, and ordinal lengths. -/
theorem join_size (FieldBit : Type*) [Fintype FieldBit] {sites cables k : ℕ} (w : ℕ)
    (fit : sites ≤ 2^k) :
    (join (cables := cables) FieldBit w fit).size ≤
      300 * (sites + 2*cables + 1) *
        (Nat.clog 2 (sites + 2*cables) + k + Fintype.card FieldBit + 1)^3 := by
  let Q := Fin cables × Bool
  let b := PackedDeckScore.batchBits (Fin sites) Q
  have hb : b = Nat.clog 2 (sites+2*cables) := by
    simp [b, Q, PackedDeckScore.batchBits, Nat.mul_comm]
  have pad : 2^b ≤ 2*(sites+2*cables+1) := by
    by_cases hp : 0 < sites+2*cables
    · have := PackedHistogram.layout_size (Fin sites) Q (by simpa [Q, Nat.mul_comm] using hp)
      rw [hb]
      simp only [Q, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm cables] at this
      omega
    · have hz : sites+2*cables = 0 := Nat.eq_zero_of_not_pos hp
      simp [hb, hz]
  have base : (join (cables := cables) FieldBit w fit).size ≤
      PackedDeckScore.queryCost b k (Fintype.card FieldBit) := by
    rw [join, Frame.withInput_size, Frame.select_size]
    simpa only [PackedLookup.lookup, PackedDeckScore.queryCost, b, PackedDeckScore.batchBits, Nat.mul_one] using
      queries_size (layout (Fin sites) Q) (fun i => PackedHistogram.fixed (Fin.castLEEmb fit i))
        (table (FieldBit := FieldBit) (cables := cables) (k := k) (w := w)) request 1 le_rfl
        (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  calc
    _ ≤ 2^b * (150*(b+k+Fintype.card FieldBit+1)^3) := base.trans (PackedDeckScore.queryCost_le ..)
    _ ≤ (2*(sites+2*cables+1)) * (150*(b+k+Fintype.card FieldBit+1)^3) := Nat.mul_le_mul_right _ pad
    _ = _ := by rw [hb]; ring

end Shortening.PublicEndpoints

end BorderVNP
end Computability
end OAI
