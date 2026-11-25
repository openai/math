import OAI.Computability.MultitapeWeakETH.NamedPackets
import OAI.Computability.MultitapeWeakETH.PlacedPackets
import OAI.Computability.VPVNP.PairShrinkRoleMapWitness

/-! # The private memory containing a placement fiber's independent child packets -/

namespace OAI.Computability.MultitapeWeakETH.NamedPackets

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open NetworkKernel PairSimulation LocalHistory NodeArguments NativeGrid
open private ordinalWord ordinalWord_poly from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open private encoded_short from OAI.Computability.MultitapeWeakETH.TerminalLayout
open scoped Classical Fin.CommRing
noncomputable section

/-- Convert the ordered unary child identifiers to keys of the level's native width. -/
def keys (q : Bits.Word × List Tally) := q.2.map fun j => ordinalWord (q.1,j)

theorem keys_poly : Poly keys := Poly.push [] [] ordinalWord_poly

theorem keys_eq {w : ℕ} (head : Word w) (ids : List ℕ) :
    keys (wordBits head,ids.map tally) = ids.map (fun j : ℕ => wordBits (j : Word w)) := by
  simp only [keys,List.map_map,Function.comp_def,ordinalWord,length_wordBits,tally_length]
  exact List.map_congr_left (fun i _ => (encoded_short w i).symm)

variable {a g : ℕ} {U : Type} (X : State a g) (place : X.network.Site → U) (v : U)
  (o : Order {u // v = place u}) (h : Placed place X.network.Half v)

def placedBank (w : ℕ) : Bank :=
  (List.ofFn (fun j => wordBits ((((siteOrder X).entries.symm (o.entries j).val).val : ℕ) : Word w)),
    List.ofFn (fun j => packed X (o.entries j).val (h _ (o.entries j).prop)))

private theorem fetch_placed {w : ℕ} (room : (siteOrder X).length ≤ 2^w)
    (u : X.network.Site) (hu : v = place u) :
    ShrinkHidden.fetch (wordBits ((((siteOrder X).entries.symm u).val : ℕ) : Word w),
      placedBank X place v o h w) = packed X u (h u hu) := by
  let j := o.entries.symm ⟨u,hu⟩
  let ord (j : Fin o.length) := (siteOrder X).entries.symm (o.entries j).val
  let num (j : Fin o.length) := ((ord j).val : Word w)
  let field (j : Fin o.length) := packed X (o.entries j).val (h _ (o.entries j).prop)
  have inject : Function.Injective num := by
    intro x y eqn
    have same := congrArg Fin.val eqn
    change ((ord x).val : Word w).val = ((ord y).val : Word w).val at same
    rw [Fin.val_cast_of_lt ((ord x).isLt.trans_le room),Fin.val_cast_of_lt ((ord y).isLt.trans_le room)] at same
    exact o.entries.injective (Subtype.ext ((siteOrder X).entries.symm.injective (Fin.ext same)))
  have read := ShrinkHidden.fetch_at num field (List.finRange o.length) j (List.mem_finRange j)
    (fun d _ eqn => congrArg field (inject eqn))
  have atJ : o.entries j = ⟨u,hu⟩ := o.entries.apply_symm_apply _
  have result : field j = packed X u (h u hu) :=
    congrArg (fun z : {x // v = place x} => packed X z.val (h z.val z.prop)) atJ
  simpa only [placedBank,List.ofFn_eq_map,Function.comp_def,num,ord,field,atJ] using read.trans result

/-- A single polynomial bit reader realizes the native private packet contract
for every child in the fiber, with row addressing by the original state ordinal. -/
theorem placed_memory :
    ∃ read : Input → Bool, Poly read ∧ ∀ {a g w : ℕ} {U : Type} (X : State a g)
      (place : X.network.Site → U) (v : U) (o : Order {u // v = place u})
      (h : Placed place X.network.Half v) (stride : ℕ),
      let bank := placedBank X place v o h w
      let mem (addr : Word w) := PrivateFields.bitValue w (read ((bank,wordBits (stride : Word w)),wordBits addr))
      (siteOrder X).length ≤ 2^w → stride < 2^w → (siteOrder X).length*stride ≤ 2^w →
      (∀ u (hu : v = place u), (packed X u (h u hu)).length ≤ stride) →
      ∀ u (hu : v = place u),
        let P := Packet.mk ((siteOrder X).entries.symm u).val (packed X u (h u hu))
        P.Fits ⟨0,stride⟩ w 0 ∧ P.Stored ⟨0,stride⟩ (DFS.scratch 0 mem) := by
  obtain ⟨read,cost,run⟩ := cell_program
  refine ⟨read,cost,?_⟩
  intro a g w U X place v o h stride bank mem room sf space width u hu P
  have length := width u hu
  have enough := Nat.mul_le_mul_right stride ((siteOrder X).entries.symm u).isLt
  rw [Nat.succ_mul] at enough
  exact run bank stride _ _ sf length ((Nat.add_le_add_left length _).trans (enough.trans space))
    (fetch_placed X place v o h room u hu)

end
end OAI.Computability.MultitapeWeakETH.NamedPackets
