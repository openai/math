import OAI.Computability.MultitapeWeakETH.HistoryField

/-! # Computing the exact number of private bits for a child argument -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM
open PairSimulation LocalHistory TerminalWords
open private address address_poly address_eq from OAI.Computability.MultitapeWeakETH.TerminalColumns
open scoped Fin.CommRing
noncomputable section

variable {A : Type} [Codec A] [Inhabited A] (read : A × Bits.Word → Bits.Word)

/-- Read the degree once and add the widths of this child's incident slots on both sides. -/
def packetSize (D : ℕ) (q : Query A) : Tally :=
  let deg := capped (read (q.1.1.1,address (q.1.1.2,tally 16)),tally D)
  let side (d : Bool) := ((Iter.lineup deg).map fun j => field read d (q,j)).flatten
  side false ++ side true

theorem packetSize_poly (hr : Poly read) (D : ℕ) : Poly (packetSize read D) := by
  have ctx : Poly (fun q : Query A => q.1.1.1) := by fun_prop
  have head : Poly (fun q : Query A => q.1.1.2) := by fun_prop
  have deg := ((((ctx.pair ((head.pair (Code.Poly.const (tally 16))).compose address_poly)).compose hr).pair
    (Code.Poly.const (tally D))).compose capped_poly).compose Iter.poly_line
  have side (d : Bool) := ((Poly.identity.pair deg).compose (Poly.push default [] (field_poly read hr d))).compose Easy.flatten.poly
  exact (side false).app (side true)

variable {w a g : ℕ} (X : State a g) (T : IncidenceDirectory w) (ctx : A) (m : Memory w)
  (rd : ∀ h : Word w, read (ctx,wordBits h)=wordBits (m h.val))

include rd
omit [Codec A] [Inhabited A] in
theorem packetSize_eq (head : Word w) (cap D : ℕ)
    (deg : m (head+16).val=((2^a : ℕ) : Word w)) (inv : m (head+19).val=T.actualIn)
    (wid : m (head+20).val=T.width) (cols : T.ActualColumns X m)
    (allow : X.maxWireWidth ≤ cap) (fit : X.maxWireWidth < 2^w) (bound : 2^a ≤ D) (dw : 2^a < 2^w)
    (v : X.network.Site) (h : X.network.Half v) :
    packetSize read D (((ctx,wordBits head),tally cap),tally ((siteOrder X).entries.symm v).val) =
      tally (NodeArguments.packed X v h).length := by
  let q : Query A := (((ctx,wordBits head),tally cap),tally ((siteOrder X).entries.symm v).val)
  have degree : capped (read (ctx,address (wordBits head,tally 16)),tally D) = tally (2^a) := by
    simp only [address_eq,Nat.cast_ofNat,rd,deg,capped,value_native,tally_length,Fin.val_natCast,Nat.mod_eq_of_lt dw,Nat.min_eq_left bound]
  have side (d : Bool) : (((Iter.lineup (tally (2^a))).map fun j => field read d (q,j)).flatten).length =
      ∑ j, X.halfWidth v d j := by
    have atSlot (j : Fin (2^a)) := field_eq read X T ctx m rd head cap deg inv wid cols allow fit v d j
    simp only [Iter.lined,List.map_ofFn,Function.comp_def,List.length_flatten]
    simp only [q,atSlot,tally_length,List.sum_ofFn]
  unfold packetSize
  rw [degree,← recover_tally (_ ++ _),List.length_append,side false,side true,NodeArguments.packed_length]
  simp [add_comm]

end
end OAI.Computability.MultitapeWeakETH.NativeGrid.ChildScan
