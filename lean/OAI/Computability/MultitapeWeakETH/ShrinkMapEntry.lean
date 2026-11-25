import OAI.Computability.MultitapeWeakETH.ShrinkMapRecord
import OAI.Computability.MultitapeWeakETH.MotifBuffers
import OAI.Computability.VPVNP.PairShrinkRoleMapWitness

/-! # Running a selected resident shrinking map with its incident bit fields -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication Code VPVNP BurstRAM Compression Compression.ShrinkMotif
open CompressorRecords DescriptorSpace PhaseRecipe PairSimulation ShrinkBlockInputs MapResidentRows
open StackInterpreter MotifGrid MotifBlocks MotifConversion LocalHistory NativeGrid TerminalWords
open private publicWords from OAI.Computability.MultitapeWeakETH.ShrinkHiddenRecipe
open scoped Classical Fin.CommRing
noncomputable section

private def label (bs : Bits.Word) : Label (Fin 6) :=
  Iter.pick ⟨0⟩ (List.ofFn (Label.mk (Q:=Fin 6)),capped (bs,tally 6))

private theorem label_poly : Poly label :=
  ((Code.Poly.const _).pair ((Poly.identity.pair (Code.Poly.const _)).compose capped_poly)).compose (Iter.facile _).poly

private theorem label_eq {w : ℕ} (v : Fin 6) (hw : 6 < 2^w) :
    label (wordBits (v.val : Word w)) = ⟨v⟩ := by
  simp only [label,capped,value_native,Fin.val_cast_of_lt (v.isLt.trans hw),tally_length,
    Nat.min_eq_left v.isLt.le,Iter.entry]

variable {A k : Type} [Codec A] [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "Q" => ShrinkHidden.Indexed A
variable (read : A × Bits.Word → Bits.Word) (hr : Poly read)
variable (readD : Bool × Bool → ShrinkHidden.Indexed A × Tally → Bits.Word)
  (readS : Bool × (Bool × Fin 4) → ShrinkHidden.Indexed A × Tally → Bits.Word)

include hr in
set_option maxHeartbeats 1800000 in
/-- The selected occurrence's own demand and term rows supply the numerical parameters.
The four field equations concern only the endpoints incident to its actual party. -/
theorem entry_program (hd : ∀ d : Bool × Bool, Poly (readD d)) (hs : ∀ s : Bool × (Bool × Fin 4), Poly (readS s))
    (number : (parameterData B.shrink).Entry → ℕ) :
    ∃ run : Q → Option (List Tally), Poly run ∧ ∀ {w g : ℕ} (ctx : A)
      (X : State (a i) (packingLaneBits (a i) g)) (sel : SelectedScore.Selection B X)
      (base : Word w) (positions blocks n cur cap : ℕ) (mem : Memory w)
      (v : Site X) (j : Fin (order X (SelectedFinish.chosen B X sel) v).length),
      let L := BlockProgram.layout B base.val positions blocks
      let e := entry X (SelectedFinish.chosen B X sel) v j
      let q : Q := (ShrinkHidden.query ctx ((levelStart L cur : ℕ) : Word w) cap (siteIndex X v).val,tally j.val)
      ∀ I : EntryInput B.shrink,
      (∀ p : Word w, read (ctx,wordBits p) = wordBits (mem p.val)) →
      CompiledResident.ShrinkPayload B base positions blocks n cur i X sel mem →
      I.party = e.2 → I.demand = X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth e.1 →
      I.payload = (sel e.1).val → X.maxWireWidth ≤ cap → fieldFactor B.shrink * (X.maxWireWidth+1) ≤ cap →
      cap < 2^w →
      (∀ d (h : I.party=demandSource d), readD (false,d) (q,tally (I.demand d)) =
        List.ofFn (MotifEntry.inputBits (I.demandBits.1 d h))) →
      (∀ d (h : I.party=demandTarget d), readD (true,d) (q,tally (I.demand d)) =
        List.ofFn (MotifEntry.inputBits (I.demandBits.2 d h))) →
      (∀ s (h : I.party=supply.src s), readS (false,s) (q,tally (supplyWidths B.shrink I.demand I.payload s)) =
        List.ofFn (MotifEntry.inputBits (I.supplyBits.1 s h))) →
      (∀ s (h : I.party=supply.dst s), readS (true,s) (q,tally (supplyWidths B.shrink I.demand I.payload s)) =
        List.ofFn (MotifEntry.inputBits (I.supplyBits.2 s h))) →
      run q = (ShrinkRole.MapWitness.names B I).map (List.map (tally ∘ number)) := by
  choose eval cost correct using ShrinkHidden.expression read hr
  let getParty (q : Q) := label (eval (party (a i)) q)
  let get (e : Expr) (q : Q) := capped (eval e q,q.1.1.2)
  let I₀ := inputs (a i)
  let make := MotifFields.bufferInput B.shrink getParty (fun d => get (I₀.demand d)) (fun e => get (I₀.payload e)) readD readS
  have costGet (e : Expr) : Poly (get e) := ((cost e).pair (show Poly (fun q : Q => q.1.1.2) by fun_prop)).compose capped_poly
  have cc : Poly make := MotifFields.bufferInput_poly _ _ _ _ _ _ ((cost (party _)).compose label_poly)
    (fun _ => costGet _) (fun _ => costGet _) hd hs
  obtain ⟨block,bc,run⟩ := MotifFields.fixed_program B.shrink demandMass_pos number
  refine ⟨fun q => block (make q),cc.compose bc,?_⟩
  intro w g ctx X sel base positions blocks n cur cap mem v j L e q I rd data pp dd ss dw pw limit outD inD outS inS
  let p : Fin 5 → Word w := publicWords (siteIndex X v).val j.val
  let head := (levelStart L cur : Word w)
  have ev (op : Expr) : eval op q = wordBits (Expr.eval p head mem op) := correct op ctx head cap _ _ mem rd
  have partyEq := (item_read B i X sel base positions blocks n cur mem data v j p rfl rfl).2
  obtain ⟨demand,payload,_⟩ := item_fields B i X sel base positions blocks n cur mem data v j p rfl rfl
  have fit := data.words.oldRoom
  have who : getParty q = ⟨I.party⟩ := by
    unfold getParty
    rw [ev]
    exact (congrArg label (congrArg wordBits partyEq)).trans ((label_eq e.2 (by omega)).trans (congrArg Label.mk pp.symm))
  have sizes (op : Expr) (k : ℕ) (val : Expr.eval p head mem op = (k : Word w)) (ok : k ≤ cap) :
      get op q = tally k := by
    change tally (min (Bits.value (eval op q)) (tally cap).length) = _
    rw [ev,val,value_native,Fin.val_cast_of_lt (ok.trans_lt limit),tally_length,Nat.min_eq_left ok]
  have dwidth (d : Bool) : get (I₀.demand d) q = tally (I.demand d) := by
    rw [dd]
    exact sizes _ _ (demand d) ((X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _)
      (Nat.two_pow_pos _) X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) e.1 d).trans dw)
  have pwidth (s : Bool × Fin 4) : get (I₀.payload s) q = tally (I.payload s) := by
    rw [ss]
    have h := X.packingData.shrinkTerm_bounds (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) B.shrink e.1 (sel e.1)
    exact sizes _ _ (payload s) ((h.2 s).1.trans pw)
  have sync : make q = MotifFields.fixedInput B.shrink I :=
    MotifFields.bufferInput_eq _ _ _ _ _ _ q I who dwidth pwidth outD inD outS inS
  exact (congrArg block sync).trans (run I)

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
