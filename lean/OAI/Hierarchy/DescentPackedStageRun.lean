import OAI.Hierarchy.DescentPackedPhasePrice
import OAI.Hierarchy.DescentPackedGroupChoices
import OAI.Hierarchy.DescentGroupedCellRank

namespace OAI
/-! # The measured grouped six-party stage in the real packed chooser -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentPackedColony DescentColonies DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C L k ℓ Δ d b w hBits : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
private theorem packed_digit {a H G M w : ℕ} (f : Fin H→Fin G→Cell a) (hm : 0<M) (width : a*M≤w)
    (v : Fin H) (g : Fin G) :
    digit a (lane g hm).val ((↑(data f (position v g hm)).val:Word w).val)=(f v g).val := by
  let p := position v g hm
  let j := lane g hm
  have coord : p.2.val*M+j.val=g.val := Nat.div_add_mod' ..
  have fit := (data f p).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) width)
  rw [Fin.val_cast_of_lt fit]
  change digit a j.val (data f p).val = (f v g).val
  unfold data
  rw [digit_encode]
  simp only [dite_eq_left (coord.trans_lt g.isLt)]
  exact congrArg (fun i=>(f v i).val) (Fin.ext coord)

local notation "fee" => A.wire*(A.z*G.b)
local notation "D" => DescentHostDegree.gap A.degree
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v:W.graph.Site=>Finset.card (Finset.filter (fun edge => W.graph.src edge = v) W.core)
local notation "wt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev full g))
local notation "amt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev outgoing g))
local notation "M" => lanes hBits (Phase.unit k b)

/-- The complete bank includes the true computed value on each padded host. -/
def WinnerWords (rs : DynamicSplit.Roster ℓ Δ) (lanesPerWord base : ℕ) (i : Fin (2^k-1)) (j : Candidate k) (out : Memory w) : Prop :=
  ∀(x : Block k) (p : Row (2^ℓ) C lanesPerWord),out (PackedWinnerRAM.slot base (2^ℓ*chunks C lanesPerWord) x+(row (2^ℓ) C lanesPerWord p).val)=
    ((data (fun v g=>PackedWinnerKey.value A.fieldBits i j x (PackedSplit.state (DynamicSplit.incoming rs) wt D cap
      (modulus A.fieldBits) (seedAt k i) v g)) p).val:Word w)

/-- The two issued ordinals and per-old-site matching outputs all come from the
same return. Cost is measured in bits, including all candidate ROM scans. -/
theorem packed_ordinary (he : 0≤ε) (S : Phase.Shelves k Δ) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (space : Phase.Space S w (2^ℓ) C b M) (wide : 2*Phase.unit k b≤hBits) (emb : hBits≤w)
    (K : ℕ) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (m : Memory w) (initial : Phase.Initial S A.fieldBits rs wt amt D cap b M m) :
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<M,
      (Phase.program S w (2^ℓ) C M).Exec m out (Phase.cost S w (2^ℓ) C M) ∧
      Phase.cost S w (2^ℓ) C M*w≤K*(Phase.factor k Δ*(hBits+2^ℓ*hBits+4*2^ℓ*C*Phase.unit k b)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<S.first,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C M)≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs M S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C M) (A.block u)+(row (2^ℓ) C M (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat := by
  have unitPos : 0<Phase.unit k b := by dsimp [Phase.unit];omega
  have hm := (occupancy hBits (Phase.unit k b) unitPos wide).1
  have each (g v x) : wt g v x<2^b := by
    dsimp only [Padded.table];split
    · exact (A.small _ x).trans_lt short
    · exact Nat.two_pow_pos _
  have multPos : 0<fee := Nat.mul_pos A.wirePos (Nat.mul_pos A.unitPos (by have:=G.paid;omega))
  have capRoom : A.cap<2^b := (Nat.le_mul_of_pos_left A.cap multPos).trans_lt short
  obtain ⟨out,i,j,run,seed,paint,readSeed,readPaint,frame,high,fields⟩:=Phase.execute S space A.fieldBits hm rs wt amt D cap each
    (fun g v x=>(A.grouped_outgoing_cap (ℓ:=ℓ) ej ev g v x).trans_lt capRoom) leaves
    (by rw [A.grouped_outgoing_total ej ev h];exact budget) m initial
  obtain ⟨scanned,muEq,paintEq⟩:=A.grouped_named he ej ev h rs members (seedAt k i) j seed paint
  refine ⟨out,i,j,hm,run,Phase.payload_price S w hBits (2^ℓ) C b K wide hardware,scanned,
    readSeed,readPaint,frame,high,muEq,paintEq,fields,?_⟩
  intro u
  dsimp only
  rw [fields,packed_digit _ hm ((Phase.output_lanes k b hBits).trans emb),PackedWinnerKey.value_actual,
    A.grouped_cell_at ej ev h rs members (seedAt k i) u]
  rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
