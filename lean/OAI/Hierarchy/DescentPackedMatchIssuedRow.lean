import OAI.Hierarchy.DescentPackedMatchTypedRows

namespace OAI
/-! # All twelve cells of an issued matching record from its genuine old typed pair -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "n" => binCount (2^k) A.degree
variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f) (profile : ℕ) (c : ScanColonies he A.stage)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pk" => slabPacking T A.cap (thinList home color c) (thickList home color c)
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)

theorem stream_size {r D p d : ℕ} (u : Panel r D p d) (key : ℕ) (side : Bool) :
    (stream u (binCount r D) key side).length≤entryCount r D p := by
  cases side with
  | false=>exact thin_length u _ _
  | true=>
    have bound (l : List (Fin (binCount r D))) : (l.flatMap (fun z=>thickBins u key z.val)).length≤l.length*(r*p) := by
      induction l with
      | nil=>simp
      | cons z l ih=>simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm (l.length*(r*p))] using
          Nat.add_le_add (thick_bin_length u key z.val) ih
    calc
      _ ≤ binCount r D * (r*p) := by
        simpa only [stream, ite_true, thickStream, List.length_finRange] using bound (List.finRange (binCount r D))
      _ = entryCount r D p := by unfold entryCount; ac_rfl

def issuedWords (e : Pair) (j : Fin (s).pairs) (atBin : ℕ) (pf : Fin (s).pairs→Cell (s).digit) : Fin 12→Cell (s).digit :=
  let a:=rawTriple A native S ready names he c false (picked A he c e false)
  let b:=rawTriple A native S ready names he c true (picked A he c e true)
  ![PackedMatch.short (s).digit 1,PackedMatch.short (s).digit j.val,PackedMatch.short (s).digit atBin,
    PackedMatch.short (s).digit (oldOffset A he c e false),PackedMatch.short (s).digit (oldOffset A he c e true),
    word (s).digit (a 0),word (s).digit (a 1),word (s).digit (a 2),word (s).digit (b 0),word (s).digit (b 1),word (s).digit (b 2),pf j]

private theorem triple_lt {r p D ceiling : ℕ} (block : Fin r) (slot : Fin p) (dest : Fin D)
    (room : (D+1)*r+r*p < ceiling) (f : Fin 3) :
    (![block.val*p+slot.val,block.val,dest.val*r+block.val] : Fin 3 → ℕ) f < ceiling := by
  have bx := block.isLt
  have sx := slot.isLt
  have ports := Nat.mul_le_mul_right p block.isLt
  have destinations := Nat.mul_le_mul_right r dest.isLt
  simp only [Nat.succ_mul] at ports destinations room
  fin_cases f
  · change block.val*p+slot.val < ceiling
    omega
  · change block.val < ceiling
    omega
  · change dest.val*r+block.val < ceiling
    omega

theorem raw_small (side : Bool) (e : Active A he c side) (f : Fin 3) :
    rawTriple A native S ready names he c side e f<2^(s).digit := by
  let q := event A he c side e
  exact triple_lt q.1 (address A native S ready ((addr c).1,q.1) q.2)
    (target A native S ready names ((addr c).1,q.1) q.2)
    (shape_width (2^k) A.degree (2*A.cap) profile).2.2.1 f

theorem raw_val (side : Bool) (e : Active A he c side) (f : Fin 3) :
    (word (s).digit (rawTriple A native S ready names he c side e f)).val=rawTriple A native S ready names he c side e f :=
  Nat.mod_eq_of_lt (raw_small A native S ready names he profile c side e f)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
include rank coord named fit winner sorted route df edgeOrder in
theorem issued_row (e : Pair) (pf : Fin (s).pairs→Cell (s).digit) :
    let x : PackedMatch.Inputs (s) := inputs s A.cap (heap (addr c).2) (panel (addr c).1) pf
    let M : PositiveAperture.Map
        (fun v : ScanColonies he A.stage => Fintype.card (ThickPool T (thickList home color c) v))
        (PackedMatch.cap x ∘ PackedLocalMatch.position (s).bins) := aperture (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c pf
    ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
      ∃b : {t : ScanColonies he A.stage // 0<Fintype.card (ThickPool T (thickList home color c) t)},b.val=e.1 ∧
      (decodeOutput s (lookupCell s (encodeInput x))).row j=
        issuedWords A native S ready names he profile c e j (PackedLocalMatch.position (s).bins (M.dest b).val).val pf := by
  intro x M
  let u : Panel (2^k) A.degree (2*A.cap) short := panel (addr c).1
  let key := heap (addr c).2
  let xs : List (List W.graph.Site) := thinPacks (live T) A.cap (thinList home color c)
  let f : List W.graph.Site → ℕ := DescentPacking.amount (live T)
  let orig (v : ScanColonies he A.stage) := Fintype.card (ThickPool T (thickList home color c) v)
  let num : Fin (Fintype.card (Pairs f (pk).decisions)) := pairNumber f (pk).decisions e
  have bounded : PackedMatch.Bounded x := shape_bounded profile A.cap key u pf
  have actual : PackedMatch.amount x = countIn he A c :=
    live_amount (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c pf
  have window : PackedMatch.amount x ≤ (s).pairs :=
    PackedLocalMatch.count_le_window (PackedMatch.need x) (PackedMatch.cap x) bounded.item
  let j : Fin (s).pairs := ⟨num.val, num.isLt.trans_le (actual.symm.le.trans window)⟩
  have measured : xs.length ≤ (s).packs ∧
      PackedMatch.need x = PackedLocalMatch.needs («n» := (s).packs) f xs :=
    measured_inputs (short:=short) A native S ready names win next he rank coord named fit winner route df profile c pf
  have wires (side : Bool) := picked_wire (short:=short) A native S ready names win next he c rank coord named fit winner sorted route df edgeOrder e side
  have off (side : Bool) : oldOffset A he c e side < (s).entries :=
    (wires side).1.trans_le (stream_size u key side)
  have token : e.2.2.val < (s).limit := by
    have h := off false
    change PairRAM.rawOffset W.graph W.core home color A.cap c e.2.1.val + e.2.2.val < (s).limit at h
    exact (Nat.le_add_left _ _).trans_lt h
  obtain ⟨b,selected,r,seen,accepted,bin_,thin_,thick_⟩ :=
    PackedLocalMatch.Holes.dense (C:=ScanColonies he A.stage) (I:=List W.graph.Site)
      («n» := (s).packs) (b:=(s).bins) (limit:=(s).limit) f xs orig (PackedMatch.cap x) M measured.1 e token
  have tpos : r.thin = oldOffset A he c e false := by
    change r.thin = PairRAM.rawOffset W.graph W.core home color A.cap c e.2.1.val + e.2.2.val
    refine thin_.trans (congrArg (· + e.2.2.val) ?_)
    unfold PairRAM.rawOffset ProtocolRAMPortRanks.«prefix»
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases early : j.val < e.2.1.val.val
    · rw [ite_eq_left early, ite_eq_left early]
      rfl'
    · simp only [ite_eq_right early]
  have hpos : r.thick = oldOffset A he c e true := thick_
  have found : PackedLocalMatch.dense (PackedMatch.need x) (PackedMatch.cap x) (s).limit j.val = some r := by
    rw [measured.2]
    exact seen
  have t : r.thin < (s).entries := tpos.le.trans_lt (off false)
  have h : r.thick < (s).entries := hpos.le.trans_lt (off true)
  have thin (z : Fin 3) : x.thin ⟨r.thin,t⟩ z =
      word (s).digit (rawTriple A native S ready names he c false (picked A he c e false) z) := by
    change word (s).digit (triple u (stream u n key false) r.thin z) = _
    rw [tpos]
    exact congrArg (word (s).digit) ((wires false).2 z)
  have thick (z : Fin 3) : x.thick ⟨r.thick,h⟩ z =
      word (s).digit (rawTriple A native S ready names he c true (picked A he c e true) z) := by
    change word (s).digit (triple u (stream u n key true) r.thick z) = _
    rw [hpos]
    exact congrArg (word (s).digit) ((wires true).2 z)
  refine ⟨j,rfl,b,selected,?_⟩
  simp only [lookupCell,decode_encode,output_inverse,transform,found,dite_eq_left (And.intro t h)]
  simp only [describe,issuedWords,thin,thick]
  simp only [accepted,bin_,tpos,hpos]; rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
