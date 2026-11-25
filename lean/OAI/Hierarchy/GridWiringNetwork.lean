import OAI.Hierarchy.UniversalGrid
import OAI.ThreeFlat.BitNetwork.OrderedGlue
import OAI.ThreeFlat.RAM.ContractionGuess
import OAI.ThreeFlat.RAM.GuardedRecord

namespace OAI
/-! # The addressed contraction used by the evaluator on each legal selector

All copies of the replacement refer to its same eight-entry local tables. The
pair index is laid out with its two signs consecutive in the physical pin tape. -/

namespace Hierarchy.UniversalGrid.Wiring

open ThreeFlat
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {e L : ℕ} {P : Type} [Fintype P]

def railPin : GridDiagonal.Ends (Fin e) ≃ Fin (e*2) :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

theorem railPin_val (i : Fin e) (side : Bool) :
    (railPin (i,side)).val = 2*i.val + side.toNat := by
  cases side <;> simp [railPin,finProdFinEquiv_apply_val,Nat.mul_comm,finTwoEquiv]; omega

def source {h : ℕ} : Address (Fin e) h → BitSource h (e*2)
  | .inl i => .hidden i
  | .inr (.inl i) => .pin (railPin i)
  | .inr (.inr b) => .constant b

theorem source_read {h : ℕ} (x : GridDiagonal.Pins (Fin e)) (b : Bits h) (v : Address (Fin e) h) :
    (source v).read b (x ∘ railPin.symm) = bit x b v := by
  rcases v with i | i | t <;> simp [source,bit,BitSource.read]

private abbrev eqCell : BitNetwork F 2 where
  internal := 0
  cells := 1
  source _ := ![.pin 0,.pin 1,.constant false]
  table _ b := if b 0 = b 1 then 1 else 0

private theorem eqCell_eval (x : Fin 2 → Bool) :
    (eqCell : BitNetwork F 2).eval x = if x 0 = x 1 then 1 else 0 := by
  change (∑ _ : Fin 0 → Bool, ∏ _ : Fin 1, (if x 0=x 1 then (1:F) else 0)) = _
  simp

private structure Part (F : Type*) (e h : ℕ) where
  pins : ℕ
  net : BitNetwork F pins
  port : Fin pins → BitSource h (e*2)

variable (W : Wiring (Fin e) P L) (N : BitNetwork F (Fintype.card P))

def copyInput (c : Fin L) (j : Fin (Fintype.card P)) : BitSource W.internal (e*2) :=
  source (W.pin c ((Fintype.equivFin P).symm j))

private abbrev child (c : Fin L) : Part F e W.internal := ⟨_,N,W.copyInput c⟩

private abbrev guard (a : Fin W.equal.length) : Part F e W.internal :=
  ⟨_,eqCell,![source (W.equal.get a).1,source (W.equal.get a).2]⟩

private def parts : Fin (L+W.equal.length) → Part F e W.internal :=
  Fin.append (child W N) (guard W)

private theorem parts_child (c : Fin L) : parts W N (c.castAdd W.equal.length) = child W N c :=
  Fin.append_left _ _ _
private theorem parts_guard (a : Fin W.equal.length) : parts W N (Fin.natAdd L a) = guard W a :=
  Fin.append_right _ _ _

/-- The evaluator lays out private bits and three-pointer/eight-weight rows
in memory order, after the shared rail and alias bits. -/
def network : BitNetwork F (e*2) :=
  BitNetwork.Ordered.glue (fun i => (parts W N i).net) (fun i => (parts W N i).port)

theorem network_sizes :
    (W.network N).cells = L*N.cells+W.equal.length ∧
    (W.network N).internal = W.internal+L*N.internal := by
  have total (f : Part F e W.internal → ℕ) (copies edges : ℕ)
      (left : ∀ c, f (child W N c)=copies) (right : ∀ j, f (guard W j)=edges) :
      (∑ i,f (parts W N i)) = L*copies+W.equal.length*edges := by
    rw [Fin.sum_univ_add]
    have lc (c : Fin L) : f (parts W N (c.castAdd W.equal.length)) = copies :=
      (congrArg f (parts_child W N c)).trans (left c)
    have rc (j : Fin W.equal.length) : f (parts W N (Fin.natAdd L j)) = edges :=
      (congrArg f (parts_guard W N j)).trans (right j)
    simp only [lc,rc,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  have rows := total (fun z => z.net.cells) N.cells 1 (fun _ => rfl) (fun _ => rfl)
  have hidden := total (fun z => z.net.internal) N.internal 0 (fun _ => rfl) (fun _ => rfl)
  change ((∑ i,(parts W N i).net.cells)=_ ∧ W.internal+(∑ i,(parts W N i).net.internal)=_)
  exact ⟨by simpa only [Nat.mul_one] using rows,
    congrArg (W.internal+·) (by simpa only [Nat.mul_zero,Nat.add_zero] using hidden)⟩

theorem network_eval (x : GridDiagonal.Pins (Fin e)) :
    (W.network N).eval (x ∘ railPin.symm) =
      W.eval (fun z => N.eval (z ∘ (Fintype.equivFin P).symm)) x := by
  classical
  rw [network, BitNetwork.Ordered.glue_eval]
  unfold eval
  apply Finset.sum_congr rfl
  intro b _
  let weight (z : Part F e W.internal) := z.net.eval (fun j => (z.port j).read b (x ∘ railPin.symm))
  change (∏ i,weight (parts W N i)) = _
  rw [Fin.prod_univ_add]
  simp only [parts_child,parts_guard]
  have copy (c : Fin L) : weight (child W N c) =
      N.eval ((fun j => bit x b (W.pin c j)) ∘ (Fintype.equivFin P).symm) := by
    apply congrArg N.eval
    funext j
    exact source_read x b _
  have test (j : Fin W.equal.length) : weight (guard W j) =
      if bit x b (W.equal.get j).1 = bit x b (W.equal.get j).2 then 1 else 0 := by
    unfold weight guard
    rw [eqCell_eval]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,source_read]
  simp only [copy,test]
  split_ifs with agree
  · have ok (j : Fin W.equal.length) := agree (W.equal.get j) (List.get_mem _ _)
    simp only [ok,ite_true,Finset.prod_const_one,mul_one]
  · obtain ⟨uv,mem,bad⟩ := not_forall.mp agree |>.imp fun uv h => by
      simpa only [not_imp] using h
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp mem
    have zero : (if bit x b (W.equal.get j).1 = bit x b (W.equal.get j).2 then (1:F) else 0) = 0 :=
      ite_eq_right bad
    rw [Finset.prod_eq_zero (Finset.mem_univ j) zero,mul_zero]

/-- Index of a row of a specified component after concatenation. The
transport identifies its own row type with that of the actual component. -/
private def partRow (i : Fin (L+W.equal.length)) (B : Part F e W.internal)
    (same : parts W N i = B) (u : Fin B.net.cells) : Fin (W.network N).cells :=
  finSigmaFinEquiv (n:=fun i => (parts W N i).net.cells)
    ⟨i,u.cast (congrArg (fun V : Part F e W.internal => V.net.cells) same.symm)⟩

def copyRow (c : Fin L) (u : Fin N.cells) : Fin (W.network N).cells :=
  partRow W N (c.castAdd _) (child W N c) (parts_child W N c) u

def edgeRow (a : Fin W.equal.length) : Fin (W.network N).cells :=
  partRow W N (Fin.natAdd L a) (guard W a) (parts_guard W N a) 0

private theorem copy_prefix {M : ℕ} (f : Fin (L+M) → ℕ) (b : ℕ) (c : Fin L)
    (hf : ∀ i : Fin L, f (i.castAdd M) = b) :
    (∑ j : Fin (c.castAdd M).val, f (Fin.castLE (c.castAdd M).isLt.le j)) = c.val*b := by
  have term (j : Fin c.val) : f (Fin.castLE (c.castAdd M).isLt.le j) = b := by
    exact hf ⟨j.val,lt_trans j.isLt c.isLt⟩
  simp [term]

private theorem edge_prefix {M : ℕ} (f : Fin (L+M) → ℕ) (b d : ℕ) (a : Fin M)
    (hl : ∀ i : Fin L, f (i.castAdd M) = b) (hr : ∀ j : Fin M, f (Fin.natAdd L j) = d) :
    (∑ j : Fin (Fin.natAdd L a).val, f (Fin.castLE (Fin.natAdd L a).isLt.le j)) =
      L*b+a.val*d := by
  let incl : Fin (L+a.val) → Fin (L+M) := Fin.castLE (Fin.natAdd L a).isLt.le
  change (∑ j : Fin (L+a.val), f (incl j)) = _
  rw [Fin.sum_univ_add]
  have left (i : Fin L) : f (incl (i.castAdd a.val)) = b := hl i
  have right (j : Fin a.val) : f (incl (Fin.natAdd L j)) = d :=
    hr ⟨j.val,lt_trans j.isLt a.isLt⟩
  simp [left,right]

@[simp] theorem copyRow_val (c : Fin L) (u : Fin N.cells) :
    (W.copyRow N c u).val = c.val * N.cells + u.val := by
  unfold copyRow partRow
  rw [finSigmaFinEquiv_apply]
  exact congrArg (· + u.val) (copy_prefix (fun i => (parts W N i).net.cells) N.cells c
    (fun i => by rw [parts_child]))

@[simp] theorem edgeRow_val (a : Fin W.equal.length) :
    (W.edgeRow N a).val = L*N.cells + a.val := by
  unfold edgeRow partRow
  rw [finSigmaFinEquiv_apply]
  have prefixCount := edge_prefix (fun i => (parts W N i).net.cells) N.cells 1 a
    (fun i => by rw [parts_child]) (fun j => by rw [parts_guard])
  simpa only [Nat.mul_one,Nat.add_zero,Fin.val_cast,Fin.val_zero] using prefixCount

/-- The two bands exhaust the emitted flat buffer, even when one band is empty. -/
def rowEquiv : (Fin L × Fin N.cells) ⊕ Fin W.equal.length ≃ Fin (W.network N).cells :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (W.network_sizes N).1.symm)

@[simp] theorem rowEquiv_copy (c : Fin L) (u : Fin N.cells) :
    W.rowEquiv N (.inl (c,u)) = W.copyRow N c u := by
  apply Fin.ext
  rw [copyRow_val]
  change u.val + N.cells*c.val = c.val*N.cells + u.val
  ac_rfl

@[simp] theorem rowEquiv_edge (a : Fin W.equal.length) :
    W.rowEquiv N (.inr a) = W.edgeRow N a := by
  apply Fin.ext
  rw [edgeRow_val]; rfl

private theorem part_table (i : Fin (L+W.equal.length)) (B : Part F e W.internal)
    (same : parts W N i = B) (u : Fin B.net.cells) :
    (W.network N).table (partRow W N i B same u) = B.net.table u := by
  subst B
  exact BitNetwork.Ordered.table_at (fun j => (parts W N j).net) (fun j => (parts W N j).port) ⟨i,u⟩

open RAM.BitLayout

private def sourceNumber (i : Fin (L+W.equal.length)) (B : Part F e W.internal) :
    BitSource B.net.internal B.pins → ℕ
  | .constant v => v.toNat
  | .pin j => sourceAddress (B.port j)
  | .hidden k => hiddenBase (e*2) + W.internal +
    (∑ j : Fin i.val, (parts W N (Fin.castLE i.isLt.le j)).net.internal) + k.val

private theorem part_source (i : Fin (L+W.equal.length)) (B : Part F e W.internal)
    (same : parts W N i = B) (u : Fin B.net.cells) (j : Fin 3) :
    sourceAddress ((W.network N).source (partRow W N i B same u) j) =
      sourceNumber W N i B (B.net.source u j) := by
  subst B
  let net := fun z => (parts W N z).net
  let wire := fun z => (parts W N z).port
  change sourceAddress ((BitNetwork.Ordered.glue net wire).source
    (finSigmaFinEquiv (⟨i,u⟩ : BitNetwork.Ordered.Row net)) j) = _
  rw [BitNetwork.Ordered.source_at]
  have resolveAddress (s : BitSource (net i).internal (parts W N i).pins) :
      sourceAddress (BitNetwork.Ordered.resolve net wire i s) = sourceNumber W N i (parts W N i) s := by
    cases s with
    | constant b => rfl
    | pin v =>
      unfold BitNetwork.Ordered.resolve sourceNumber
      change sourceAddress _ = sourceAddress (wire i v)
      cases hv : wire i v <;> simp [hv,sourceAddress,BitNetwork.Ordered.privateEquiv]
    | hidden v =>
      change hiddenBase (e*2) + (BitNetwork.Ordered.privateEquiv (h:=W.internal) net (.inr ⟨i,v⟩)).val =
        hiddenBase (e*2) + W.internal + (∑ t : Fin i.val, (net (Fin.castLE i.isLt.le t)).internal) + v.val
      rw [BitNetwork.Ordered.private_offset]
      ac_rfl
  exact resolveAddress _

theorem copy_table (c : Fin L) (u : Fin N.cells) :
    (W.network N).table (W.copyRow N c u) = N.table u :=
  part_table W N _ _ (parts_child W N c) u

theorem copy_address (c : Fin L) (u : Fin N.cells) (j : Fin 3) :
    sourceAddress ((W.network N).source (W.copyRow N c u) j) =
      RAM.GuardedRecord.mapped N W.copyInput c (N.source u j) := by
  unfold copyRow
  rw [part_source]
  change sourceNumber W N _ (child W N c) (N.source u j) = _
  cases h : N.source u j with
  | constant b => rfl
  | pin v => rfl
  | hidden v =>
    have count := copy_prefix (fun z => (parts W N z).net.internal) N.internal c
      (fun i => by rw [parts_child])
    exact congrArg (fun m => hiddenBase (e*2) + W.internal + m + v.val) count

theorem edge_table (a : Fin W.equal.length) (v : Fin 3 → Bool) :
    (W.network N).table (W.edgeRow N a) v = if v 0 = v 1 then 1 else 0 :=
  congrFun (part_table W N _ _ (parts_guard W N a) 0) v

theorem edge_address (a : Fin W.equal.length) (j : Fin 3) :
    sourceAddress ((W.network N).source (W.edgeRow N a) j) =
      if j = 0 then sourceAddress (source (W.equal.get a).1) else
      if j = 1 then sourceAddress (source (W.equal.get a).2) else 0 := by
  unfold edgeRow
  rw [part_source]
  fin_cases j <;> rfl

/-- The eleven actual RAM words for a copied table row. -/
theorem copy_record {w : ℕ} (code : RAM.FieldCode F w) (c : Fin L) (u : Fin N.cells) (j : Fin 11) :
    record (W.network N) code (W.copyRow N c u) j =
      if hj : j.val < 3 then Fin.ofNat _ (RAM.GuardedRecord.mapped N W.copyInput c (N.source u ⟨j.val,hj⟩))
      else record N code u j := by
  by_cases hj : j.val < 3
  · simp only [record,dite_eq_left hj]
    exact congrArg (Fin.ofNat _) (W.copy_address N c u ⟨j.val,hj⟩)
  · simp only [record,dite_eq_right hj,copy_table]

/-- The three addresses and eight encoded entries at an appended equality row. -/
theorem edge_record {w : ℕ} (code : RAM.FieldCode F w) (a : Fin W.equal.length) (j : Fin 11) :
    record (W.network N) code (W.edgeRow N a) j =
      if j.val = 0 then Fin.ofNat _ (sourceAddress (source (W.equal.get a).1)) else
      if j.val = 1 then Fin.ofNat _ (sourceAddress (source (W.equal.get a).2)) else
      if j.val = 2 then 0 else
        if (j.val-3).testBit 0 = (j.val-3).testBit 1 then code.encode 1 else code.encode 0 := by
  by_cases hj : j.val < 3
  · simp only [record,dite_eq_left hj]
    rw [edge_address]
    have cases' : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
    rcases cases' with h | h | h <;> simp [Fin.ext_iff,h]
  · have h0 : j.val ≠ 0 := by omega
    have h1 : j.val ≠ 1 := by omega
    have h2 : j.val ≠ 2 := by omega
    simp only [record,dite_eq_right hj,edge_table,h0,h1,h2,ite_false,bits]
    change code.encode (if (j.val-3).testBit 0 = (j.val-3).testBit 1 then 1 else 0) = _
    exact apply_ite _ _ _ _

/-- For the real native contraction instruction set the selected grid row has
exactly one physical multiplicative evaluation for every internal guess. -/
theorem native_value [Fintype F] {w : ℕ} (fit : RAM.Contraction.Fits (W.network N) w)
    (x : GridDiagonal.Pins (Fin e)) (scratch : Fin (W.network N).internal → Bool)
    (extra : ℕ) (rest : Computability.VPVNP.BurstRAM.Memory w) :
    RAM.value (RAM.Contraction.codec (W.network N) fit)
      (RAM.Contraction.machine (RAM.Contraction.parameters (W.network N) fit))
      (extra+9+5*(W.internal+L*N.internal)+22*(L*N.cells+W.equal.length)) 0
      (RAM.BitLayout.memoryWithTail rest (W.network N) (RAM.Contraction.codec _ fit)
        (x ∘ railPin.symm) scratch) =
      W.eval (fun z => N.eval (z ∘ (Fintype.equivFin P).symm)) x := by
  rw [←(W.network_sizes N).1,←(W.network_sizes N).2,
    RAM.Contraction.value_eq_network (W.network N) fit _ scratch extra rest, W.network_eval]

end
end Hierarchy.UniversalGrid.Wiring

end OAI
