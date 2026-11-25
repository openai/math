import OAI.Computability.BorderVNP.CellPacketGeometryRecordTags

/-! # Positional public operands for every frozen sparse row constructor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket.Stored

open CellSparse Word Inherited
variable {I : Type*}

private def portAt (f : ℕ → WidthExpr I) (i : ℕ) : PortCode I := ⟨f i,f (i+1),f (i+2)⟩

private def routeAt (f : Fin 8 → WidthExpr I) : RouteCode I :=
  ⟨f 0,f 1,⟨f 2,f 3,f 4⟩,⟨f 5,f 6,f 7⟩⟩

/-- Each stored scalar is connected at its literal packet ordinal. In a
profile the histogram starts at seven and each complete route has eight fields. -/
def Shape.code (s : Shape) (f : ℕ → WidthExpr I) : RecordCode I :=
  match s with
  | .zero => .zero (f 1) (f 2) (portAt f 3)
  | .equal => .equal (f 1) (f 2) (portAt f 3) (portAt f 6)
  | .box => .box (f 1) (f 2) (f 3) (f 4)
  | .profile h n => .profile (f 1) (portAt f 2) (f 5) (List.ofFn fun j : Fin h => f (7+j.val))
      (List.ofFn fun i : Fin n => routeAt (fun j => f (8+h+i.val*8+j.val)))

private theorem routeAt_read (f : Fin 8 → WidthExpr I) (x : I → ℕ) (r : Route)
    (h : ∀ j, (f j).eval x = (Packet.route r)[j.val]?.getD 0) : (routeAt f).read x = r := by
  simp only [routeAt,RouteCode.read,PortCode.read,h]
  cases r with
  | mk t l a b => cases a; cases b; rfl

private theorem block_field {A B : Type*} (xs : List A) (block : A → List B) (n : ℕ)
    (size : ∀ a, (block a).length=n) (i : Fin xs.length) (j : Fin n) :
    (xs.flatMap block)[i.val*n+j.val]? = (block xs[i.val])[j.val]? := by
  induction xs with
  | nil => exact i.elim0
  | cons a xs ih =>
    refine Fin.cases ?_ (fun b => ?_) i
    · simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [size]; exact j.isLt)]
    · simp only [Fin.val_succ,List.flatMap_cons,List.getElem_cons_succ,Nat.succ_mul]
      rw [List.getElem?_append_right (by rw [size]; omega),size]
      convert ih b using 2; omega

/-- The positional wire template reconstructs the complete true row from its
canonical scalar fields, in particular every histogram and both ports of each route. -/
theorem code_read (r : Record) (f : ℕ → WidthExpr I) (x : I → ℕ)
    (fields : ∀ j, (f j).eval x = (Packet.record r)[j]?.getD 0) :
    ((shape r).code f).read x = r := by
  cases r with
  | zero n w p => simp only [shape,Shape.code,portAt,RecordCode.read,PortCode.read,fields]; cases p; rfl
  | equal n w a b => simp only [shape,Shape.code,portAt,RecordCode.read,PortCode.read,fields]; cases a; cases b; rfl
  | box i b n d => simp only [shape,Shape.code,RecordCode.read,fields]; rfl
  | profile n p w hist rs =>
    let r := Record.profile n p w hist rs
    let lead := [3,n,p.base,p.copyStride,p.laneStride,w,hist.length]
    have data : Packet.record r = lead++hist++([rs.length]++rs.flatMap Packet.route) := by
      simp [r,lead,Packet.record,Packet.port,Packet.vector,Packet.fieldList]
    have hHist (i : Fin hist.length) : (f (7+i.val)).eval x = hist[i.val] := by
      rw [fields]
      change ((Packet.record r)[7+i.val]?).getD 0 = _
      rw [data,List.append_assoc,List.getElem?_append_right (by simp [lead]),show 7+i.val-lead.length=i.val by simp [lead],
        List.getElem?_append_left i.isLt,List.getElem?_eq_getElem i.isLt,Option.getD_some]
    have histogram : (List.ofFn fun j : Fin hist.length => f (7+j.val)).map (WidthExpr.eval x) = hist := by
      apply List.ext_getElem
      · simp
      · intro j hj h; simp only [List.getElem_map,List.getElem_ofFn]; exact hHist ⟨j,h⟩
    have hRoute (i : Fin rs.length) (j : Fin 8) :
        (f (8+hist.length+i.val*8+j.val)).eval x = (Packet.route rs[i.val])[j.val]?.getD 0 := by
      rw [fields]
      change ((Packet.record r)[8+hist.length+i.val*8+j.val]?).getD 0 = _
      rw [data,List.getElem?_append_right (by simp [lead]; omega)]
      have ix : 8+hist.length+i.val*8+j.val-(lead++hist).length = 1+(i.val*8+j.val) := by simp [lead]; omega
      rw [ix,List.getElem?_append_right (by simp),show 1+(i.val*8+j.val)-[rs.length].length=i.val*8+j.val by simp,
        block_field rs Packet.route 8 (fun _ => rfl) i j]
    have routes : (List.ofFn fun i : Fin rs.length => routeAt (fun j => f (8+hist.length+i.val*8+j.val))).map
        (RouteCode.read x) = rs := by
      apply List.ext_getElem
      · simp
      · intro j hj h; simp only [List.getElem_map,List.getElem_ofFn]; exact routeAt_read _ x rs[j] (hRoute ⟨j,h⟩)
    simp only [shape,Shape.code,RecordCode.read,portAt,PortCode.read,fields,histogram,routes]
    cases p
    rfl

/-- A fixed physical scalar pin of the immutable tagged row, with zero outside
its public extent. -/
def fieldOf (ts : List Kind) (pin : Fin ts.length → I) (n : ℕ) : WidthExpr I :=
  if h : n<ts.length then .field (pin ⟨n,h⟩) else .const 0

/-- A complete schema for a row coming from the chronological native history
tape. It depends only on immutable relocation tags and the actual stored pins. -/
def fromTags (ts : List Kind) (pin : Fin ts.length → I) : RecordCode I :=
  (decodeShape ts).code (fieldOf ts pin)

/-- Any stored array with the real tagged scalar sequence of a mathematical
row yields exactly that row, including when different roles have equal values. -/
theorem fromTags_read (ts : List Kind) (pin : Fin ts.length → I) (x : I → ℕ) (r : Record)
    (trueRow : List.ofFn (fun i : Fin ts.length => (ts[i.val],x (pin i))) = marked r) :
    (fromTags ts pin).read x = r := by
  have tagged := congrArg (List.map Prod.fst) trueRow
  simp only [List.map_ofFn,Function.comp_def,marked_tags,List.ofFn_getElem] at tagged
  have hwords : (marked r).map Prod.snd = Packet.record r := by
    have h := marked_move 0 0 r
    have move (a : Kind × ℕ) : a.1.move 0 0 a.2 = a.2 := by cases a with | mk t v => cases t <;> simp [Kind.move]
    rw [show (fun a : Kind × ℕ => a.1.move 0 0 a.2) = Prod.snd from funext move] at h
    have zero : (r.shift 0).rebaseBox 0=r := by
      cases r with
      | zero n w p => cases p; simp [Record.shift,Port.shift,Record.rebaseBox]
      | equal n w p q => cases p; cases q; simp [Record.shift,Port.shift,Record.rebaseBox]
      | box => simp [Record.shift,Record.rebaseBox]
      | profile n p w h rs =>
        cases p
        have rt (u : Route) : u.shift 0 = u := by cases u; simp [Route.shift,Port.shift]
        simp [Record.shift,Record.rebaseBox,Port.shift,rt]
    simpa only [zero] using h
  have vals := congrArg (List.map Prod.snd) trueRow
  simp only [List.map_ofFn,Function.comp_def,hwords] at vals
  unfold fromTags
  rw [(congrArg decodeShape tagged).trans (decode_tags (shape r))]
  apply code_read
  intro j
  have hv := congrArg (fun xs : List ℕ => xs[j]?.getD 0) vals
  by_cases h : j<ts.length <;> simpa [fieldOf,h,WidthExpr.eval,List.getElem?_ofFn] using hv

end Packing.BankPacket.Stored

end BorderVNP
end Computability
end OAI
