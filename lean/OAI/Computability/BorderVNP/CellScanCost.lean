import OAI.Computability.BorderVNP.CellVisitClock
import OAI.Computability.BorderVNP.CellSerializedLength
import OAI.Computability.BorderVNP.CellLiteralLoops

/-! # Cost of traversing the compact cell descriptor

A command visit scans at most the stored input and the current lexical environment. A read
additionally emits one unary symbol per offset. These symbols are charged to the actual output
stream. Empty loop bodies and the terminal scans still receive a charge.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open CellSparse RationalHitting.StackLanguage
open private fixedJob readJob from OAI.Computability.BorderVNP.CellGeneratorWire

/-- One local visit has space for the entire compact descriptor, the binary expression
procedures, and the lexical environment. -/
noncomputable def visitSize (d H M J S : ℕ) :=
  S + (visitClock d H).eval (visitWidth M M J) + H*(2*M.size+1) + M.size + 1

private theorem scan_single (j : Job) : scanCost [j] = 14*j.input.length+j.ticks+22 := by
  simp [scanCost]; omega

private theorem record_single (row : List Bool) : (records [row]).length = 2*row.length+2 := by
  simp [records,codeWord_length]

private theorem scan_append (xs ys : List Job) : scanCost (xs++ys) ≤ scanCost xs + scanCost ys := by
  simp [scanCost]; omega

private theorem loop_sweep_le (body env : List Bool) (cost weight : ℕ → ℕ) (B cap i n : ℕ)
    (hover : ∀ j, i ≤ j → j < i+n → 1 + Loop.overhead body env j ≤ B)
    (hchild : ∀ j, i ≤ j → j < i+n → cost j ≤ B*(cap+weight j)) :
    Loop.sweepCost body env cost i n ≤ 1+B*(n*(1+cap)+((List.range' i n).map weight).sum) := by
  induction n generalizing i with
  | zero => simp [Loop.sweepCost]
  | succ n ih =>
    have ho := hover i le_rfl (by omega)
    have hc := hchild i le_rfl (by omega)
    have hh := ih (i+1) (fun j hj hk => hover j (by omega) (by omega))
      (fun j hj hk => hchild j (by omega) (by omega))
    simp only [Loop.sweepCost, List.range'_succ, List.map_cons, List.sum_cons, Nat.succ_mul]
    simp only [Nat.mul_add,Nat.mul_one] at hc hh ⊢
    omega

private theorem read_cost (d : ℕ) (e : NatExpr) (env : List ℕ) (X : ℕ)
    (h₁ : ([false,false,true] ++ exprBits d e).length ≤ X)
    (h₂ : (clocks d).expr e env ≤ X) (h₃ : (e.eval env).bits.length ≤ X) (hX : 1 ≤ X) :
    scanCost (jobs (clocks d) d (.read e) env) ≤ 1000*X*(1+work (.read e) env) := by
  let n := e.eval env
  have hc := Nat.mul_le_mul_left (7*n+8) h₃
  have hx := Nat.mul_le_mul_left n hX
  change scanCost [readJob _ _ _ _] ≤ _
  rw [scan_single]
  change 14*([false,false,true] ++ exprBits d e).length +
    (3+(clocks d).expr e env+(7*n+8)*n.bits.length+4*n+9)+22 ≤ _
  have hw : work (.read e) env = n+4 := by simp [work,stream,Stmt.expand,Op.bits,n]
  rw [hw]
  nlinarith only [h₁,h₂,hc,hx,hX]

private theorem fixed_cost (o : Op) (X : ℕ) (hX : 1 ≤ X)
    (hrow : ([false,false,false] ++ o.bits).length ≤ X) :
    scanCost [fixedJob o] ≤ 1000*X := by
  rw [scan_single]
  change 14*([false,false,false] ++ o.bits).length+(3+4*o.bits.length+2)+22 ≤ _
  simp only [List.length_append,List.length_cons,List.length_nil] at *
  omega

private theorem loop_charge {expr body : List Bool} {k X costExpr : ℕ}
    (hin : ([true,false] ++ Loop.payload expr body).length ≤ X) (he : expr.length ≤ X)
    (hb : body.length ≤ X) (hk : k.bits.length ≤ X) (hc : costExpr ≤ X) (hX : 1 ≤ X) :
    14*([true,false] ++ Loop.payload expr body).length +
      (2+Loop.overheadDispatch expr body k+costExpr)+22+1 ≤ 1000*X*(k+1) := by
  have hh := Nat.mul_le_mul_left (7*k+8) hk
  unfold Loop.overheadDispatch
  nlinarith only [hin,he,hb,hk,hc,hX,hh]

private theorem branch_charge {cond yes no : List Bool} {X vlen costExpr : ℕ}
    (hin : ([true,true] ++ branchPayload cond yes no).length ≤ X) (hc : cond.length ≤ X)
    (hy : yes.length ≤ X) (hn : no.length ≤ X) (hv : vlen ≤ X) (hcost : costExpr ≤ X) (hX : 1 ≤ X) :
    14*([true,true] ++ branchPayload cond yes no).length + 2+costExpr+
      20*(cond.length+yes.length+no.length+vlen+3)+22 ≤ 1000*X := by omega

private theorem scan_bound {d H M J S : ℕ} (s : Stmt) (h : ℕ) (env : List ℕ)
    (fit : s.FitsDepth d h) (lit : s.LiteralLoops) (depthEnv : env.length+h ≤ H)
    (vals : ∀ i ∈ env, i ≤ M) (fields : s.field ≤ M) (lex : s.lexical ≤ J)
    (serial : (serialized d s).length ≤ S) :
    scanCost (jobs (clocks d) d s env) ≤
      1000*visitSize d H M J S * ((M+2)^h*s.mass + work s env) := by
  let X := visitSize d H M J S
  let B := 1000*X
  have hX : 1 ≤ X := by dsimp [X,visitSize]; omega
  have hS : S ≤ X := by dsimp [X,visitSize]; omega
  have hV : (visitClock d H).eval (visitWidth M M J) ≤ X := by dsimp [X,visitSize]; omega
  have hB : 1 ≤ B := by dsimp [B]; omega
  change scanCost _ ≤ B*((M+2)^h*s.mass+work s env)
  induction s generalizing h env with
  | nil =>
    have hpow := Nat.one_le_pow h _ (show 0 < M+2 by omega)
    change 1 ≤ B*((M+2)^h*1+0)
    simp only [Nat.mul_one,Nat.add_zero]
    exact one_le_mul_of_one_le_of_one_le hB hpow
  | fixed o =>
    have hpow := Nat.one_le_pow h _ (show 0 < M+2 by omega)
    cases o with
    | read k =>
      have hrow : ([false,false,true] ++ exprBits d (.lit k)).length ≤ X := by
        simp only [serialized,wire,record_single] at serial; omega
      have hv := expression_visit (d := d) (h := H) (M := M) (U := M) (J := J) (by omega) vals
        (.lit k) (Nat.zero_le _) fields (Nat.zero_le _)
      have hh := read_cost d (.lit k) env X hrow (hv.2.1.trans hV) (hv.2.2.trans hV) hX
      change scanCost (jobs _ d (.read (.lit k)) env) ≤ _
      exact hh.trans (Nat.mul_le_mul_left _ (by change 1+work (.read (.lit k)) env ≤ (M+2)^h*1+work (.read (.lit k)) env; omega))
    | literal b | guess | nand | sign | guard =>
      apply (fixed_cost _ X hX ?_).trans
      · exact Nat.le_mul_of_pos_right B (by change 0 < (M+2)^h*1+_; omega)
      · simp only [serialized,wire,record_single] at serial; omega
  | read e =>
    have hrow : ([false,false,true] ++ exprBits d e).length ≤ X := by
      simp only [serialized,wire,record_single] at serial; omega
    have hv := expression_visit (d := d) (h := H) (by omega) vals e fit fields lex
    have hh := read_cost d e env X hrow (hv.2.1.trans hV) (hv.2.2.trans hV) hX
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ _ (by omega)) (by change 1 ≤ 1+_; omega)) _))
  | bit v i =>
    have hb := bit_visit (d := d) (h := H) (by omega) vals v i (max_le_iff.mp fields).1
      (max_le_iff.mp fields).2 (max_le_iff.mp lex).1 (max_le_iff.mp lex).2
    have hcost := hb.2.trans hV
    change scanCost [_] ≤ _
    rw [scan_single]
    have hrow : ([false,true] ++ Coding.code (Address.pack d v,Address.pack d i)).length ≤ X := by
      simp only [serialized,wire,record_single] at serial; omega
    change 14*([false,true] ++ Coding.code (Address.pack d v,Address.pack d i)).length+
      (2+(clocks d).bit v i env)+22 ≤ _
    have hbase : 1 ≤ (M+2)^h*(Stmt.bit v i).mass+work (.bit v i) env :=
      (one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ _ (by omega)) (by change 1 ≤ 1+_+_; omega)).trans (Nat.le_add_right ..)
    apply le_trans _ (Nat.mul_le_mul_left B hbase)
    change _ ≤ 1000*X*1; rw [Nat.mul_one]; omega
  | seq a b ha hb =>
    have hs : (serialized d a).length+(serialized d b).length ≤ S := by
      simpa only [serialized,wire,records_append,List.length_append] using serial
    have h₁ := ha h env fit.1 lit.1 depthEnv vals (max_le_iff.mp fields).1 (max_le_iff.mp lex).1 (by omega)
    have h₂ := hb h env fit.2 lit.2 depthEnv vals (max_le_iff.mp fields).2 (max_le_iff.mp lex).2 (by omega)
    apply (scan_append ..).trans ((Nat.add_le_add h₁ h₂).trans ?_)
    simp only [Stmt.mass,work_seq,Nat.mul_add,Nat.mul_one]
    omega
  | loop e s ih =>
    cases h with
    | zero => exact (Nat.lt_irrefl 0 fit.1).elim
    | succ h =>
      obtain ⟨⟨k,rfl⟩,hchild⟩ := lit
      let expr := exprBits d (.lit k)
      let body := serialized d s
      have hs : (records [[true,false] ++ Loop.payload expr body]).length ≤ S := serial
      rw [record_single] at hs
      have hin : ([true,false] ++ Loop.payload expr body).length ≤ X := by omega
      simp only [Loop.payload,List.length_append,List.length_cons,List.length_nil,codeWord_length] at hs
      have hsBody : body.length ≤ S := by omega
      have he : expr.length ≤ X := by omega
      have hk : k ≤ M := (max_le_iff.mp fields).1
      have hv := expression_visit (d := d) (h := H) (M := M) (U := M) (J := J) (by omega) vals
        (.lit k) (Nat.zero_le _) hk (Nat.zero_le _)
      have hkbits : k.bits.length ≤ X := hv.2.2.trans hV
      have base := loop_charge hin he (hsBody.trans hS) hkbits (hv.2.1.trans hV) hX
      have hEnv : (Coding.code env).length ≤ X := (env_length env H M (by omega) vals).trans (by dsimp [X,visitSize]; omega)
      let cap := (M+2)^h*s.mass
      let weights := fun i => work s (i::env)
      have hsweep := loop_sweep_le body (Coding.code env)
        (fun i => scanCost (jobs (clocks d) d s (i::env))) weights B cap 0 k
        (fun j _ hj => by
          have hj' := Nat.size_le_size (show j ≤ k by omega)
          rw [← Nat.size_eq_bits_len j, ← Nat.size_eq_bits_len k] at hj'
          dsimp [Loop.overhead,B]; omega)
        (fun j _ hj => ih h (j::env) fit.2.2 hchild (by simp; omega)
          (by intro i hi; rcases List.mem_cons.mp hi with rfl|hh; omega; exact vals _ hh)
          (max_le_iff.mp fields).2 (max_le_iff.mp lex).2 hsBody)
      rw [← List.range_eq_range'] at hsweep
      change scanCost [_] ≤ _
      rw [scan_single,work_loop]
      change 14*([true,false] ++ Loop.payload expr body).length+
        (2+Loop.overheadDispatch expr body k+(clocks d).expr (.lit k) env+
        Loop.sweepCost body (Coding.code env) _ 0 k)+22 ≤
        B*((M+2)^(h+1)*(1+1+s.mass)+((List.range k).map weights).sum)
      have room : k+1+k*(1+cap) ≤ (M+2)^(h+1)*(1+1+s.mass) := by
        have hpow := Nat.one_le_pow h _ (show 0 < M+2 by omega)
        have hcap := Nat.mul_le_mul_right cap hk
        have hmul := Nat.mul_le_mul_left (M+2) hpow
        rw [pow_succ']; dsimp [cap] at hcap ⊢
        nlinarith only [hcap,hmul,hk]
      have htotal := Nat.mul_le_mul_left B (Nat.add_le_add_right room ((List.range k).map weights).sum)
      dsimp only [B] at base hsweep htotal ⊢
      simp only [Nat.mul_add,Nat.mul_one] at base hsweep htotal ⊢
      omega
  | ifEq a b y n iy ino =>
    cases h with
    | zero => exact (Nat.lt_irrefl 0 fit.1).elim
    | succ h =>
      let e := difference a b
      let cond := exprBits d e
      let yes := serialized d y
      let no := serialized d n
      have hs : (records [[true,true] ++ branchPayload cond yes no]).length ≤ S := serial
      rw [record_single] at hs
      have hin : ([true,true] ++ branchPayload cond yes no).length ≤ X := by omega
      simp only [branchPayload,List.length_append,List.length_cons,List.length_nil,codeWord_length] at hs
      have hv := expression_visit (d := d) (h := H) (M := M) (U := M) (J := J) (by omega) vals e
        (by rw [show e = difference a b from rfl,depth_difference]; exact fit.2.1)
        (by rw [show e = difference a b from rfl,difference_field]; exact (max_le_iff.mp fields).1)
        (by rw [show e = difference a b from rfl,difference_lexical]; exact (max_le_iff.mp lex).1)
      have base := branch_charge hin (by omega) (by omega) (by omega) (hv.2.2.trans hV) (hv.2.1.trans hV) hX
      have h₁ := iy h env fit.2.2.1 lit.1 (by omega) vals (max_le_iff.mp (max_le_iff.mp fields).2).1
        (max_le_iff.mp (max_le_iff.mp lex).2).1 (show yes.length ≤ S by omega)
      have h₂ := ino h env fit.2.2.2 lit.2 (by omega) vals (max_le_iff.mp (max_le_iff.mp fields).2).2
        (max_le_iff.mp (max_le_iff.mp lex).2).2 (show no.length ≤ S by omega)
      have room (m : ℕ) (hm : m ≤ (Stmt.ifEq a b y n).mass-1) :
          1+(M+2)^h*m ≤ (M+2)^(h+1)*(Stmt.ifEq a b y n).mass := by
        have hp := Nat.one_le_pow h _ (show 0 < M+2 by omega)
        have hmass : m+1 ≤ (Stmt.ifEq a b y n).mass := by simp only [Stmt.mass] at *; omega
        have hmul := Nat.mul_le_mul_left ((M+2)^h) hmass
        have hstep := Nat.mul_le_mul_right (Stmt.ifEq a b y n).mass
          (Nat.pow_le_pow_right (show 0 < M+2 by omega) (Nat.le_succ h))
        change (M+2)^h*(Stmt.ifEq a b y n).mass ≤ (M+2)^(h+1)*(Stmt.ifEq a b y n).mass at hstep
        simp only [Nat.mul_add,Nat.mul_one] at hmul
        omega
      change scanCost [_] ≤ _
      rw [scan_single]
      change 14*([true,true] ++ branchPayload cond yes no).length + (2+(clocks d).expr e env+
        (if a.eval env = b.eval env then scanCost (jobs (clocks d) d y env) else scanCost (jobs (clocks d) d n env))+
        20*(cond.length+yes.length+no.length+(e.eval env).bits.length+3))+22 ≤ _
      by_cases hab : a.eval env = b.eval env
      · rw [ite_eq_left hab,show work (.ifEq a b y n) env = work y env by simp [work,Stmt.expand,hab]]
        have hroom := Nat.mul_le_mul_left B (Nat.add_le_add_right (room y.mass (by simp [Stmt.mass]; omega)) (work y env))
        change _ ≤ B at base; simp only [Nat.mul_add,Nat.mul_one] at hroom h₁ ⊢; omega
      · rw [ite_eq_right hab,show work (.ifEq a b y n) env = work n env by simp [work,Stmt.expand,hab]]
        have hroom := Nat.mul_le_mul_left B (Nat.add_le_add_right (room n.mass (by simp [Stmt.mass]; omega)) (work n env))
        change _ ≤ B at base; simp only [Nat.mul_add,Nat.mul_one] at hroom h₂ ⊢; omega

/-- The generator clock for a bounded-depth program with literal loop bounds. The descriptor
mass pays for repeated empty scans. The emitted stream pays for all unary read offsets. -/
theorem scanCost_le (s : Stmt) (d H : ℕ) (fit : s.FitsDepth d H) (lit : s.LiteralLoops) :
    scanCost (jobs (clocks d) d s []) ≤
      1000*visitSize d H s.field s.lexical (serialized d s).length *
        ((s.field+2)^H*s.mass + work s []) :=
  scan_bound s H [] fit lit (by simp) (by simp) le_rfl le_rfl le_rfl

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
