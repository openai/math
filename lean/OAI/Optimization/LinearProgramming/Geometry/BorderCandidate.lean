import OAI.Optimization.LinearProgramming.Geometry.BorderExchange
import OAI.Optimization.LinearProgramming.Geometry.BorderPackedState
import OAI.Optimization.LinearProgramming.Geometry.BorderCandidateControl

/-! One executable iteration of the streaming online geometric-minor interface. A zero
determinant is copied with log zero. A nonzero determinant really invokes the oracle,
and the restart exit is taken before advancing to or querying another candidate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Contract OracleSegments Matrix BorderScatter

variable {r s n k : ℕ}

def candidate : Segment := (Segment.core load).seq (nonzero (submit.seq unpack) (.core BorderScatter.append))

def candidateCost (k n : ℕ) : ℕ := 6*k+60+n*(8*k+16)+2*n

structure Sources (L : Layout r n) (m : Memory ℚ) (D : Matrix (Fin r) (Fin n) ℚ)
    (hr : k+1 ≤ r) (J : Fin k → Fin n) (price : Fin n → ℚ) : Prop where
  ready : L.Ready D J m
  raw (j : Fin n) : m.data (L.answers+j.val)=borderedMinor (D.submatrix (Fin.castLE hr) id) J j
  prices (j : Fin n) : m.data (L.prices+j.val)=price j

theorem candidate_runs {L : Layout r n} {original m : Memory ℚ} (P A : ℚ → Prop) (o : ScalarOracle ℚ)
    (h : Contract.History ℚ) (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (J : Fin k → Fin n) (price : Fin n → ℚ) (hr : k+1 ≤ r) (hrn : r ≤ n) (src : Sources L original D hr J price)
    (j : Fin n) (v : Fin n → ℚ) (hm : m.AllData P) (hAP : ∀q,A q → P q) (hz : A 0)
    (hn : ∀i ≤ n,P (i:ℚ)) (responds : Responds D E A o)
    (active : ScanReady L original (borderedMinor (D.submatrix (Fin.castLE hr) id) J) price A j.val v m) :
    let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
    let next (w : Fin n → ℚ) (t : Memory ℚ) := ScanReady L original raw price A (j.val+1) w t
    if raw j = 0 then ∃ t c, c ≤ candidateCost k n ∧ Runs candidate o (Memory.AllData P) m h c t h ∧ next v t
    else ∃ ans : Option ℚ, ∃ t c, c ≤ candidateCost k n ∧ Runs candidate o (Memory.AllData P) m h c t
        ((keyPacket D E (pivotKey J j),reply ans)::h) ∧
      match ans with | none => ScanStopped L original t | some q => next (Function.update v j q) t := by
  dsimp only
  let raw := borderedMinor (D.submatrix (Fin.castLE hr) id) J
  let b := loadState m
  have eLoad := Runs.core (load_spec m hm (hAP 0 hz)) o h
  have hold : ScanReady L original raw price A j.val v b := active.hold (scanLoad active)
  obtain ⟨raw27,price28,zero2,zero29⟩ := loaded_inputs active j rfl (src.raw j) (src.prices j)
  change b.data 27=raw j at raw27
  change b.data 28=price j at price28
  change b.data 2=0 at zero2
  change b.data 29=0 at zero29
  split
  · rename_i isZero
    have eq : b.data 27=b.data 2 := raw27.trans (isZero.trans zero2.symm)
    have go := Runs.core (append_spec b eLoad.finish) o h
    exact ⟨appendState b,4+(1+(1+9)),by unfold candidateCost; omega,
      eLoad.seq (nonzero_equal (submit.seq unpack) (.core BorderScatter.append) eq go),
      hold.skip hz raw27 zero29 price28⟩
  · rename_i nz
    have ne : b.data 27 ≠ b.data 2 := by rwa [raw27,zero2]
    have field (a : ℕ) (ha : 128 ≤ a) (hn : a ≠ 139) : b.index a=original.index a := hold.indices a ha hn
    have bk := (field 128 (by decide) (by decide)).trans src.ready.prefixCount
    have bn := (field 130 (by decide) (by decide)).trans src.ready.width
    have bs := (field 144 (by decide) (by decide)).trans src.ready.scratchAddr
    have bp := (field 136 (by decide) (by decide)).trans src.ready.pivotAddr
    have bJ (i : Fin k) : b.index (b.index 136+i.val)=(J i).val := by
      rw [bp,field _ (by have := L.pivots_ge; omega) (by have := L.pivots_ge; omega),src.ready.pivotData]
    have sl := L.source_ge; have sp := L.source_end; have pt := L.prices_end; have tr := L.triples_end
    have rd := L.rounded_end; have ab := L.answers_end; have ps := L.pivots_ge
    have high : 256 ≤ L.scratch := by omega
    have nonzeroMinor : circuitMinor (D.submatrix (Fin.castLE hr) id) J j ≠ 0 := by
      rw [←borderedMinor_eq]; exact nz
    obtain ⟨ans,z,c,hc,send,out,hq⟩ := submit_runs b P o h D E J j hr hrn nonzeroMinor L.scratch bk bn hold.cursor
      bs high (by rw [bp]; omega) bJ eLoad.finish hn (hAP 0 hz) (by simpa using hn 1 (by omega)) A hAP responds
    have rz : Holding L.scratch b z := ⟨fun p hp => out.index p (by omega) (by omega) (by omega) (by omega) (by omega),
      fun p hp ha => out.data p (by omega) (Or.inr (by omega)) ha⟩
    let t := loadTagState z
    have tHold := (hold.hold rz).hold (scanTagHold z)
    have tagRead := Runs.core (loadTag_spec z send.finish) o ((keyPacket D E (pivotKey J j),reply ans)::h)
    obtain ⟨tag,_,td⟩ := loadTag_out z
    have low (i : ℕ) (lo : 2 ≤ i) (hi : i < 30) (hn : i ≠ 3) : t.data i=b.data i :=
      (td i hn).trans (out.data i lo (Or.inl hi) (by omega))
    have tz : t.data 2=0 := (low 2 (by decide) (by decide) (by decide)).trans zero2
    have announced : t.data 3 = if ans.isNone then 1 else 0 := by rw [show t.data 3=z.data (z.index 82) from tag,out.destination,out.tag]
    cases ans with
    | none =>
      have tag1 : t.data 3=1 := announced
      have eRestart := Runs.core (restart_spec t tagRead.finish) o ((keyPacket D E (pivotKey J j),reply none)::h)
      have action : Runs (submit.seq unpack) o (Memory.AllData P) b h (c+(1+(1+2+1))) (restartState t)
          ((keyPacket D E (pivotKey J j),reply none)::h) :=
        send.seq (unpack_restart tagRead tz tag1 eRestart)
      obtain ⟨x,hx,choose⟩ := nonzero_different (submit.seq unpack) (.core BorderScatter.append) ne action
      exact ⟨none,restartState t,4+(x+(c+(1+(1+2+1)))),by unfold candidateCost; omega,eLoad.seq choose,tHold.restart src.ready.width⟩
    | some q =>
      have tag0 : t.data 3=0 := announced
      let w := valueState t
      have readValue := Runs.core (value_spec t tagRead.finish) o ((keyPacket D E (pivotKey J j),reply (some q))::h)
      have appendCell := Runs.core (append_spec w readValue.finish) o ((keyPacket D E (pivotKey J j),reply (some q))::h)
      have action : Runs (submit.seq unpack) o (Memory.AllData P) b h (c+(1+(1+(2+9)))) (appendState w)
          ((keyPacket D E (pivotKey J j),reply (some q))::h) :=
        send.seq (unpack_value tagRead tz tag0 readValue appendCell)
      obtain ⟨x,hx,choose⟩ := nonzero_different (submit.seq unpack) (.core BorderScatter.append) ne action
      obtain ⟨wv,_,wd,_⟩ := value_out t
      have a82 : t.index 82 = L.scratch := (congrFun (loadTag_out z).2.1 82).trans out.destination
      have wq : w.data 29=q := by rw [show w.data 29 = t.data (t.index 82+1) from wv,a82,td _ (by omega),out.value q rfl]
      have frame := (tHold.hold (scanValueHold t)).append q (hq q rfl)
        ((wd 27 (by decide)).trans ((low 27 (by decide) (by decide) (by decide)).trans raw27)) wq
        ((wd 28 (by decide)).trans ((low 28 (by decide) (by decide) (by decide)).trans price28))
      exact ⟨some q,appendState w,4+(x+(c+(1+(1+(2+9))))),by unfold candidateCost; omega,eLoad.seq choose,frame⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
