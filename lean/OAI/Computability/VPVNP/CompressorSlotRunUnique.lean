import OAI.Computability.VPVNP.CompressorSlotBuild

/-!
# Uniqueness of reports from the deterministic slot workers

The slot program has empty choice tapes after its layout has been selected.
Its operand banks and initial memory determine the reports of every phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM SlotLevel

variable {w : ℕ} {s : Shape} {h : Heads} {m : Memory w}

theorem ShrinkSlots.Preparation.Reports.Native.unique {layout : Bool} {r t : ShrinkSlots.Preparation.Reports w}
    (hr : r.Native s h layout m) (ht : t.Native s h layout m) : r = t := by
  have fixed {r : ShrinkSlots.Preparation.Reports w} (run : r.Native s h layout m) :
      r.publish = ShrinkSlots.Preparation.published h.subdivisions s.subdivisions w := by
    funext i
    have hp := ShrinkSlots.Preparation.publish_run h.subdivisions s.subdivisions
      (after m (eventLog ((List.ofFn r.publish).take i.val))) i
    exact (List.cons.inj (Option.some.inj ((run.1 i).symm.trans hp))).1
  have eq := (fixed hr).trans (fixed ht).symm
  rcases r with ⟨p,r,c,z⟩
  rcases t with ⟨q,r',c',z'⟩
  change p=q at eq; subst q
  rcases hr with ⟨_,hr,hc,hz⟩
  rcases ht with ⟨_,hr',hc',hz'⟩
  have e : r=r' := Option.some.inj (hr.symm.trans hr'); subst r'
  have e : c=c' := Option.some.inj (hc.symm.trans hc'); subst c'
  have e : z=z' := Option.some.inj (hz.symm.trans hz'); subst z'
  rfl

theorem SlotLevel.Reports.Native.unique {r t : SlotLevel.Reports w}
    (hr : r.Native s h m) (ht : t.Native s h m) : r=t := by
  rcases r with ⟨g,d,a,i,b⟩
  rcases t with ⟨g',d',a',i',b'⟩
  obtain ⟨hg,hd,ha,hi,hb⟩ := hr
  obtain ⟨hg',hd',ha',hi',hb'⟩ := ht
  have e : g=g' := Option.some.inj (hg.symm.trans hg'); subst g'
  have e : d=d' := Option.some.inj (hd.symm.trans hd'); subst d'
  have e : a=a' := Option.some.inj (ha.symm.trans ha'); subst a'
  have e : i=i' := Option.some.inj (hi.symm.trans hi'); subst i'
  have e : b=b' := Option.some.inj (hb.symm.trans hb'); subst b'
  rfl

end CompressorRecords

end VPVNP
end Computability
end OAI
