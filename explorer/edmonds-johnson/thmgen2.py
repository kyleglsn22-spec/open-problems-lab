import os
from thmgen import certs, fl, A6, A6p, A7
def gen(folder, matname, imp, A, doc, chain=None):
    E=certs(A); n=len(A[0])
    d=f'../../Lab/EdmondsJohnson/{folder}'; os.makedirs(d,exist_ok=True)
    prev=f"Lab.EdmondsJohnson.{imp}"
    for k in range(1,6):
        Ek=[e for e in E if len(e[0])==k]
        # keep all heavy files on one import chain (lake would otherwise build chains in parallel)
        extra=("\nimport "+chain) if (k==1 and chain) else ""
        rows=[]
        for R,C,t,dd in Ek:
            cert=("Sum.inl ["+", ".join(fl(r) for r in dd)+"]") if t=='N' else "Sum.inr "+fl(dd)
            rows.append(f"  (({fl(R)}, {fl(C)}), {cert})")
        s=f'''import Lab.EdmondsJohnson.THMBasic
import {prev}{extra}

/-! Certificates for the {k} × {k} submatrices of `{matname}` ({len(Ek)} of them). -/

namespace EdmondsJohnson

set_option maxHeartbeats 0 in
/-- Certificates for the {k} × {k} submatrices of `{matname}`. -/
def table{matname}_{k} : CertTable :=
[
{(","+chr(10)).join(rows)}]

set_option maxHeartbeats 0 in
lemma certs{matname}_{k} : ∀ lr ∈ (List.finRange 5).sublistsLen {k},
    ∀ lc ∈ (List.finRange {n}).sublistsLen {k}, certOK {matname} table{matname}_{k} {k} lr lc := by
  decide +kernel

end EdmondsJohnson
'''
        open(f'{d}/Size{k}.lean','w').write(s)
        prev=f"Lab.EdmondsJohnson.{folder}.Size{k}"
    s=f'''import {prev}

/-!
# `{matname}` is totally half-modular

{doc} Checked with one certificate for each of the {len(E)} square submatrices with
increasing row and column indices (`isTHM_of_certs`; certificates in `Size1` … `Size5`).
-/

namespace EdmondsJohnson

/-- The certificate tables of `{matname}`, by size. -/
def table{matname} : ℕ → CertTable
  | 1 => table{matname}_1
  | 2 => table{matname}_2
  | 3 => table{matname}_3
  | 4 => table{matname}_4
  | _ => table{matname}_5

/-- **`{matname}` is totally half-modular.** -/
theorem isTHM_{matname} : IsTHM {matname} := by
  refine isTHM_of_certs {matname} table{matname} (fun k h1 h5 => ?_)
  interval_cases k
  · exact certs{matname}_1
  · exact certs{matname}_2
  · exact certs{matname}_3
  · exact certs{matname}_4
  · exact certs{matname}_5

end EdmondsJohnson
'''
    open(f'{d}/Main.lean','w').write(s)
gen('THM6','A6','A6',A6,"Del Pia (arXiv:2611.28580), Proposition 2.4.")
gen('THM6plus','A6plus','A6plus',A6p,"Stated without proof in Del Pia (arXiv:2611.28580), Section 6.",
    'Lab.EdmondsJohnson.THM6.Main')
gen('THM7','A7','A7',A7,"Stated without proof in Del Pia (arXiv:2611.28580), Section 6.",
    'Lab.EdmondsJohnson.THM6plus.Main')
