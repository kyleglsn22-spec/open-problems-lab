import Lab.Bondage.GammaDefs
import Lab.Bondage.QPart19

/-! Part 0 of the check that no five vertices dominate.

The import of `QPart19` is not used by any proof here: it keeps every heavy `decide` module of
`Lab/Bondage` on one import chain, so a parallel build never runs two of them at once (CI memory). -/

namespace OpenProblemsLab.Bondage

theorem checkGa_0 : checkGa 0 = true := by decide +kernel


end OpenProblemsLab.Bondage
