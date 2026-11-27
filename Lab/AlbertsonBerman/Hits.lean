import Lab.AlbertsonBerman.Basic

/-! Part of claim AB-1, see `Lab/AlbertsonBerman/Basic.lean`. -/

namespace OpenProblemsLab.AlbertsonBerman

open SimpleGraph

/-! ## Hitting facts: each large vertex set on one side contains a listed cycle -/

lemma hitQ0 : ∀ B : Finset (Fin 29), B ⊆ QL.toFinset → B.card = 7 →
    ∃ l ∈ cycQ0, ∀ v ∈ l, v ∈ ([] : List (Fin 29)) ∨ v ∈ B :=
  hits_of_allSub cycQ0 mcycQ0 mcycQ0_eq QL 7 ([] : List (Fin 29)) (by decide +kernel)

lemma hitQx : ∀ B : Finset (Fin 29), B ⊆ QL.toFinset → B.card = 7 →
    ∃ l ∈ cycQx, ∀ v ∈ l, v ∈ [27] ∨ v ∈ B :=
  hits_of_allSub cycQx mcycQx mcycQx_eq QL 7 [27] (by decide +kernel)

lemma hitQy : ∀ B : Finset (Fin 29), B ⊆ QL.toFinset → B.card = 7 →
    ∃ l ∈ cycQy, ∀ v ∈ l, v ∈ [28] ∨ v ∈ B :=
  hits_of_allSub cycQy mcycQy mcycQy_eq QL 7 [28] (by decide +kernel)

lemma hitQxy : ∀ B : Finset (Fin 29), B ⊆ QL.toFinset → B.card = 6 →
    ∃ l ∈ cycQxy, ∀ v ∈ l, v ∈ [27, 28] ∨ v ∈ B :=
  hits_of_allSub cycQxy mcycQxy mcycQxy_eq QL 6 [27, 28] (by decide +kernel)

lemma hitR0 : ∀ B : Finset (Fin 29), B ⊆ RL.toFinset → B.card = 9 →
    ∃ l ∈ cycR0, ∀ v ∈ l, v ∈ ([] : List (Fin 29)) ∨ v ∈ B :=
  hits_of_allSub cycR0 mcycR0 mcycR0_eq RL 9 ([] : List (Fin 29)) (by decide +kernel)

lemma hitRx : ∀ B : Finset (Fin 29), B ⊆ RL.toFinset → B.card = 8 →
    ∃ l ∈ cycRx, ∀ v ∈ l, v ∈ [27] ∨ v ∈ B :=
  hits_of_allSub cycRx mcycRx mcycRx_eq RL 8 [27] (by decide +kernel)

lemma hitRy : ∀ B : Finset (Fin 29), B ⊆ RL.toFinset → B.card = 8 →
    ∃ l ∈ cycRy, ∀ v ∈ l, v ∈ [28] ∨ v ∈ B :=
  hits_of_allSub cycRy mcycRy mcycRy_eq RL 8 [28] (by decide +kernel)

lemma hitRxy : ∀ B : Finset (Fin 29), B ⊆ RL.toFinset → B.card = 8 →
    ∃ l ∈ cycRxy, ∀ v ∈ l, v ∈ [27, 28] ∨ v ∈ B :=
  hits_of_allSub cycRxy mcycRxy mcycRxy_eq RL 8 [27, 28] (by decide +kernel)

end OpenProblemsLab.AlbertsonBerman
