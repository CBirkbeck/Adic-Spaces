import «Adic spaces».IteratedOverlapEquiv

open ValuationSpectrum

noncomputable example {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    presheafValue (laurentOverlapDatum D₀ f) ≃+*
      presheafValue (iteratedOverlapDatum_B P D₀ f hLocLift_B) :=
  presheafValue_iteratedOverlap_equiv P D₀ f hLocLift_B