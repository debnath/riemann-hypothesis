module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeEqualityFromTestFunctions
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem multiplicity_one_hypotheses_hold : UnitaryGroupStructuralFacts :=
  ⟨ReciprocityTheory.ChartRestriction.DS.Xi.heisenbergHaarFacts_hold,
    Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists,
    _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.rankOneCoord,
    _root_.Formalism.FourierDecayAlt.P.LongWeylElement.t_bigcellfactor,
    _root_.Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts,
    _root_.Formalism.FourierDecayAlt.P.B2x1.conjHaar,
    Formalism.FourierDecayAlt.P.lemma_b_from_xi,
    _root_.Formalism.FourierDecayAlt.P.B7.jc_stepJCont,
    Formalism.FourierDecayAlt.P.phase_function_bound,
    Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear,
    Formalism.FourierDecayAlt.P.regularised_average_identity,
    _root_.Formalism.FourierDecayAlt.P.B7.y_stepUnfold,
    Formalism.FourierDecayAlt.P.ae_equality_from_test_functions,
    Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting,
    Formalism.FourierDecayAlt.P.normalisation_unique_every_setting,
    Formalism.QuantumDeterminants.uWNormal,
    Formalism.QuantumDeterminants.ellAdd,
    Formalism.QuantumDeterminants.nSubgroup⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
