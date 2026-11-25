module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianLeviVectorBaseOrthogonal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem heisenbergHaarFacts_hold : InductiveHeisenbergInputs :=
  ⟨Formalism.FourierDecayAlt.P.stabilizer_integration_formula,
    _root_.Formalism.FourierDecayAlt.P.B2x8.al_oneStepCoord,
    _root_.Formalism.FourierDecayAlt.P.B2x8.al_oneStepMem,
    Formalism.FourierDecayAlt.P.unipotent_haar_recursion,
    Formalism.FourierDecayAlt.P.unipotent_haar_base_case,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisConjLev,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisConjLevMeas,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisInv,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisMul,
    _root_.Formalism.FourierDecayAlt.P.B2x4.heisMem,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisClosed,
    _root_.Formalism.FourierDecayAlt.P.B2x5.heisHaar,
    Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting,
    _root_.Formalism.FourierDecayAlt.P.B2x3.compactW,
    Formalism.FourierDecayAlt.P.norm_power_integrable_sharp,
    Formalism.FourierDecayAlt.P.matrix_norm_ge_one,
    _root_.Formalism.FourierDecayAlt.P.B2x1.haarUnique,
    Formalism.FourierDecayAlt.P.haar_measure_inversion,
    _root_.Formalism.FourierDecayAlt.P.B2x3.compactHaar,
    _root_.Formalism.FourierDecayAlt.P.B2x2.closedG,
    _root_.Formalism.FourierDecayAlt.P.B2x2.closedN,
    _root_.Formalism.FourierDecayAlt.P.B2x3.closedW,
    _root_.Formalism.FourierDecayAlt.P.B2x2.levHaar,
    _root_.Formalism.FourierDecayAlt.P.B2x3.haarW,
    Formalism.FourierDecayAlt.P.unipotent_haar_exists,
    _root_.Formalism.FourierDecayAlt.P.B2x3.haarG,
    _root_.Formalism.FourierDecayAlt.P.B2x4.heisAct⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
