module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.StatementU
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Ux4

section blocks

variable {k j ρ : ℕ}

theorem block_index_first_val_eq (a : Fin j) : ((eB k j ρ) (Sum.inl (Sum.inl a))).val = a.val := by
  simp [eB]

theorem block_index_middle_val_eq (v : Fin (2 * ρ + k + 1)) : ((eB k j ρ) (Sum.inl (Sum.inr v))).val = j + v.val := by
  simp [eB]

theorem block_index_last_val_eq (a : Fin j) : ((eB k j ρ) (Sum.inr a)).val = j + (2 * ρ + k + 1) + a.val := by
  simp [eB]

theorem block3_apply
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by
  simp [blk3, Matrix.reindex_apply]

theorem ext_eB {M N : B.Mat k (j + ρ)} (h : ∀ x y : Ix k j ρ, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) :
    M = N := by
  ext a b
  simpa using h ((eB k j ρ).symm a) ((eB k j ρ).symm b)

theorem block3_one : (1 : B.Mat k (j + ρ)) = blk3 (k := k) (j := j) (ρ := ρ) 1 0 0 0 1 0 0 0 1 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;>
    simp [Matrix.one_apply, (eB k j ρ).injective.eq_iff]

theorem block_three_zero_size_eq : blk3 (k := k) (j := j) (ρ := ρ) 0 0 0 0 0 0 0 0 0 = 0 := by
  apply ext_eB
  intro x y
  rw [block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp

theorem block3_add
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 + blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 + ToralGalois) (A12 + cocyclesToWachVectorsExponent) (A13 + B13) (A21 + B21) (A22 + B22) (A23 + B23) (A31 + B31) (A32 + B32) (A33 + B33) := by
  apply ext_eB
  intro x y
  rw [Matrix.add_apply, block3_apply, block3_apply, block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp

theorem block3_lower_blocks_zero
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (h21 : A21 = 0) (h31 : A31 = 0) (i b : Fin (2 * (j + ρ) + k + 1)) (hb : b.val < j) (hi : j ≤ i.val) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 i b = 0 := by
  obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
  rw [block3_apply]
  rcases y with ((c | c) | c)
  · rcases x with ((a | a) | a)
    · rw [block_index_first_val_eq] at hi
      exact absurd hi (not_le.2 a.isLt)
    · simp [h21]
    · simp [h31]
  · rw [block_index_middle_val_eq] at hb
    omega
  · rw [block_index_last_val_eq] at hb
    omega

end blocks

section rad

variable {k j ρ : ℕ}

theorem w_w_mul (M : Matrix (Fin j) (Fin j) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, _root_.Formalism.FourierDecayAlt.P.Ux3.wMat_mul_self, Matrix.one_mul]

theorem w_w_mul' {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by
  rw [← Matrix.mul_assoc, _root_.Formalism.FourierDecayAlt.P.Ux3.wMat_mul_self, Matrix.one_mul]

noncomputable def RnInv (x : RC k j ρ) : B.Mat k (j + ρ) :=
  blk3 1 (G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ)
    (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
      G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (-(Matrix.of x.1)) 0 0 1

theorem Rn_mul_RnInv (x : RC k j ρ) : Rn k j ρ x * RnInv x = 1 := by
  rw [Rn, RnInv, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, block3_one]
  congr 1 <;>
    simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_neg, smul_zero, sub_zero, neg_zero] <;> abel

theorem Rn_inv_eq (x : RC k j ρ) : (Rn k j ρ x)⁻¹ = RnInv x := Matrix.inv_eq_right_inv (Rn_mul_RnInv x)

theorem mMap_mul_embG (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    mMap k j ρ Z γ * embG k j ρ y = mMap k j ρ Z (γ * y) := by
  unfold mMap embG
  rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul]
  congr 1 <;> simp

theorem embG_mul_mMap (Z : Matrix (Fin j) (Fin j) ℂ) (γ y : B.Mat k ρ) :
    embG k j ρ y * mMap k j ρ Z γ = mMap k j ρ Z (y * γ) := by
  unfold mMap embG
  rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul]
  congr 1 <;> simp

theorem mMap_mul_muP (Z W : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    mMap k j ρ Z γ * muP k j ρ W = mMap k j ρ (Z * W) γ := by
  unfold mMap muP
  rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul]
  congr 1 <;> simp [Matrix.mul_assoc, w_w_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev]

end rad

theorem symmetricScalarBlockMatrix_mul {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem zj_mul {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z q : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H (Z * q) = Zj a b H Z * ((blk2 1 (Matrix.of b) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of b) 0 1) := by
  have hU : blk2 1 (Matrix.of b) 0 1 * (blk2 1 (Matrix.of b) 0 1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block2_det_upper_triangular]; simp)
  have hD : blk2 H 0 0 (Z * q) = blk2 H 0 0 Z * blk2 1 0 0 q := by
    rw [symmetricScalarBlockMatrix_mul]; simp
  unfold Zj
  rw [hD]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (blk2 1 (Matrix.of b) 0 1) (blk2 1 (Matrix.of b) 0 1)⁻¹, hU, Matrix.one_mul]

theorem ux_zjAffine : ZjAffine := by
  intro p s a b H CC
  unfold Zj
  rw [symmetricScalarBlockMatrix_mul, symmetricScalarBlockMatrix_mul]
  simp

end Formalism.FourierDecayAlt.P.Ux4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Ux4

theorem slice_right_coordinates : Formalism.FourierDecayAlt.U.SliceRight := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← mMap_mul_embG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, _root_.Formalism.FourierDecayAlt.P.Ux3.rn_mul_inv, Matrix.one_mul]

theorem slice_left_coordinates : Formalism.FourierDecayAlt.U.SliceLeft := by
  intro k p s ρ σ d ξ Z γ y
  unfold gaXi
  rw [← embG_mul_mMap]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.1) (Rn k (p + s) ρ ξ.1.1)⁻¹, _root_.Formalism.FourierDecayAlt.P.Ux3.rn_mul_inv, Matrix.one_mul]

theorem slice_z_coordinates : Formalism.FourierDecayAlt.U.SliceZ := by
  intro k p s ρ σ d ξ Z q γ
  unfold gaXi
  have hZ : ZjH σ d ξ.2 (Matrix.of Z * q) = ZjH σ d ξ.2 Z *
      ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of ξ.2.1.2) 0 1) := by
    unfold ZjH
    exact zj_mul _ _ _ _ _
  rw [hZ, ← mMap_mul_muP]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Rn k (p + s) ρ ξ.1.2) (Rn k (p + s) ρ ξ.1.2)⁻¹, _root_.Formalism.FourierDecayAlt.P.Ux3.rn_mul_inv, Matrix.one_mul]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.Ux4

section lie

variable {k j ρ : ℕ}

theorem conj_lie {N : ℕ} (n M H : Matrix (Fin N) (Fin N) ℂ) (hu : nᴴ * H * n = H) (hH : Hᴴ = H)
    (hn : n * n⁻¹ = 1) (hM : Mᴴ * H + H * M = 0) :
    (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = 0 := by
  have h1 : H * n⁻¹ = nᴴ * H := by
    calc H * n⁻¹ = nᴴ * H * n * n⁻¹ := by rw [hu]
      _ = nᴴ * H := by rw [Matrix.mul_assoc (nᴴ * H), hn, Matrix.mul_one]
  have h2 : (n⁻¹)ᴴ * H = H * n := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hH] using this
  calc (n⁻¹ * M * n)ᴴ * H + H * (n⁻¹ * M * n) = nᴴ * Mᴴ * ((n⁻¹)ᴴ * H) + (H * n⁻¹) * M * n := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = nᴴ * (Mᴴ * H + H * M) * n := by
        rw [h2, h1]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hM]; simp

theorem lie_Y (Y : B.Mat k ρ) (hY : B.inLie k ρ Y) :
    B.inLie k (j + ρ) (blk3 0 0 0 0 Y 0 0 0 0) := by
  unfold B.inLie at hY ⊢
  rw [_root_.Formalism.FourierDecayAlt.P.Ux3.hpkBlocks k j ρ, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_conjTranspose, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_zero, hY]

theorem lie_Q (Q : Matrix (Fin j) (Fin j) ℂ) :
    B.inLie k (j + ρ) (blk3 (k := k) (ρ := ρ) Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j))) := by
  unfold B.inLie
  have hw := _root_.Formalism.FourierDecayAlt.P.Ux3.wMat_conjTranspose j
  rw [_root_.Formalism.FourierDecayAlt.P.Ux3.hpkBlocks k j ρ, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_conjTranspose, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, block3_add, ← block_three_zero_size_eq]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hw, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, w_w_mul, _root_.Formalism.FourierDecayAlt.P.Ux3.wMat_mul_self, add_neg_cancel]
  all_goals abel

end lie

end Formalism.FourierDecayAlt.P.Ux4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Ux4

theorem directions_in_parabolic : Formalism.FourierDecayAlt.U.DirectionsInP := by
  intro k j ρ x
  have hn := _root_.Formalism.FourierDecayAlt.P.Ux3.rn_mul_inv x
  constructor
  · intro Y hY
    refine ⟨conj_lie _ _ _ (_root_.Formalism.FourierDecayAlt.P.Ux3.rn_unitary x) (_root_.Formalism.FourierDecayAlt.P.Ux3.hpk_herm k (j + ρ)) hn (lie_Y Y hY), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi
  · intro Q
    refine ⟨conj_lie _ _ _ (_root_.Formalism.FourierDecayAlt.P.Ux3.rn_unitary x) (_root_.Formalism.FourierDecayAlt.P.Ux3.hpk_herm k (j + ρ)) hn (lie_Q Q), ?_⟩
    intro i b hb hi
    rw [Rn_inv_eq]
    unfold RnInv Rn
    rw [_root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul, _root_.Formalism.FourierDecayAlt.P.Ux3.block3_mul]
    exact block3_lower_blocks_zero _ _ _ _ _ _ _ _ _ (by simp) (by simp) i b hb hi

end Formalism.FourierDecayAlt.P
