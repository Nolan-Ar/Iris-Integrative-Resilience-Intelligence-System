/-
  Théorème d'échange d'énergie dans IRIS
  Démontre que la création de valeur ΔV respecte les principes thermodynamiques
  et est distribuée de façon cohérente dans le système
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms

open IrisAxioms

/-!
# THÉORÈME D'ÉCHANGE D'ÉNERGIE

Ce théorème formalise l'échange fondamental d'énergie dans le système IRIS :
la conversion des ressources brûlées (S_burn, U_burn) en valeur économique ΔV
via l'efficacité systémique η, avec conservation des grandeurs fondamentales.
-/

theorem theoreme_echange_energie 
  (η_phys μ_social Δt : ℝ)
  (S_burn U_burn : ℝ)
  (v_avant : Valeurs)
  (beneficiaires : List CompteUtilisateur)
  (alloc : CompteUtilisateur → ℝ)
  (h_phys : 0 < η_phys ∧ η_phys ≤ 1)
  (h_social : 1 ≤ μ_social ∧ μ_social ≤ 2)
  (h_dt : 0 < Δt)
  (h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn)
  (h_pos_alloc : ∀ cu ∈ beneficiaires, 0 ≤ alloc cu)
  (h_suffisamment_S : S_burn ≤ v_avant.S)
  (h_suffisamment_U : U_burn ≤ v_avant.U) :
  -- Conditions de cohérence
  let η := η_phys * μ_social
  let w_S := S_burn / (S_burn + U_burn) 
  let w_U := U_burn / (S_burn + U_burn)
  let Et := w_S * S_burn + w_U * U_burn
  let ΔV := η * Δt * Et
  -- Conclusions
  ∃ (v_apres : Valeurs) (ΔU_distribue : ℝ),
    -- 1. Création de valeur non-négative (A6)
    0 ≤ ΔV ∧
    -- 2. Distribution effective du RU (A12)
    ΔU_distribue = ΔV ∧
    (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = ΔU_distribue ∧
    -- 3. Conservation thermodynamique (A10)
    0 ≤ v_apres.V ∧ 0 ≤ v_apres.D ∧
    -- 4. Mise à jour cohérente des comptes
    v_apres.S = v_avant.S - S_burn ∧
    v_apres.U = v_avant.U - U_burn + ΔU_distribue ∧
    v_apres.V = v_avant.V + ΔV ∧
    v_apres.D = v_avant.D ∧
    -- 5. Préservation des contraintes
    v_apres.hS : 0 ≤ v_apres.S ∧
    v_apres.hU : 0 ≤ v_apres.U ∧
    v_apres.hV : 0 ≤ v_apres.V ∧
    v_apres.hD : 0 ≤ v_apres.D := by
  intro η w_S w_U Et ΔV
  
  -- 1. Création de valeur par A6
  have hΔV_nonneg : 0 ≤ ΔV := by
    have h_poids : w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U := by
      constructor
      · field_simp [w_S, w_U]
        rcases h_burn with ⟨hS, hU⟩
        have h_total : 0 ≤ S_burn + U_burn := by linarith
        rcases eq_zero_or_pos_of_nonneg h_total with h|h
        · have : S_burn = 0 := by linarith
          have : U_burn = 0 := by linarith
          simp [w_S, w_U, this]
        · field_simp [w_S, w_U, h.ne.symm]
    exact A6_creation_valeur_energetique η_phys μ_social Δt w_S w_U S_burn U_burn 
            h_phys h_social h_poids h_burn h_dt
  
  -- 2. Distribution via A12
  let ΔU_distribue := ΔV
  have h_distribution : (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = ΔU_distribue :=
    A12_distribution_RU ΔU_distribue beneficiaires alloc h_pos_alloc
  
  -- 3. Construction du nouvel état Valeurs
  let v_apres : Valeurs :=
    { S := v_avant.S - S_burn
      U := v_avant.U - U_burn + ΔU_distribue
      V := v_avant.V + ΔV
      D := v_avant.D
      hS := by linarith [v_avant.hS, h_burn.1, h_suffisamment_S]
      hU := by linarith [v_avant.hU, h_burn.2, h_suffisamment_U, hΔV_nonneg]
      hV := by linarith [v_avant.hV, hΔV_nonneg]
      hD := v_avant.hD }
  
  -- 4. Vérification de la conservation thermodynamique
  have h_conservation : 0 ≤ v_apres.V ∧ 0 ≤ v_apres.D := 
    ⟨by linarith [v_avant.hV, hΔV_nonneg], v_avant.hD⟩
  
  -- 5. Assemblage de la preuve
  refine ⟨v_apres, ΔU_distribue, hΔV_nonneg, rfl, h_distribution, 
          h_conservation.1, h_conservation.2, ?_, ?_, ?_, ?_, 
          v_apres.hS, v_apres.hU, v_apres.hV, v_apres.hD⟩
  all_goals { simp [v_apres] }

/-!
# COROLLAIRES DU THÉORÈME
-/

-- Version simplifiée pour l'échange énergétique pur
corollary corollaire_creation_valeur_pure
  (η_phys μ_social Δt S_burn U_burn : ℝ)
  (h_phys : 0 < η_phys ∧ η_phys ≤ 1)
  (h_social : 1 ≤ μ_social ∧ μ_social ≤ 2)
  (h_dt : 0 < Δt)
  (h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn) :
  let η := η_phys * μ_social
  let Et := (S_burn + U_burn) / 2  -- Mélange équitable
  let ΔV := η * Δt * Et
  0 ≤ ΔV := by
  intro η Et ΔV
  have : Et = (1/2 : ℝ) * S_burn + (1/2 : ℝ) * U_burn := by ring
  rw [this]
  have h_poids : (1/2 : ℝ) + (1/2 : ℝ) = 1 ∧ 0 ≤ (1/2 : ℝ) ∧ 0 ≤ (1/2 : ℝ) := by norm_num
  exact A6_creation_valeur_energetique η_phys μ_social Δt (1/2) (1/2) S_burn U_burn 
         h_phys h_social h_poids h_burn h_dt

-- Échange avec efficacité maximale
corollary corollaire_efficacite_maximale
  (Δt S_burn U_burn : ℝ)
  (h_dt : 0 < Δt)
  (h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn) :
  let η_phys := (1 : ℝ)
  let μ_social := (2 : ℝ) 
  let η := η_phys * μ_social
  let Et := (S_burn + U_burn) / 2
  let ΔV := η * Δt * Et
  ΔV = 2 * Δt * Et ∧ 0 ≤ ΔV := by
  intro η_phys μ_social η Et ΔV
  have h_phys : 0 < η_phys ∧ η_phys ≤ 1 := by norm_num
  have h_social : 1 ≤ μ_social ∧ μ_social ≤ 2 := by norm_num
  have h_nonneg : 0 ≤ ΔV := 
    corollaire_creation_valeur_pure η_phys μ_social Δt S_burn U_burn h_phys h_social h_dt h_burn
  constructor
  · norm_num [η, η_phys, μ_social]
  · exact h_nonneg

/-!
# APPLICATION NUMÉRIQUE
-/

example : 
  let η_phys := 0.8
  let μ_social := 1.5
  let Δt := 1.0
  let S_burn := 100.0
  let U_burn := 50.0
  let η := η_phys * μ_social
  let Et := (S_burn + U_burn) / 2
  let ΔV := η * Δt * Et
  -- Vérification des conditions et calcul
  (0 < η_phys ∧ η_phys ≤ 1) ∧
  (1 ≤ μ_social ∧ μ_social ≤ 2) ∧
  (0 ≤ S_burn ∧ 0 ≤ U_burn) ∧
  ΔV = 90.0 := by
  intro η_phys μ_social Δt S_burn U_burn η Et ΔV
  have h_phys : 0 < η_phys ∧ η_phys ≤ 1 := by norm_num
  have h_social : 1 ≤ μ_social ∧ μ_social ≤ 2 := by norm_num  
  have h_burn : 0 ≤ S_burn ∧ 0 ≤ U_burn := by norm_num
  refine ⟨h_phys, h_social, h_burn, ?_⟩
  norm_num [η, Et, ΔV]

#check theoreme_echange_energie
#check corollaire_creation_valeur_pure
#check corollaire_efficacite_maximale
